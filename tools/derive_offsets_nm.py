#!/usr/bin/env python3
"""
derive_offsets_nm.py — Extract SamTimer symbol addresses from a vmlinux ELF.

Obtain vmlinux.elf from the device's boot partition:

    # Try direct ADB read (often works without root on Samsung user builds):
    adb shell "dd if=/dev/block/by-name/boot of=/sdcard/boot_a55.img bs=4096" \
      && adb pull /sdcard/boot_a55.img .

    # Extract the vmlinux ELF (requires vmlinux-to-elf):
    pip install vmlinux-to-elf
    vmlinux-to-elf boot_a55.img a55_vmlinux.elf

    # Then run:
    python3 tools/derive_offsets_nm.py a55_vmlinux.elf [a55_btf.bin]

Also reads /proc/iomem output for MEMSTART_ADDR:
    adb shell cat /proc/iomem > a55_iomem.txt
    python3 tools/derive_offsets_nm.py a55_vmlinux.elf --iomem a55_iomem.txt

Requires: nm, objdump (from binutils or llvm-binutils; arm64 cross-tools work too).
    apt-get install binutils-aarch64-linux-gnu
    # then: NM=aarch64-linux-gnu-nm OBJDUMP=aarch64-linux-gnu-objdump python3 ...
"""

import re
import subprocess
import sys
import os
from typing import Optional

NM      = os.environ.get('NM',      'nm')
OBJDUMP = os.environ.get('OBJDUMP', 'objdump')


# ---------------------------------------------------------------------------
# nm helpers
# ---------------------------------------------------------------------------

def _run_nm(elf: str) -> dict:
    """Return {symbol_name: address} for all symbols in the ELF."""
    try:
        out = subprocess.check_output([NM, '--defined-only', '-n', elf],
                                      stderr=subprocess.DEVNULL,
                                      timeout=120)
    except (subprocess.CalledProcessError, FileNotFoundError) as e:
        raise SystemExit(f"nm failed: {e}\nSet NM= env to override binary (e.g. NM=aarch64-linux-gnu-nm)") from e
    syms = {}
    for line in out.decode('utf-8', errors='replace').splitlines():
        parts = line.split()
        if len(parts) >= 3:
            try:
                syms[parts[2]] = int(parts[0], 16)
            except ValueError:
                pass
    return syms


def _sym(syms: dict, name: str, fallbacks=()) -> Optional[int]:
    if name in syms:
        return syms[name]
    for fb in fallbacks:
        if fb in syms:
            return syms[fb]
    return None


# ---------------------------------------------------------------------------
# objdump helpers — find kmem_cache_alloc return addresses (callsite anchors)
# ---------------------------------------------------------------------------

def _disasm_func(elf: str, func_name: str) -> list:
    """Return lines of objdump disassembly for the named function."""
    try:
        out = subprocess.check_output(
            [OBJDUMP, '-d', '--no-show-raw-insn',
             f'--disassemble={func_name}', elf],
            stderr=subprocess.DEVNULL,
            timeout=180)
    except (subprocess.CalledProcessError, FileNotFoundError):
        return []
    return out.decode('utf-8', errors='replace').splitlines()


# Pattern: "  ffffffc00812abcd:  bl  ffffffc008456780 <kmem_cache_alloc>"
# The return address is the address of the NEXT instruction.
_BL_RE = re.compile(
    r'^\s*([0-9a-f]+):\s+bl\s+[0-9a-f]+\s+<(kmem_cache_alloc\S*)>'
)
_ADDR_RE = re.compile(r'^\s*([0-9a-f]+):')


def _find_alloc_callsite(elf: str, func_name: str) -> Optional[int]:
    """
    Disassemble func_name and return the return address of the FIRST
    'bl <kmem_cache_alloc*>' instruction (i.e. address of next insn).
    """
    lines = _disasm_func(elf, func_name)
    prev_addr = None
    for i, line in enumerate(lines):
        # Track the current instruction address
        m_addr = _ADDR_RE.match(line)
        if m_addr:
            prev_addr = int(m_addr.group(1), 16)

        m_bl = _BL_RE.match(line)
        if m_bl:
            bl_addr = int(m_bl.group(1), 16)
            # Return address = address of next instruction = bl_addr + 4
            return bl_addr + 4

    return None


# ---------------------------------------------------------------------------
# /proc/iomem parser — extract MEMSTART_ADDR
# ---------------------------------------------------------------------------

def _parse_iomem(path: str) -> Optional[int]:
    try:
        with open(path) as f:
            for line in f:
                line = line.strip()
                if 'System RAM' in line or 'DRAM' in line:
                    m = re.match(r'^([0-9a-f]+)-', line, re.I)
                    if m:
                        return int(m.group(1), 16)
    except OSError:
        pass
    return None


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    import argparse
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('vmlinux', help='Path to vmlinux ELF (from vmlinux-to-elf)')
    ap.add_argument('--iomem', metavar='FILE',
                    help='Path to adb-pulled /proc/iomem output for MEMSTART_ADDR')
    args = ap.parse_args()

    elf = args.vmlinux

    print(f"[*] Running nm on {elf} ...", file=sys.stderr)
    syms = _run_nm(elf)
    print(f"[*] Loaded {len(syms)} symbols.", file=sys.stderr)

    # ---- Symbol addresses ----
    selinux_state        = _sym(syms, 'selinux_state')
    panic_on_warn        = _sym(syms, 'panic_on_warn')
    system_unbound_wq    = _sym(syms, 'system_unbound_wq')
    umh_exec_work        = _sym(syms, 'call_usermodehelper_exec_work')
    creds_fast_hash      = _sym(syms, 'creds_fast_hash',
                                 ('creds_fast_hash_enabled',))
    root_user            = _sym(syms, 'root_user')
    init_user_ns         = _sym(syms, 'init_user_ns')
    init_ucounts         = _sym(syms, 'init_ucounts')
    init_groups          = _sym(syms, 'init_groups')
    anon_pipe_buf_ops    = _sym(syms, 'anon_pipe_buf_ops')
    kernel_va_base_sym   = _sym(syms, '_text', ('stext',))
    kernel_phys_load_sym = _sym(syms, '_text', ('stext',))  # unslid VA

    # ---- Callsite addresses ----
    print(f"[*] Disassembling do_timer_create ...", file=sys.stderr)
    static_timer_site = _find_alloc_callsite(elf, 'do_timer_create')

    print(f"[*] Disassembling prepare_creds ...", file=sys.stderr)
    cred_site = _find_alloc_callsite(elf, 'prepare_creds')

    print(f"[*] Disassembling dup_task_struct ...", file=sys.stderr)
    task_site = _find_alloc_callsite(elf, 'dup_task_struct')

    # ---- MEMSTART_ADDR from iomem ----
    memstart = None
    if args.iomem:
        memstart = _parse_iomem(args.iomem)
        if memstart is not None:
            print(f"[*] MEMSTART_ADDR from {args.iomem}: {memstart:#x}", file=sys.stderr)
    if memstart is None:
        # Default assumption for Exynos mid-range; verify!
        memstart = 0x80000000
        print(f"[*] MEMSTART_ADDR: assumed {memstart:#x} (verify with --iomem)", file=sys.stderr)

    # ---- KERNEL_PHYS_LOAD ----
    # On GKI aarch64 builds the kernel loads at MEMSTART_ADDR (physical).
    # The unslid _text virtual address - KERNEL_VA_BASE gives the offset
    # from the physical load, but typically = MEMSTART_ADDR on Samsung.
    kernel_phys_load = memstart  # conservative assumption

    # ---- Report ----
    def v(val, name=''):
        if val is None:
            return f'0x/* TODO -- {name} not found in nm output */'
        return f'0x{val:016x}ULL'

    def vi(val):
        if val is None:
            return '/* TODO */'
        return f'0x{val:016x}ULL'

    print()
    print("=" * 70)
    print("  SamTimer nm/disasm-derived symbol addresses")
    print(f"  Source: {elf}")
    print("=" * 70)
    print()

    checks = [
        ("STATIC_TIMER_SITE", static_timer_site),
        ("CRED_SITE_STATIC", cred_site),
        ("TASK_SITE_STATIC", task_site),
        ("SELINUX_STATE_STATIC", selinux_state),
        ("PANIC_ON_WARN_STATIC", panic_on_warn),
        ("SYSTEM_UNBOUND_WQ_STATIC", system_unbound_wq),
        ("UMH_EXEC_WORK_STATIC", umh_exec_work),
        ("CREDS_FAST_HASH_STATIC", creds_fast_hash),
        ("ROOT_USER_STATIC", root_user),
        ("INIT_USER_NS_STATIC", init_user_ns),
        ("INIT_UCOUNTS_STATIC", init_ucounts),
        ("INIT_GROUPS_STATIC", init_groups),
        ("ANON_PIPE_BUF_OPS_STATIC", anon_pipe_buf_ops),
        ("MEMSTART_ADDR", memstart),
        ("KERNEL_PHYS_LOAD", kernel_phys_load),
    ]

    for name, val in checks:
        status = 'DERIVED' if val is not None else '*** MISSING ***'
        print(f"  {name:<40} {vi(val):<30}  [{status}]")

    if static_timer_site:
        low21 = static_timer_site & 0x1fffff
        print(f"\n  TIMER_SITE_LOW21  = 0x{low21:06x}ULL")
    if task_site:
        low21 = task_site & 0x1fffff
        print(f"  TASK_ALLOC_LOW21  = 0x{low21:06x}ULL")

    print()
    missing = [n for n, v in checks if v is None]
    if missing:
        print(f"  *** {len(missing)} symbol(s) not found: {', '.join(missing)}")
        print(f"  *** Ensure the ELF has symbols (vmlinux-to-elf output should).")
        print(f"  *** For creds_fast_hash: Samsung DEFEX may use a different name.")
        print(f"  ***   grep for 'creds_fast_hash' in nm output:")
        print(f"  ***   nm {elf} | grep -i creds")
        print()

    # ---- Generate C block ----
    print("=" * 70)
    print("  C #define block — symbol addresses section of offsets.h")
    print("=" * 70)
    print()
    print(f"/* SM-A556E (Exynos 1480) symbol addresses from nm + disasm */")
    print(f"#define STATIC_TIMER_SITE        {vi(static_timer_site)}")
    if static_timer_site:
        print(f"#define TIMER_SITE_LOW21         0x{static_timer_site & 0x1fffff:06x}ULL")
    else:
        print(f"#define TIMER_SITE_LOW21         0x/* TODO */ULL")
    print(f"#define CRED_SITE_STATIC         {vi(cred_site)}")
    print(f"#define TASK_SITE_STATIC         {vi(task_site)}")
    if task_site:
        print(f"#define TASK_ALLOC_LOW21         0x{task_site & 0x1fffff:06x}ULL")
    else:
        print(f"#define TASK_ALLOC_LOW21         0x/* TODO */ULL")
    print(f"#define SELINUX_STATE_STATIC     {vi(selinux_state)}")
    print(f"#define PANIC_ON_WARN_STATIC     {vi(panic_on_warn)}")
    print(f"#define SYSTEM_UNBOUND_WQ_STATIC {vi(system_unbound_wq)}")
    print(f"#define UMH_EXEC_WORK_STATIC     {vi(umh_exec_work)}")
    print(f"#define CREDS_FAST_HASH_STATIC   {vi(creds_fast_hash)}")
    print(f"#define ROOT_USER_STATIC         {vi(root_user)}")
    print(f"#define INIT_USER_NS_STATIC      {vi(init_user_ns)}")
    print(f"#define INIT_UCOUNTS_STATIC      {vi(init_ucounts)}")
    print(f"#define INIT_GROUPS_STATIC       {vi(init_groups)}")
    print(f"#define ANON_PIPE_BUF_OPS_STATIC {vi(anon_pipe_buf_ops)}")
    print(f"#define MEMSTART_ADDR            0x{memstart:016x}ULL")
    print(f"#define KERNEL_PHYS_LOAD         0x{kernel_phys_load:016x}ULL")
    print(f"/* KERNEL_PHYS_CANDIDATES covers common Exynos load addresses */")
    print(f"#define KERNEL_PHYS_CANDIDATES \\")
    print(f"    0x{memstart:016x}ULL, 0xa8000000ULL, 0xa0000000ULL, 0x88000000ULL, \\")
    print(f"    0x90000000ULL, 0xb0000000ULL")
    print()


if __name__ == '__main__':
    main()
