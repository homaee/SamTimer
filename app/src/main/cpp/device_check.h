#ifndef DEVICE_CHECK_H
#define DEVICE_CHECK_H

/*
 * device_check.h -- hard safety block for CVE-2026-98260.
 *
 * offsets.h was derived from ONE specific vmlinux (SM-S921N, Exynos 2400,
 * 6.1.162-android14-11).  Running on any other kernel build produces
 * immediate kernel memory corruption and a forced reboot.
 *
 * To add a new device:
 *  1. Obtain the vmlinux or System.map for that exact firmware build.
 *  2. Re-derive every constant in offsets.h (see the comment there).
 *  3. Add the device model string to DEVICE_ALLOWED_MODELS below.
 *  4. Update SUPPORTED_DEVICE_FP as a comment record.
 *  5. Test iteratively on a physical device — compilation is not evidence.
 */

/* Kernel version substring that must appear in /proc/version for the
 * offsets in offsets.h to be valid. */
#define OFFSETS_KERNEL_SUBSTR "6.1.162-android14-11"

/* Devices verified against the offsets in offsets.h (NULL-terminated).
 * RootService.kt writes device.allowed with the ro.product.model string;
 * the C check verifies the string is in this list. */
static const char *const DEVICE_ALLOWED_MODELS[] = {
    "SM-S921N",
    NULL
};

/* File written by RootService.kt before launching the binary.
 * Path is relative to CWD = /data/local/tmp/samtimer (set by ProcessBuilder).
 * Content: DEVICE_ALLOW_MAGIC + Build.MODEL + ":" + Build.HARDWARE + "\n" */
#define DEVICE_ALLOW_FILE  "device.allowed"
#define DEVICE_ALLOW_MAGIC "SAMTIMER_OK:"

/*
 * device_safety_check() - hard abort if the running device/kernel does not
 * match the offsets in offsets.h.  Call this in main() before any exploit
 * code.  Does NOT apply to helper sub-commands (--umh, setksu, setshell,
 * wait) which run post-exploitation and do not use kernel symbol addresses.
 *
 * Layer 1 (Kotlin gate): reads DEVICE_ALLOW_FILE written by RootService.kt.
 *   If missing: the binary was launched without going through RootService,
 *   so we cannot know the device is safe.  Block unconditionally.
 *   If present: verify it starts with DEVICE_ALLOW_MAGIC and that the model
 *   field is in DEVICE_ALLOWED_MODELS.  Unlink after reading (one-use token).
 *
 * Layer 2 (kernel-string check): reads /proc/version and verifies the
 *   OFFSETS_KERNEL_SUBSTR substring is present.  Independent of Layer 1.
 *
 * Returns 0 if both checks pass, -1 on any mismatch.
 */
static int device_safety_check(void)
{
    char buf[512];
    int fd;
    int i;

    /* ---- Layer 1: Kotlin-written allow-token ---- */
    fd = open(DEVICE_ALLOW_FILE, O_RDONLY);
    if (fd < 0) {
        fprintf(stdout,
            "DEVICE_BLOCKED: allow-token missing (%s not found).\n"
            "This binary requires RootService.kt to validate the device before\n"
            "launch. The offsets in offsets.h are specific to SM-S921N (Exynos\n"
            "2400); running on any other device corrupts kernel memory.\n",
            DEVICE_ALLOW_FILE);
        return -1;
    }
    memset(buf, 0, sizeof(buf));
    (void)!read(fd, buf, sizeof(buf) - 1);
    close(fd);
    unlink(DEVICE_ALLOW_FILE); /* single-use token */

    if (strncmp(buf, DEVICE_ALLOW_MAGIC, strlen(DEVICE_ALLOW_MAGIC)) != 0) {
        fprintf(stdout,
            "DEVICE_BLOCKED: allow-token content is not valid "
            "(got \"%.*s\").\n",
            (int)(sizeof(buf) - 1), buf);
        return -1;
    }

    /* Model field follows the magic prefix. */
    const char *model_start = buf + strlen(DEVICE_ALLOW_MAGIC);
    int model_ok = 0;
    for (i = 0; DEVICE_ALLOWED_MODELS[i] != NULL; i++) {
        size_t mlen = strlen(DEVICE_ALLOWED_MODELS[i]);
        if (strncmp(model_start, DEVICE_ALLOWED_MODELS[i], mlen) == 0 &&
            (model_start[mlen] == ':' || model_start[mlen] == '\n' ||
             model_start[mlen] == '\0')) {
            model_ok = 1;
            break;
        }
    }
    if (!model_ok) {
        /* Extract model string for the error message (up to first ':' or '\n'). */
        char model_found[64];
        size_t ml = 0;
        while (ml < sizeof(model_found) - 1 &&
               model_start[ml] != ':' && model_start[ml] != '\n' &&
               model_start[ml] != '\0')
            ml++;
        memcpy(model_found, model_start, ml);
        model_found[ml] = '\0';

        fprintf(stdout,
            "DEVICE_BLOCKED: device model \"%s\" is not in the supported list.\n"
            "Supported: %s\n"
            "The offsets in offsets.h were verified on SM-S921N (Exynos 2400)\n"
            "only.  Running on \"%s\" will corrupt kernel memory and reboot the\n"
            "device.  See the porting guide in device_check.h to add support.\n",
            model_found,
            DEVICE_ALLOWED_MODELS[0],
            model_found);
        return -1;
    }

    /* ---- Layer 2: /proc/version kernel-string check ---- */
    memset(buf, 0, sizeof(buf));
    fd = open("/proc/version", O_RDONLY);
    if (fd >= 0) {
        (void)!read(fd, buf, sizeof(buf) - 1);
        close(fd);
    }
    if (!strstr(buf, OFFSETS_KERNEL_SUBSTR)) {
        fprintf(stdout,
            "DEVICE_BLOCKED: kernel version mismatch.\n"
            "  running : \"%.*s\"\n"
            "  required: contains \"" OFFSETS_KERNEL_SUBSTR "\"\n"
            "The offsets in offsets.h were derived from %s.  A different\n"
            "kernel build invalidates every symbol address and struct offset.\n",
            (int)(sizeof(buf) - 1), buf,
            OFFSETS_KERNEL_SUBSTR);
        return -1;
    }

    return 0;
}

#endif /* DEVICE_CHECK_H */
