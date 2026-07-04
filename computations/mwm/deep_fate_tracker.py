#!/usr/bin/env python3
"""(DEEP-FATE) — task #156, the ONE sanctioned computation of docs 48/49/51.

Track census off-line pairs through tower levels k: from below birth, through
the matched level N, to N+10. Carrier identical to the census
(euler_suppression_boxcount.make_phi, completed normalization).

PRE-REGISTERED (before run; docs 48 §3, 51 §8(3), 51 §9):
  P-DF1 (prior 0.80): max_k eta(k) <= 0.25 for every event — NO runaway
        deepening toward N^{-1/4} (0.36-0.52 in this N range).
  P-DF2 (prior 0.60): off-line run below matched level has length
        <= 3*N^{1/3} entries (absorption/birth locality).
  P-DF3 (prior 0.50, SHARP): past matched level every pair dies fast —
        off-line pair gone (eta < 0.01 or lost) by k = N + 3 (slip budget
        2*pi*d^2 <= 0.236 exhausted at the first integer step; no re-lock).
Falsification of P-DF3 = the hold story needs repair. Failure of P-DF1 =
the deepen branch is real and (MID-central) is in trouble.
"""
import sys
from mpmath import mp, mpc, mpf, pi, sqrt, findroot, fabs
from euler_suppression_boxcount import make_phi, coeffs

NC = 90  # N reaches 42+10 = 52; safe margin

EVENTS = [
    # (label, T, N, sigma, t, class)
    ("mb-1413", 1413.0, 14, '0.67106', '1415.6767', 'MID'),
    ("mb-4251", 4251.0, 26, '0.61541', '4253.5428', 'MID'),
    ("mb-4587", 4587.0, 27, '0.67795', '4589.7089', 'MID'),
    ("mb-4990", 4990.0, 28, '0.64232', '4990.3903', 'MID'),
    ("mb-6426", 6426.0, 31, '0.61566', '6430.8007', 'MID'),
    ("mb-7709", 7709.0, 35, '0.59619', '7712.8523', 'MID'),
    ("mb-7734", 7734.0, 35, '0.59711', '7734.7144', 'MID'),
    ("mb-11123", 11123.0, 42, '0.62190', '11127.6330', 'MID'),
    ("sh-5360", 5360.0, 29, '0.54889', '5361.7772', 'SH'),
    ("sh-2295", 2295.0, 19, '0.53862', '2297.1914', 'SH'),
    ("sh-1766", 1766.0, 16, '0.56391', '1770.0831', 'SH'),
]


def find_pair(phi, seed):
    """Newton/secant root near seed; classify."""
    try:
        r = findroot(phi, seed, tol=1e-24, maxsteps=60)
    except Exception:
        return None, 'lost'
    if fabs(phi(r)) > mpf('1e-15'):
        return None, 'lost'
    eta = float(r.real - mpf('0.5'))
    if abs(float(r.imag) - float(seed.imag)) > 3.0:
        return None, 'migrated'
    if eta < 1e-4:
        return r, 'online'
    return r, 'pair'


def track(label, T, N, sig, t0, cls):
    mp.dps = 30
    a = coeffs('E', 0, NC)
    rows = []
    # upward from matched level
    seed = mpc(mpf(sig), mpf(t0))
    for k in range(N, N + 11):
        phi = make_phi(a, k)
        r, st = find_pair(phi, seed)
        eta = float(r.real - 0.5) if r is not None else float('nan')
        rows.append((k, st, eta))
        if st != 'pair':
            break
        seed = r
    # downward from matched level
    seed = mpc(mpf(sig), mpf(t0))
    down = []
    for k in range(N - 1, max(1, N - 16), -1):
        phi = make_phi(a, k)
        r, st = find_pair(phi, seed)
        eta = float(r.real - 0.5) if r is not None else float('nan')
        down.append((k, st, eta))
        if st != 'pair':
            break
        seed = r
    out = [f"{label} (N={N}, {cls}):"]
    for k, st, eta in sorted(down) + rows:
        out.append(f"  k={k:3d} {st:8s} eta={eta:+.4f}")
    return "\n".join(out)


if __name__ == '__main__':
    for ev in EVENTS:
        print(track(*ev))
        sys.stdout.flush()
    print("done")
