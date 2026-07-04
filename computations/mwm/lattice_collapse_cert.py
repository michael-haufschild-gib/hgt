#!/usr/bin/env python3
"""Pre-certification for doc 50 + CascadeGeometric.lean (task #150/#151).

PRE-REGISTERED PREDICTIONS (written before running):
  P-L1 (collapse):   e^{-i pi (4pm + m^2)} == w^m exactly (fp ~1e-10), w = e^{-i pi (1+4p)},
                     for m <= 300 and 40 random p.
  P-L2 (denominator): |1 - w| == 2|cos(2 pi p)| to fp precision, same p sample.
  P-L3 (Abel bound): for antitone nonneg envelopes a_m in {const, 1/(1+m), (1-m/M), e^{-m/50}}
                     and p away from quarter-points, max_K |sum_{m<K} a_m w^m| <= 2 a_0 / |1-w|,
                     with the largest observed ratio bound/actual reported (expect >= 1, and
                     the bound attained within factor ~2 at worst p).
  P-L4 (drift):      exact step Delta(m) = -t log((N-m)/(N-m-1)) at t = 2 pi (N+p)^2 satisfies
                     Delta(m) === -pi(1 + 4 p_eff(m)) mod 2pi with
                     p_eff(m) = p + (m+p)(m+p+1)/(2(N-m)) + (m+p)^2/(4(N-m)^2) + 1/(6N) + err,
                     |err| <= C (m+1)^2/N^2 + C/N^2 predicted with C ~ 10, for N = 10^4,
                     m <= 400, p in {0.1, 0.37}.
"""
import mpmath as mp
import random

mp.mp.dps = 30
random.seed(88406217641540469)

pi = mp.pi
I = mp.mpc(0, 1)

def w_of(p):
    return mp.e**(-I * pi * (1 + 4 * p))

# ---------- P-L1 collapse ----------
worst1 = mp.mpf(0)
for _ in range(40):
    p = mp.mpf(random.random())
    w = w_of(p)
    for m in range(0, 301, 7):
        lhs = mp.e**(-I * pi * (4 * p * m + m * m))
        rhs = w**m
        worst1 = max(worst1, abs(lhs - rhs))
print("P-L1 collapse max|lhs-rhs| =", mp.nstr(worst1, 5), "PASS" if worst1 < mp.mpf("1e-18") else "FAIL")

# ---------- P-L2 denominator ----------
worst2 = mp.mpf(0)
for _ in range(40):
    p = mp.mpf(random.random())
    w = w_of(p)
    worst2 = max(worst2, abs(abs(1 - w) - 2 * abs(mp.cos(2 * pi * p))))
print("P-L2 denominator max err =", mp.nstr(worst2, 5), "PASS" if worst2 < mp.mpf("1e-25") else "FAIL")

# ---------- P-L3 Abel bound ----------
M = 240
envs = {
    "const": [mp.mpf(1)] * M,
    "1/(1+m)": [mp.mpf(1) / (1 + m) for m in range(M)],
    "linear": [mp.mpf(1) - mp.mpf(m) / M for m in range(M)],
    "exp": [mp.e**(-mp.mpf(m) / 50) for m in range(M)],
}
viol = 0
worst_ratio = mp.mpf('inf')   # min over samples of bound/actual (should stay >= 1)
for _ in range(60):
    p = mp.mpf(random.random())
    if min(abs(p - mp.mpf('0.25')), abs(p - mp.mpf('0.75'))) < mp.mpf('0.02'):
        continue
    w = w_of(p)
    bound_denom = abs(1 - w)
    for name, a in envs.items():
        bound = 2 * a[0] / bound_denom
        s = mp.mpc(0)
        mx = mp.mpf(0)
        for m in range(M):
            s += a[m] * w**m
            mx = max(mx, abs(s))
        if mx > bound * (1 + mp.mpf('1e-20')):
            viol += 1
            print("  VIOLATION", name, mp.nstr(p, 6), mp.nstr(mx, 8), mp.nstr(bound, 8))
        worst_ratio = min(worst_ratio, bound / mx)
print("P-L3 Abel bound violations =", viol, "; tightest bound/actual =", mp.nstr(worst_ratio, 5),
      "PASS" if viol == 0 else "FAIL")

# ---------- P-L4 drift ----------
N = 10000
worst4 = mp.mpf(0)
for p in [mp.mpf('0.1'), mp.mpf('0.37')]:
    t = 2 * pi * (N + p)**2
    for m in range(0, 401, 13):
        j = N - m
        delta = -t * mp.log(mp.mpf(j) / (j - 1))
        p_eff = p + (m + p) * (m + p + 1) / (2 * (j)) + (m + p)**2 / (4 * j**2) + mp.mpf(1) / (6 * N)
        model = -pi * (1 + 4 * p_eff)
        # compare mod 2pi
        d = (delta - model) / (2 * pi)
        d = d - mp.nint(d)
        err = abs(d * 2 * pi)
        allowed = 10 * (m + 1)**2 / mp.mpf(N)**2 + 10 / mp.mpf(N)**2
        if err > allowed:
            worst4 = max(worst4, err / allowed)
print("P-L4 drift: worst err/allowed =", mp.nstr(worst4, 5), "PASS" if worst4 == 0 else "FAIL")

# ---------- bonus: resonance blowup profile (for doc 50 table) ----------
print("\ncollective-push bound 1/|cos 2 pi p| at p = 0, .1, .19, .24, .25 :")
for ps in ['0', '0.1', '0.19', '0.24', '0.25']:
    p = mp.mpf(ps)
    c = abs(mp.cos(2 * pi * p))
    print("  p =", ps, " bound =", "inf" if c == 0 else mp.nstr(1 / c, 6))
