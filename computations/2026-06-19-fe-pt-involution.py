#!/usr/bin/env python3
# Verification for: completed-connection-category.md §3 — the FE is a PT-involution.
# iota: s -> 1-s.  Claim: iota d_s iota^{-1} = -d_s  (archimedean Time-reversal of the s-flow).
# Fix(iota) = {Re=1/2} (the critical line / constraint surface).
# Local, sub-second, no runpod.
import mpmath as mp
mp.mp.dps = 25

iota = lambda f: (lambda s: f(1 - s))          # (iota f)(s) = f(1-s); iota is its own inverse
ds = lambda f, s: mp.diff(f, s)

tests = [
    ('exp',      lambda s: mp.e**(mp.mpf('0.7') * s)),
    ('Gamma*zeta(+2)', lambda s: mp.gamma(s) * mp.zeta(s + 2)),
    ('poly',     lambda s: s**3 - 2*s),
]
print("iota d_s iota^{-1} f  vs  -d_s f :")
for name, f in tests:
    finv = iota(f)                              # iota^{-1} f = f(1-.)
    g = lambda s: ds(finv, s)                   # d_s (iota^{-1} f)
    lhs = iota(g)                               # iota d_s iota^{-1} f
    for s in [mp.mpf('0.3'), mp.mpf('1.4')]:
        print("  %-16s s=%s  |iota d_s iota^{-1} f - (-d_s f)|=%.1e"
              % (name, mp.nstr(s, 2), float(abs(lhs(s) - (-ds(f, s))))))

print()
print("==> iota d_s iota^{-1} = -d_s : FE = Time-reversal of the s-flow (D=d_s -> -D).")
print("    Fix(iota): 1-s=s  =>  s=1/2  => the critical line = the constraint surface.")
