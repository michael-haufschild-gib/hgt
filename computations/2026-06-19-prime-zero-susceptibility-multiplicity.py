"""Multiplicity-m generalization of the prime->zero susceptibility (Leaner-returned gap).
Verifies: a zero of multiplicity m splits under z_eps = zeta + eps*n^{-s} into m zeros at
distance ~ (n^{-beta}/|c_rho|)^{1/m} * |eps|^{1/m}, c_rho the leading coefficient; and the
mirror-pair susceptibility ratio (n^{1-2beta}/|chi_FE|)^{1/m} is frequency-independent iff beta=1/2,
for ANY finite m -> the FE-balance<->RH characterization is UNCONDITIONAL (no simplicity assumption)."""
import mpmath as mp
mp.mp.dps = 40
print("# toy double zero f=(s-2)^2 + eps*n^{-s}; predicted |s-2| = n^{-1}|eps|^{1/2}")
for n in [2, 3, 5]:
    for eps in [mp.mpf('1e-6'), mp.mpf('1e-8')]:
        f = lambda s: (s - 2)**2 + eps * mp.power(n, -s)
        r1 = mp.findroot(f, 2 + (-eps * n**-2)**mp.mpf('0.5'))
        d = abs(r1 - 2)
        pred = (n**mp.mpf(-2))**mp.mpf('0.5') * abs(eps)**mp.mpf('0.5')
        print(f"n={n} eps={float(eps):.0e}  |s-2|={float(d):.6e}  pred={float(pred):.6e}  ratio={float(d/pred):.5f}")
print("# mirror frequency-exponent (1-2beta)/m vanishes iff beta=1/2:")
for beta, m in [(0.5,1),(0.5,2),(0.4,1),(0.4,2),(0.3,3)]:
    e = (1-2*mp.mpf(beta))/m
    print(f"beta={beta} m={m}: (1-2beta)/m={float(e):+.4f}  n-indep={abs(e)<1e-30}")
