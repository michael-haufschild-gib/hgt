"""
Pre-certify the prime->zero linear-response susceptibility formula.

Claim (single Dirichlet-coefficient perturbation):
    zeta_eps(s) = zeta(s) + eps * n^{-s}
A simple zero rho moves as
    drho/deps = - n^{-rho} / zeta'(rho).

Verify by central finite difference at the first few zeros, for n=2 and n=3.

Also exhibit the FE-mirror susceptibility ratio scaling exponent:
    |chi_n(rho)| ~ n^{-Re rho}/|zeta'(rho)|,   ratio(rho,1-rho) ~ n^{1-2 Re rho},
so frequency(n)-independence <=> Re rho = 1/2  (the criticality / FE-balance signature).
"""
import mpmath as mp

mp.mp.dps = 40

def rho_of_eps(n, eps, rho0):
    # solve zeta(s) + eps * n^{-s} = 0 near rho0
    f = lambda s: mp.zeta(s) + eps * mp.power(n, -s)
    return mp.findroot(f, rho0)

print("n   k   rho0(approx)             predicted d_rho/d_eps           finite-diff               |rel err|")
for n in (2, 3):
    for k in (1, 2, 3):
        rho0 = mp.zetazero(k)
        zp = mp.zeta(rho0, derivative=1)
        pred = -mp.power(n, -rho0) / zp
        h = mp.mpf('1e-12')
        rp = rho_of_eps(n, h, rho0)
        rm = rho_of_eps(n, -h, rho0)
        fd = (rp - rm) / (2*h)
        relerr = abs(fd - pred) / abs(pred)
        print(f"{n}   {k}   {mp.nstr(rho0,8):>22}   {mp.nstr(pred,10):>28}   {mp.nstr(fd,10):>22}   {mp.nstr(relerr,3)}")

print()
print("FE-mirror amplitude exponent check (analytic): |n^{-beta}| / |n^{-(1-beta)}| = n^{1-2 beta}")
for beta in (mp.mpf('0.5'), mp.mpf('0.4'), mp.mpf('0.3')):
    for n in (2, 5, 100):
        ratio = mp.power(n, 1 - 2*beta)
        print(f"  beta={float(beta):.2f}  n={n:>4}  n^(1-2beta) = {mp.nstr(ratio,8)}   (==1 iff beta=0.5)")
