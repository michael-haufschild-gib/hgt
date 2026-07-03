# R9-mini [PRE-REGISTERED]: mirror-identity test for 16-pinning-and-emission.md §3.
# Family: f_k(s) = c_k L(s,chi) + conj(c_k) L(s,chibar),  c_k = (1-ik)/2, chi mod 5 with chi(2)=i.
# L(s,chi) = 5^{-s} * sum_{a=1}^{4} chi(a) * hurwitz(s, a/5).
# PREDICTIONS:
#   P0: f_kappa(rho_certified) ~ 0 (implementation sanity, residual < 1e-10)
#   P1: for k1 = kappa+0.03, the zero rho(k1) continued from rho_certified exists (Muller converges)
#   P2: with k' = tan(2*atan(kappa) - atan(k1)), f_{k'} has a zero at 1 - conj(rho(k1)),
#       within 1e-10 (dps 30). Same for k1 = kappa-0.05.
#   FAILURE would mean the epsilon/chibar normalization in doc 16 Sec 3 is wrong.
from mpmath import mp, mpc, mpf, zeta, tan, atan, sqrt, findroot, fabs

mp.dps = 30
i = mpc(0, 1)
chi = {1: mpc(1), 2: i, 3: -i, 4: mpc(-1)}
kappa = (sqrt(10 - 2*sqrt(5)) - 2) / (sqrt(5) - 1)
print("kappa =", kappa)

def L(s, conj_char=False):
    tot = mpc(0)
    for a in range(1, 5):
        c = chi[a].conjugate() if conj_char else chi[a]
        tot += c * zeta(s, mpf(a)/5)
    return 5**(-s) * tot

def f(k, s):
    c = (1 - i*k)/2
    return c * L(s) + c.conjugate() * L(s, conj_char=True)

rho0 = mpc("0.808517182456637386", "85.6993484853775922")

# P0
r0 = f(kappa, rho0)
print("P0 residual |f_kappa(rho)| =", fabs(r0))

def zero_near(k, seed):
    return findroot(lambda s: f(k, s), seed, solver='muller', tol=1e-25)

for dk in [mpf("0.03"), mpf("-0.05")]:
    k1 = kappa + dk
    rho1 = zero_near(k1, rho0)
    kp = tan(2*atan(kappa) - atan(k1))
    pred = 1 - rho1.conjugate()
    try:
        rho2 = zero_near(kp, pred)
        err = fabs(rho2 - pred)
        print(f"dk={dk}: k1={k1}, rho(k1)={rho1}")
        print(f"        k'={kp}, predicted mirror={pred}")
        print(f"        found zero of f_k' ={rho2}")
        print(f"        |found - predicted| = {err}   -> {'PASS' if err < 1e-10 else 'FAIL'}")
    except Exception as e:
        print(f"dk={dk}: k'={kp} Muller FAILED from predicted seed: {e}  -> FAIL")
