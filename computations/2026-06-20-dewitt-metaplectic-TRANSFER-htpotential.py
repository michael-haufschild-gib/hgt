#!/usr/bin/env python3
# MACHINE STEP7 done RIGHT: STRUCTURAL transfer of the metaplectic NODE-test script (minimal change).
# NODE test skeleton (unchanged): build H = p^2/2 + V(q); diagonalize -> exact spectrum;
#   Bohr-Sommerfeld count S(E)=oint p dq = 2*int sqrt(2(E-V)) dq ; solve S=2*pi*(n+mu/4);
#   test whether the +1/2 (mu=2 metaplectic/Maslov) shift is what matches the spectrum.
# ONLY CHANGE: the potential V(q). DA controls q^2, q^4  ->  HT seed potential V(q)=logGamma(2+q^2).
# Question (STEP8): does the metaplectic +1/2 hold for a HYPERTRANSCENDENTAL well, or is there anomaly?
import numpy as np
from scipy import integrate, optimize
import mpmath as mp

N = 200
a = np.diag(np.sqrt(np.arange(1, N)), 1)
ad = a.T.conj()
q = ((a + ad)/np.sqrt(2)).real
p = ((a - ad)/(1j*np.sqrt(2)))
P2 = (p @ p).real
# functional calculus on q for a general V (used for the HT potential)
lam, U = np.linalg.eigh(q)
def Vmat(Vfun):
    return (U * Vfun(lam)) @ U.T

def exact_spectrum(H, k=8):
    return np.sort(np.linalg.eigvalsh(H).real)[:k]

def bs_spectrum(Vfun, k=8, mu=2):
    # S(E)=2*int_{q-}^{q+} sqrt(2(E-V)) dq = 2*pi*(n+mu/4)  -> solve for E_n
    def Vscalar(x): return float(Vfun(np.array([x]))[0])
    V0 = Vscalar(0.0)
    def action(E):
        # find right turning point (even single well, min at 0)
        hi = 1.0
        while Vscalar(hi) < E: hi *= 1.6
        qp = optimize.brentq(lambda x: Vscalar(x)-E, 0.0, hi)
        val,_ = integrate.quad(lambda x: np.sqrt(max(2*(E-Vscalar(x)),0.0)), -qp, qp, limit=100)
        return 2*val   # oint p dq = 2 * (turning-point-to-turning-point integral)
    out=[]
    for n in range(k):
        target = 2*np.pi*(n+mu/4)
        if target <= 1e-9:
            out.append(V0); continue
        Elo, Ehi = V0+1e-9, V0+1.0
        while action(Ehi) < target: Ehi = V0 + (Ehi-V0)*1.8
        En = optimize.brentq(lambda E: action(E)-target, Elo, Ehi)
        out.append(En)
    return np.array(out)

def report(name, Vfun, useMat=False, Hexact=None):
    H = Hexact if Hexact is not None else Vmat(Vfun)
    e = exact_spectrum(0.5*P2 + H)
    print(f"\n=== {name} ===")
    print("  exact:", np.round(e,5))
    for mu in (0,2):
        ew = bs_spectrum(Vfun, mu=mu)
        # compare on levels 2..7 (WKB best for higher n; avoids ground-state WKB error)
        err = np.abs(ew-e)
        rel_hi = np.max(np.abs((ew[2:]-e[2:])/e[2:]))
        tag = "(+1/2 metaplectic)" if mu==2 else "(no corr)"
        print(f"  mu={mu} {tag}: BS={np.round(ew,4)}  rel-err(lvls2-7)={rel_hi:.3%}")
    # the metaplectic test: best-fit mu (does +1/2 i.e. mu=2 minimize error?)
    def fiterr(mu):
        ew=bs_spectrum(Vfun, mu=mu); return np.sum(((ew[2:]-e[2:])/e[2:])**2)
    mus=np.linspace(0,4,17)
    errs=[fiterr(m) for m in mus]
    best=mus[int(np.argmin(errs))]
    print(f"  best-fit Maslov mu (grid): {best:.2f}  (metaplectic predicts mu=2 -> +1/2). "
          f"err@2={fiterr(2):.2e}")
    return e

# ---- DA controls (potential = monomial) ----
report("CONTROL DA: V=q^2 (SHO)", lambda x: x**2, Hexact=(q@q))
report("CONTROL DA: V=q^4 (quartic)", lambda x: x**4, Hexact=(q@q@q@q))

# ---- HT transfer: ONLY V changed to a hypertranscendental seed potential ----
def V_ht(x):  # logGamma(2+q^2): even, single well (min at 0, since 2>min-arg 1.4616), HT
    return np.array([float(mp.re(mp.loggamma(2+xx*xx))) for xx in np.atleast_1d(x)])
report("HT TRANSFER: V=logGamma(2+q^2)", V_ht)

print("\nSTEP8 read: compare best-fit mu and +1/2 fit-quality of the HT well vs the DA controls.")
