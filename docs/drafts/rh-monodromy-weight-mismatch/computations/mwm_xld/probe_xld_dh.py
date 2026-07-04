#!/usr/bin/env python3
"""Doc 76 probe, Davenport-Heilbronn side: truncation-valley persistence at
GENUINE off-line zeros. P-X3/P-X4 pre-registered in 76-xld-two-level.md.

Self-certifying construction (no recalled constants):
  kappa solved from Lambda(s) = Lambda(1-s) with Lambda = (5/pi)^((s+1)/2)
  Gamma((s+1)/2) F(s), F(s) = 5^{-s} [zeta(s,1/5) + k zeta(s,2/5)
  - k zeta(s,3/5) - zeta(s,4/5)]; FE re-verified at independent points.
  Off-line zeros: valley scan of Z_DH then mpmath findroot certification.
"""
import numpy as np, json, math
import mpmath as mp

MATCH = 0.3
BAND = (0.02, 0.60)     # accept off-line zeros in this eta/spacing band
T_LO, T_HI, DT = 60.0, 2000.0, 0.01

# ---------- kappa from the functional equation ----------
mp.mp.dps = 30
def F_of(s, kap):
    return mp.power(5, -s) * (mp.zeta(s, mp.mpf(1)/5) + kap*mp.zeta(s, mp.mpf(2)/5)
                              - kap*mp.zeta(s, mp.mpf(3)/5) - mp.zeta(s, mp.mpf(4)/5))
def Lam(s, kap, delta):
    return mp.power(5/mp.pi, (s+delta)/2) * mp.gamma((s+delta)/2) * F_of(s, kap)
def fe_defect(s, kap, delta):
    return Lam(s, kap, delta) - Lam(1-s, kap, delta)
kappa, DELTA = None, None
for delta in (1, 0):
    s0 = mp.mpc('0.3', '2.0')
    A = fe_defect(s0, 0, delta)
    B = fe_defect(s0, 1, delta) - A
    kap_try = -A/B
    if abs(mp.im(kap_try)) > mp.mpf('1e-18'):
        continue
    kap_try = mp.re(kap_try)
    ok = True
    for stest in [mp.mpc('0.7', '5.3'), mp.mpc('0.2', '11.1')]:
        d = abs(fe_defect(stest, kap_try, delta)) / abs(Lam(stest, kap_try, delta))
        if d > mp.mpf('1e-18'):
            ok = False
            break
    if ok:
        kappa, DELTA = kap_try, delta
        break
assert kappa is not None, "no gamma-factor candidate satisfies the FE"
print(json.dumps(dict(kappa=float(kappa), delta=DELTA)), flush=True)
KAP = float(kappa)
ACOEF = {1: 1.0, 2: KAP, 3: -KAP, 4: -1.0, 0: 0.0}

# ---------- vectorized Euler-Maclaurin Hurwitz zeta on s = 1/2 + it ----------
B2J = [1/6, -1/30, 1/42]
def hurwitz_line(t, a):
    """zeta(1/2 + it, a) for t 1d-array, scalar a in (0,1)."""
    out = np.empty(t.size, dtype=np.complex128)
    for i0 in range(0, t.size, 2000):
        tt = t[i0:i0+2000]
        s = 0.5 + 1j*tt
        M = int(1.5*tt.max()) + 50
        k = np.arange(M, dtype=np.float64) + a
        lg = np.log(k)
        mat = np.exp(np.multiply.outer(-s, lg))
        acc = mat.sum(axis=1)
        aM = M + a
        acc += aM**(1-s)/(s-1) + 0.5*aM**(-s)
        poch = s.copy()
        fac = 1.0
        for j, b in enumerate(B2J, start=1):
            fac_term = b / math.factorial(2*j)
            acc += fac_term * poch * aM**(-s - (2*j-1))
            poch = poch * (s + 2*j - 1) * (s + 2*j)
        out[i0:i0+2000] = acc
    return out

# validate EM against mpmath
mp.mp.dps = 20
for tchk in [77.3, 501.2, 1999.0]:
    for a5 in [1, 2, 3, 4]:
        em = hurwitz_line(np.array([tchk]), a5/5)[0]
        ref = complex(mp.zeta(mp.mpc(0.5, tchk), mp.mpf(a5)/5))
        assert abs(em - ref) < 1e-7 * max(1.0, abs(ref)), (tchk, a5, em, ref)
print(json.dumps(dict(em_hurwitz="validated 1e-7")), flush=True)

def theta5(t):
    z = (0.5 + DELTA)/2 + 0.5j*t
    lg = np.array([complex(mp.loggamma(complex(zz))) for zz in z])
    return 0.5*t*math.log(5/math.pi) + lg.imag

def Z_full(t):
    F = np.exp(-(0.5 + 1j*t)*math.log(5)) * (
        hurwitz_line(t, 0.2) + KAP*hurwitz_line(t, 0.4)
        - KAP*hurwitz_line(t, 0.6) - hurwitz_line(t, 0.8))
    u = np.exp(1j*theta5(t)) * F
    return u

# phase fold: Z must be real up to one constant phase
t_smp = np.linspace(T_LO+5, T_HI-5, 60)
u = Z_full(t_smp)
phi0 = 0.5*np.angle(np.mean((u/np.abs(u))**2))
res = np.max(np.abs(np.imag(u*np.exp(-1j*phi0)))) / np.max(np.abs(u))
if res > 1e-5:
    phi0 += np.pi/2
    res = np.max(np.abs(np.imag(u*np.exp(-1j*phi0)))) / np.max(np.abs(u))
assert res < 1e-5, f"phase fold failed: {res}"
print(json.dumps(dict(phi0=float(phi0), fold_residual=float(res))), flush=True)

def valleys(t, Z, dt):
    Zp = (np.roll(Z, -1) - np.roll(Z, 1)) / (2*dt)
    Zpp = (np.roll(Z, -1) - 2*Z + np.roll(Z, 1)) / dt**2
    sgn = np.sign(Zp)
    crit = np.where(sgn[:-1]*sgn[1:] < 0)[0]
    crit = crit[(crit > 5) & (crit < len(t)-6)]
    keep = Z[crit]*Zpp[crit] > 0
    crit = crit[keep]
    eta = np.sqrt(2*np.abs(Z[crit])/np.abs(Zpp[crit]))
    shift = np.clip(-Zp[crit]/Zpp[crit], -dt, dt)
    return t[crit]+shift, eta, Z[crit]

# ---------- stage 1: scan Z_DH, find + certify off-line zeros ----------
t = np.arange(T_LO, T_HI, DT)
Zg = np.real(Z_full(t) * np.exp(-1j*phi0))
tv_all, eta_all, zm_all = valleys(t, Zg, DT)
zeros = []
mp.mp.dps = 25
for tv, eta in zip(tv_all, eta_all):
    spacing = 2*math.pi/math.log(5*tv/(2*math.pi))
    if not (BAND[0] <= eta/spacing <= BAND[1]):
        continue
    try:
        root = mp.findroot(lambda s: F_of(s, kappa), mp.mpc(0.5+eta, tv))
    except Exception:
        continue
    sig, gam = float(mp.re(root)), float(mp.im(root))
    if abs(gam - tv) > 2*spacing or abs(sig - 0.5) < 1e-6:
        continue
    if abs(complex(F_of(root, kappa))) > 1e-15:
        continue
    zeros.append(dict(t=gam, sigma=sig, eta_scan=float(eta),
                      eta_true=abs(sig-0.5), spacing=spacing))
# dedupe
ded = []
for z in zeros:
    if not any(abs(z['t']-w['t']) < 0.5*z['spacing'] for w in ded):
        ded.append(z)
zeros = ded
print(json.dumps(dict(n_offline_zeros=len(zeros),
                      zeros=[(round(z['t'],4), round(z['sigma'],5)) for z in zeros])),
      flush=True)

# ---------- stage 2: truncation-valley lifetime at each certified zero ----------
def Z_trunc(tloc, psi, n):
    ks = np.arange(1, n+1)
    ak = np.array([ACOEF[k % 5] for k in ks])
    nz = ak != 0
    ks, ak = ks[nz].astype(np.float64), ak[nz]
    return 2*np.sum(ak[None,:]*np.cos(psi[:,None] - tloc[:,None]*np.log(ks)[None,:])
                    / np.sqrt(ks)[None,:], axis=1)

results = []
for z in zeros:
    tv, spacing = z['t'], z['spacing']
    nstar = int(round(math.sqrt(5*tv/(2*math.pi))))
    Wd = min(15, nstar - 3)
    tloc = np.arange(tv - 3*spacing, tv + 3*spacing, 0.002)
    psi = theta5(tloc) - phi0
    present = []
    rms_by_n = {}
    Zloc_full = np.real(Z_full(tloc)*np.exp(-1j*phi0))
    for n in range(nstar - Wd, nstar + Wd + 1):
        Zn = Z_trunc(tloc, psi, n)
        rms_by_n[n] = float(np.sqrt(np.mean((Zn - Zloc_full)**2)))
        tvv, ee, zz = valleys(tloc, Zn, 0.002)
        present.append(int(np.any(np.abs(tvv - tv) < MATCH*spacing)))
    # longest run and whether it covers nstar
    best, cur, s_best, s_cur = 0, 0, -1, 0
    for i, p in enumerate(present):
        if p:
            if cur == 0:
                s_cur = i
            cur += 1
            if cur > best:
                best, s_best = cur, s_cur
        else:
            cur = 0
    run_lo = nstar - Wd + s_best
    covers = run_lo <= nstar <= run_lo + best - 1
    pres = np.array(present, dtype=bool)
    cond = (pres[:-1] & pres[1:]).sum() / max(1, pres[:-1].sum())
    n_match_emp = min(rms_by_n, key=rms_by_n.get)
    results.append(dict(t=round(tv,4), sigma=round(z['sigma'],5),
                        eta_over_spacing=round(z['eta_true']/spacing, 4),
                        nstar=nstar, W=Wd, run=best, covers_matched=bool(covers),
                        frac_present=float(pres.mean()),
                        cond_persist=float(cond),
                        n_matched_emp=n_match_emp,
                        rms_at_matched=rms_by_n[nstar]))
    print(json.dumps(results[-1]), flush=True)

if results:
    summary = dict(n_zeros=len(results),
                   run_median=float(np.median([r['run'] for r in results])),
                   run_min=int(min(r['run'] for r in results)),
                   covers_frac=float(np.mean([r['covers_matched'] for r in results])),
                   cond_persist_mean=float(np.mean([r['cond_persist'] for r in results])))
    print(json.dumps(summary), flush=True)
