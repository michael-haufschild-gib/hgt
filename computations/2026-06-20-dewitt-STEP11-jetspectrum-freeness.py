#!/usr/bin/env python3
# MACHINE STEP11 (wild experiment, no predictable outcome): metaphor freeness<->HT.
# Freeness signature = a UNIVERSAL spectral shape (Marchenko-Pastur) from maximal independence.
# HT "constraint not flow" = derivative tower maximally differentially-independent (no finite ADE).
# WILD QUESTION: does an HT function's derivative-JET COVARIANCE spectrum fall in the free/random
# universality class (MP), or a rigid/structured class? Method#16: minimal jet order R that witnesses it.
import numpy as np
import mpmath as mp
mp.mp.dps = 30

N = 60                      # sample points (2 disjoint intervals)
xs = [mp.mpf('1.3')+i*mp.mpf('0.13') for i in range(N//2)] + [mp.mpf('9.0')+i*mp.mpf('0.13') for i in range(N//2)]
R = 14                     # jet orders 0..R-1

def jet_cov_spectrum(colfun, label):
    # build N x R jet matrix, column-standardize (zero mean, unit var per derivative order), eigenvalues of R x R corr
    M = np.zeros((N,R))
    for k in range(R):
        col = colfun(k)
        M[:,k] = np.array([float(c) for c in col])
    # standardize columns
    M = M - M.mean(0)
    sd = M.std(0); sd[sd==0]=1
    M = M/sd
    C = (M.T@M)/N
    ev = np.sort(np.linalg.eigvalsh(C))[::-1]
    ev = np.clip(ev,0,None)
    rank = int(np.sum(ev>1e-10))
    print(f"  {label:26s}: rank={rank:2d}/{R}  top5 eig={np.round(ev[:5],3)}  tail eig={np.round(ev[-3:],4)}")
    return ev

print(f"=== STEP11 wild: jet-covariance eigenvalue spectrum (N={N} pts, R={R} orders) ===")
# HT: logGamma jet = [logGamma, psi, psi', ...] = polygamma (accurate, fast)
def ht_col(k):
    if k==0: return [mp.loggamma(x) for x in xs]
    return [mp.polygamma(k-1, x) for x in xs]
ev_ht = jet_cov_spectrum(ht_col, "logGamma (HT)")
# HT2: try zeta jet via mp.diff
def zeta_col(k):
    return [mp.diff(lambda t: mp.zeta(t), x, k) for x in xs]
ev_z = jet_cov_spectrum(zeta_col, "zeta (HT)")
# DA controls
ev_exp = jet_cov_spectrum(lambda k: [mp.e**x for x in xs], "exp (DA, rank1)")
ev_sin = jet_cov_spectrum(lambda k: [mp.sin(x+k*mp.pi/2) for x in xs], "sin (DA, rank2)")
# FREE/random reference (Marchenko-Pastur): NxR iid Gaussian
rng=np.random.default_rng(7)
Xr=rng.normal(size=(N,R)); Xr=(Xr-Xr.mean(0))/Xr.std(0); Cr=(Xr.T@Xr)/N
ev_mp=np.sort(np.linalg.eigvalsh(Cr))[::-1]
print(f"  {'random iid (MP ref)':26s}: rank={int(np.sum(ev_mp>1e-10)):2d}/{R}  top5 eig={np.round(ev_mp[:5],3)}  tail eig={np.round(ev_mp[-3:],4)}")

print("\n=== shape: eigenvalue decay (log10) — structured(fast decay) vs free/MP(spread) ===")
for label,ev in [("logGamma(HT)",ev_ht),("zeta(HT)",ev_z),("MP ref",ev_mp)]:
    pos=ev[ev>1e-14]
    lg=np.log10(pos/pos[0])
    print(f"  {label:14s}: log10(eig/eig0) = {np.round(lg[:8],2)}")
print("\nMethod#16 (minimal): the minimal R where HT rank exceeds the DA controls' (1,2) = where HT's")
print("differential richness first shows. INTERPRET: is the HT jet-spectrum free/MP-like or rigid/structured?")
