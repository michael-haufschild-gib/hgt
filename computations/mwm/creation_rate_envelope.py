#!/usr/bin/env python3
"""Creation-rate reader (doc 52) across p in [0,1/2]: does birth INTENSITY carry
the B(p)=|cos(pi/8-2pi p^2)| envelope, or the frozen-max modulus |cos 2pi p^2|?

Reader (doc 52 §1-3): on sigma=1/2, zeta_N = |F|e^{i phi}(1+e^{iA}),
  A = -2 theta_RS - 2 phi,  A' = -2(theta_RS' + Re(F_N'/F_N)),
births = tangencies A'=0 at odd-pi levels. Define the DEFICIT function
  h(t) = theta_RS'(t) + Re(F_N'/F_N)(1/2+it),   theta_RS'(t) = 1/2 log(t/2pi).
Mean Re(F'/F) = -1/2 log N, theta_RS' = log N  =>  mean h = +1/2 log N > 0.
A tangency (birth) is h touching 0: a DOWNWARD excursion of h to ~0.
Birth-proxy intensity I(p) = frequency / depth of low-h excursions, binned by p.
F_N(1/2+it) = sum_{n<=N} n^{-1/2} e^{-it log n};  F_N' = sum -log n * (that).

Two candidate envelopes (the FORK):
  H_B   : births ~ B(p)^2 = cos^2(pi/8 - 2pi p^2)     [peaks at p=1/4]
  H_frz : births ~ |cos 2pi p^2|^2 = cos^2(2pi p^2)   [peaks at p=0, frozen-max]
census: births ENHANCED near p~0 (42/106 vs 26.5 uniform), SUPPRESSED near p=1/2
(14/106). So the PEAK LOCATION discriminates: p=0 -> H_frz, p=1/4 -> H_B.

PRE-REGISTERED (before running):
  C1 (prior 0.6): I(p) is p-modulated (not flat): enhanced small-p, suppressed p~1/2.
  C2 THE FORK (prior 0.5): the low-h intensity PEAKS at p~0, not p~1/4 -> favors
     H_frz (creation envelope = frozen-max modulus, NO pi/8) over H_B. If it peaks
     at 1/4 -> H_B (creation shares survival's pi/8). Report peak location + which
     of {const, H_B, H_frz} best fits mean-h(p) and low-tail(p).
  C3 (prior 0.5): the DEPTH (min h / low quantile) is deepest at small p and
     shallowest at p~1/2 (the 2.4x cap as a creation-side depth property).
  C4 (prior 0.4): the suppression ratio [near 0]:[near 1/2] ~ 3 (census); H_B
     predicts ~1.7 (under-shoots), H_frz predicts ~? report both.
"""
import numpy as np

TWO_PI = 2*np.pi

def sweep_h(N, P):
    """return arrays p, h for fixed N over P equally-spaced p in [0,1)."""
    p = np.arange(P)/P
    t = TWO_PI*(N+p)**2                      # matched height at offset p
    n = np.arange(1, N+1)
    logn = np.log(n)
    ninvsqrt = n**(-0.5)
    # F, F' via matrix: rows p, cols n
    ph = np.exp(-1j*np.outer(t, logn))       # e^{-it log n}
    term = ph*ninvsqrt                        # n^{-1/2} e^{-it log n}
    F  = term.sum(axis=1)
    Fp = (term*(-logn)).sum(axis=1)          # F'(1/2+it)
    ReFpF = (Fp*np.conj(F)).real/(np.abs(F)**2)
    thetap = 0.5*np.log(t/TWO_PI)            # = log(N+p)
    h = thetap + ReFpF                        # deficit; birth where h ~ 0
    return p, h, thetap

NS = list(range(40, 121))     # matched heights t ~ 1e4 .. 9e4
P = 4000                       # p-resolution
NB = 25                        # p-bins on [0,1/2]

# accumulate h into p-bins (fold p and 1-p together: d = min(p,1-p))
bin_h = [[] for _ in range(NB)]
logN_ref = np.log(np.mean(NS))
for N in NS:
    p, h, thetap = sweep_h(N, P)
    d = np.minimum(p, 1-p)                    # distance to integer, in [0,1/2]
    # normalize h by log N so heights combine
    hn = h/thetap                             # units of theta' ; birth at hn->0, mean ~0.5
    idx = np.minimum((d*2*NB).astype(int), NB-1)
    for b in range(NB):
        bin_h[b].extend(hn[idx==b].tolist())

dcen = (np.arange(NB)+0.5)/(2*NB)             # bin centers in d
meanh = np.array([np.mean(b) for b in bin_h])
minh  = np.array([np.min(b)  for b in bin_h])
q05   = np.array([np.quantile(b,0.05) for b in bin_h])   # low tail
# birth-proxy intensity: fraction with hn below a near-tangency threshold
thr = 0.15
inten = np.array([np.mean(np.array(b) < thr) for b in bin_h])

B2   = np.cos(np.pi/8 - 2*np.pi*dcen**2)**2   # H_B
frz2 = np.cos(2*np.pi*dcen**2)**2             # H_frz

def fit_report(y, name):
    # fit y ~ a + b*model for model in {B2, frz2}; report R^2 and peak loc of y
    out=[]
    for mname, m in [('const',np.ones_like(dcen)),('H_B(pi/8)',B2),('H_frz(0)',frz2)]:
        X = np.vstack([np.ones_like(dcen), m]).T if mname!='const' else np.ones((NB,1))
        coef,_,_,_ = np.linalg.lstsq(X, y, rcond=None)
        pred = X@coef
        ss_res = np.sum((y-pred)**2); ss_tot=np.sum((y-np.mean(y))**2)
        r2 = 1-ss_res/ss_tot if ss_tot>0 else float('nan')
        out.append(f"{mname}:R2={r2:.3f}")
    peak = dcen[np.argmax(y)] if name!='meanh' else dcen[np.argmin(y)]
    print(f"  {name:8s} peak/extremum at d={peak:.3f}  | "+"  ".join(out))

print(f"NS={NS[0]}..{NS[-1]} P={P} bins={NB}  (h normalized by theta'; birth ~ h->0)")
print("d    meanh  q05    min    intensity(h<0.15)   B2     frz2")
for b in range(NB):
    print(f"{dcen[b]:.3f} {meanh[b]:+.3f} {q05[b]:+.3f} {minh[b]:+.3f}   {inten[b]:.4f}"
          f"          {B2[b]:.3f}  {frz2[b]:.3f}")

print("\n--- fits (which envelope; where is the peak?) ---")
fit_report(inten,'intensity')     # birth proxy: peak location is the FORK
fit_report(-q05,  'neg_q05')      # low tail depth (more negative q05 = more birth-prone)
fit_report(meanh, 'meanh')        # mean deficit (minimum = most birth-prone)

# census-style ratio: near d~0 (d in [0,0.125]) vs near d~1/2 ([0.375,0.5])
lo = inten[dcen<0.125].mean(); hi = inten[dcen>0.375].mean()
print(f"\nintensity ratio [d<0.125]:[d>0.375] = {lo/hi:.2f}  (census births 3.0; H_B~1.7)")
print(f"  B2   ratio = {B2[dcen<0.125].mean()/B2[dcen>0.375].mean():.2f}")
print(f"  frz2 ratio = {frz2[dcen<0.125].mean()/frz2[dcen>0.375].mean():.2f}")
