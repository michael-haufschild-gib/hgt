#!/usr/bin/env python3
"""Depth-graded off-line census: do birth DEPTHS of the completed partial sum
Phi_N track |cos 2pi p^2| (frozen-max, peak p=0, NO pi/8) or B(p)=|cos(pi/8-2pi p^2)|
(peak p=1/4)?  Resolves where the metaplectic pi/8 lives (doc 52 §9 follow-up).

Object: xi_N(s) = pi^{-s/2} Gamma(s/2) sum_{n<=N} n^{-s};  Phi_N = xi_N(s)+xi_N(1-s),
real on sigma=1/2:  g(t) = Re[xi_N(1/2+it)] (drop factor 2). An off-line pair at
1/2 +- eta + i t0 shows on the line as a NON-CROSSING valley of g (two on-line
zeros 'missing'), with, by analyticity (isotropic |Phi| near the pair),
    g(1/2+it) ~ a (t-t0)^2 + c,  eta = sqrt(c/a)   [same units as census eta].

Detection: local minima of |g| that do NOT cross zero AND sit at an anomalously
large on-line-zero gap (missed pair); depth from a local parabola fit. Record
(p, eta), p = sqrt(t0/2pi)-N in [0,1/2). Aggregate over a matched N-band.

loggamma via Stirling (arg = 1/4 + i t/2, |Im| ~ pi N^2 huge -> exact); validated
against mpmath inline.

PRE-REGISTERED (before running):
  D1 (prior 0.6): pair eta in [0.02,0.3], median ~0.1 (census 0.09-0.18).
  D2 THE FORK (prior 0.5): high-quantile / max eta(p) PEAKS at p~0 -> tracks
     |cos 2pi p^2| (frozen-max, NO pi/8), not p~1/4 (B, pi/8). Report peak loc +
     fits eta ~ {const, |cos2pi p^2|, B(p)} (DEPTH is linear in modulus).
  D3 (prior 0.55): eta suppressed as p->1/2; ratio eta(p~0)/eta(p~1/2). frozen-max
     predicts eta(1/2)->0; B predicts 0.383/0.924=0.41. Report which.
  D4 (prior 0.4): pair COUNT per p-bin flat (matching §9 reader) or modulated by
     the depth threshold (deep pairs rarer at large p)?
"""
import numpy as np
import mpmath as mp

TWO_PI = 2*np.pi
LOG2PI = np.log(TWO_PI)

def stirling_loggamma(z):
    # z complex array, |z| large. Stirling series.
    z2 = z*z
    s = (z-0.5)*np.log(z) - z + 0.5*LOG2PI
    s += 1.0/(12*z)
    s += -1.0/(360*z*z2)
    s += 1.0/(1260*z*z2*z2)
    return s

# validate vs mpmath
zt = 0.25+5500j
err = abs(complex(stirling_loggamma(np.array([zt]))[0]) - complex(mp.loggamma(zt)))
print(f"loggamma Stirling check at {zt}: err={err:.2e}")

def theta_rs(t):
    # Riemann-Siegel theta = Im loggamma(1/4 + it/2) - (t/2) log pi
    return np.imag(stirling_loggamma(0.25 + 0.5j*t)) - 0.5*t*np.log(np.pi)

def g_on_line(N, t):
    # Hardy Z of the FE-symmetrized truncation (prefactor divided out; no underflow):
    # Z_N(t) = 2 Re[e^{i theta} sum_{n<=N} n^{-1/2-it}]; real, zeros = on-line zeros,
    # off-line pairs = non-crossing valleys. Same pair structure as Phi_N.
    n = np.arange(1, N+1)
    logn = np.log(n)
    F = ((n**(-0.5))[None,:]*np.exp(-1j*np.outer(t, logn))).sum(axis=1)
    th = theta_rs(t)
    return 2*(np.cos(th)*F.real - np.sin(th)*F.imag)

def census_pairs(N, dt=0.02, gapfac=1.4, W=6):
    t0v = TWO_PI*N*N
    t1v = TWO_PI*(N+0.5)**2
    t = np.arange(t0v, t1v, dt)
    g = g_on_line(N, t)
    ag = np.abs(g)
    # on-line zeros: sign changes
    sc = np.where(g[:-1]*g[1:] < 0)[0]
    zt_ = t[sc]  # approx zero times
    if len(zt_) < 4: return []
    gaps = np.diff(zt_)
    medgap = np.median(gaps)
    # local minima of |g|
    loc = np.where((ag[1:-1] < ag[:-2]) & (ag[1:-1] < ag[2:]))[0] + 1
    out = []
    for i in loc:
        if i < W or i > len(t)-W-1: continue
        # non-crossing? g same sign across the window
        seg = g[i-W:i+W+1]
        if np.any(seg[:-1]*seg[1:] < 0):  # crosses zero nearby -> on-line
            continue
        # missed-zero: nearest on-line zeros straddle a big gap
        left = zt_[zt_ < t[i]]; right = zt_[zt_ > t[i]]
        if len(left)==0 or len(right)==0: continue
        localgap = right[0]-left[-1]
        if localgap < gapfac*medgap:   # not a missed pair
            continue
        # parabola fit g = a(t-t0)^2 + c on window
        tt = t[i-W:i+W+1]-t[i]
        A = np.vstack([tt*tt, tt, np.ones_like(tt)]).T
        coef,_,_,_ = np.linalg.lstsq(A, seg, rcond=None)
        a,b,c = coef
        t0 = t[i] - b/(2*a)
        gmin = c - b*b/(4*a)
        if a==0 or gmin/a <= 0: continue    # need same sign (valley)
        eta = np.sqrt(gmin/a)
        p = np.sqrt(t0/TWO_PI) - N
        if 0 <= p < 0.5 and eta < 1.0:
            out.append((float(p), float(eta)))
    return out

NS = list(range(45, 96))
allpairs = []
for N in NS:
    allpairs.extend(census_pairs(N))
print(f"N band {NS[0]}..{NS[-1]}: {len(allpairs)} off-line pair candidates")
if not allpairs:
    print("NO pairs found"); raise SystemExit
ps = np.array([q[0] for q in allpairs]); etas = np.array([q[1] for q in allpairs])
print(f"eta: median={np.median(etas):.3f} mean={np.mean(etas):.3f} "
      f"5-95pct=[{np.quantile(etas,0.05):.3f},{np.quantile(etas,0.95):.3f}]  (census 0.09-0.18)")

NB = 10
edges = np.linspace(0, 0.5, NB+1); cen = 0.5*(edges[:-1]+edges[1:])
frz = np.abs(np.cos(2*np.pi*cen**2))              # frozen-max modulus (peak p=0)
Bp  = np.abs(np.cos(np.pi/8 - 2*np.pi*cen**2))     # B(p) (peak p=1/4)
print("\n d-bin   count  mean_eta  90pct_eta  max_eta   |cos2pip^2|  B(p)")
meaneta=np.full(NB,np.nan); q90=np.full(NB,np.nan); mx=np.full(NB,np.nan); cnt=np.zeros(NB)
for b in range(NB):
    m = (ps>=edges[b])&(ps<edges[b+1])
    cnt[b]=m.sum()
    if m.sum()>0:
        meaneta[b]=etas[m].mean(); q90[b]=np.quantile(etas[m],0.9); mx[b]=etas[m].max()
    print(f" {cen[b]:.3f}   {int(cnt[b]):4d}   "
          f"{meaneta[b]:.3f}     {q90[b]:.3f}      {mx[b]:.3f}     {frz[b]:.3f}      {Bp[b]:.3f}")

def fit(y, lab):
    ok = ~np.isnan(y)
    if ok.sum()<4: print(f"  {lab}: too few bins"); return
    yy=y[ok]
    res=[]
    for nm,mod in [('const',np.ones(ok.sum())),('frzmax|cos2pip^2|',frz[ok]),('B(pi/8)',Bp[ok])]:
        X=np.vstack([np.ones(ok.sum()),mod]).T if nm!='const' else np.ones((ok.sum(),1))
        cf,_,_,_=np.linalg.lstsq(X,yy,rcond=None); pr=X@cf
        r2=1-np.sum((yy-pr)**2)/np.sum((yy-yy.mean())**2) if np.sum((yy-yy.mean())**2)>0 else float('nan')
        res.append(f"{nm}:R2={r2:.3f}")
    peak=cen[ok][np.argmax(yy)]
    print(f"  {lab:9s} peak at d={peak:.3f} | "+"  ".join(res))

print("\n--- fits (DEPTH linear in modulus; peak p=0 -> frozen-max/no-pi/8, p=1/4 -> B) ---")
fit(meaneta,'mean_eta'); fit(q90,'q90_eta'); fit(mx,'max_eta')

# D3 suppression ratio + D4 count profile
lo = np.nanmean(meaneta[cen<0.15]); hi = np.nanmean(meaneta[cen>0.35])
print(f"\nD3 depth ratio eta[d<0.15]/eta[d>0.35] = {lo/hi:.2f} "
      f"(frzmax: {frz[cen<0.15].mean()/frz[cen>0.35].mean():.2f}, B: {Bp[cen<0.15].mean()/Bp[cen>0.35].mean():.2f})")
cr = cnt[cen<0.15].mean()/max(cnt[cen>0.35].mean(),1e-9)
print(f"D4 count ratio [d<0.15]/[d>0.35] = {cr:.2f} (flat=1; census births 3.0)")
