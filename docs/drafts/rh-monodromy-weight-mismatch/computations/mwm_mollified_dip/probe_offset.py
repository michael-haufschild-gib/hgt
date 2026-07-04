#!/usr/bin/env python3
"""Doc 74 probe: offset location + residual R = log|Z| - ReP_m moments,
full vs restricted (dist to nearest zero > 0.1 mean spacing).
Predictions P-OL1..P-OL7 pre-registered in 74-offset-location-and-harvest.md."""
import numpy as np, json, math

def theta(t):
    return t/2*np.log(t/(2*np.pi)) - t/2 - np.pi/8 + 1/(48*t) + 7/(5760*t**3)

def primes_upto(n):
    s = list(range(n+1)); s[0]=s[1]=0
    for i in range(2,int(n**0.5)+1):
        if s[i]:
            for j in range(i*i,n+1,i): s[j]=0
    return [p for p in s if p]

def Zval(t):
    a = np.sqrt(t/(2*np.pi)); m = np.floor(a).astype(np.int64)
    out = np.empty_like(t)
    for mv in np.unique(m):
        idx = m == mv; tt = t[idx]
        n = np.arange(1, mv+1, dtype=np.float64)
        th = theta(tt); res = np.zeros(tt.size)
        B = max(1, int(4e7 // max(1, mv)))
        for i in range(0, tt.size, B):
            sl = slice(i, min(i+B, tt.size))
            ph = th[sl,None] - tt[sl,None]*np.log(n)[None,:]
            res[sl] = 2*np.sum(np.cos(ph)/np.sqrt(n)[None,:], axis=1)
        p = a[idx]-mv
        res += (-1)**(mv+1)*(tt/(2*np.pi))**(-0.25)*np.cos(2*np.pi*(p*p-p-1/16.0))/np.cos(2*np.pi*p)
        out[idx] = res
    return out

def RePm(t, m):
    P = np.array(primes_upto(m), dtype=np.float64)
    out = np.zeros(t.size)
    B = max(1, int(4e7 // max(1, P.size)))
    for i in range(0, t.size, B):
        sl = slice(i, min(i+B, t.size))
        out[sl] = np.sum(np.cos(t[sl,None]*np.log(P)[None,:])/np.sqrt(P)[None,:], axis=1)
    return out

def stats(x, w):
    x = x[w]
    return dict(m1=float(x.mean()), m2=float((x**2).mean()),
                m4=float((x**4).mean()), m6=float((x**6).mean()))

def run(T, U, delta):
    t = np.arange(0.0, U, delta) + T
    Z = Zval(t); absZ = np.abs(Z)
    m = int(math.isqrt(int(T/(2*math.pi))))
    ReP = RePm(t, m)
    v_pm = sum(1/(2.0*p) for p in primes_upto(m))
    # zeros
    sc = np.where(Z[:-1]*Z[1:] < 0)[0]
    gam = t[sc] + np.abs(Z[sc])/(np.abs(Z[sc])+np.abs(Z[sc+1]))*delta
    spacing = U/len(gam)
    gs = np.sort(gam)
    idx = np.searchsorted(gs, t)
    left = np.where(idx > 0, np.abs(t - gs[np.maximum(idx-1,0)]), np.inf)
    right = np.where(idx < gs.size, np.abs(gs[np.minimum(idx,gs.size-1)] - t), np.inf)
    dmin = np.minimum(left, right)
    ok = absZ > 1e-12
    logZ = np.log(np.where(ok, absZ, 1e-12))
    R = logZ - ReP
    full = ok
    restr = ok & (dmin > 0.1*spacing)
    out = dict(T=T, U=U, m=m, n_zeros=len(gam), v_pm=v_pm,
               frac_restricted=float(restr.mean()),
               logZ_full=stats(logZ, full), logZ_restr=stats(logZ, restr),
               R_full=stats(R, full), R_restr=stats(R, restr),
               ReP_var=float(ReP.var()))
    print(json.dumps(out), flush=True)

for (T,U,delta) in [(1e6,3000.0,0.001),(1e7,1500.0,0.001),(1e8,600.0,0.002)]:
    run(T,U,delta)
