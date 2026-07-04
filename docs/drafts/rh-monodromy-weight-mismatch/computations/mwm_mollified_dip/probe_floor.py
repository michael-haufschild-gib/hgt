#!/usr/bin/env python3
"""Doc 72 probe: zero-dip floor of |zeta(1/2+it)| via Z(t) (RS + C0).
Pre-registered predictions P-F1..P-F5 in 72-effm14-attack.md BEFORE this run.
Outputs JSON."""
import numpy as np, json, sys, math

def theta(t):
    return t/2*np.log(t/(2*np.pi)) - t/2 - np.pi/8 + 1/(48*t) + 7/(5760*t**3)

def Zval(t):
    """RS main sum + C0 correction, vectorized over t (1d array)."""
    a = np.sqrt(t/(2*np.pi))
    m = np.floor(a).astype(np.int64)
    out = np.empty_like(t)
    for mv in np.unique(m):
        idx = m == mv
        tt = t[idx]
        n = np.arange(1, mv+1, dtype=np.float64)
        th = theta(tt)
        # chunk over tt to bound memory
        res = np.zeros(tt.size)
        B = max(1, int(4e7 // max(1, mv)))
        for i in range(0, tt.size, B):
            sl = slice(i, min(i+B, tt.size))
            ph = th[sl, None] - tt[sl, None]*np.log(n)[None, :]
            res[sl] = 2*np.sum(np.cos(ph)/np.sqrt(n)[None, :], axis=1)
        p = a[idx] - mv
        C0 = np.cos(2*np.pi*(p*p - p - 1/16.0))/np.cos(2*np.pi*p)
        res += (-1)**(mv+1) * (tt/(2*np.pi))**(-0.25) * C0
        out[idx] = res
    return out

def logpow_int(c, L, kmax=6):
    """int_0^L (log(c x))^k dx for k=0..kmax (c>0, L>0), closed form."""
    lcL = math.log(c*L)
    vals = []
    for k in range(kmax+1):
        s = 0.0
        fk = math.factorial(k)
        for j in range(k+1):
            s += fk/math.factorial(j) * ((-1)**(k-j)) * lcL**j
        vals.append(L*s)
    return vals  # vals[k]

def analyze(T, U, delta, hacc):
    t = np.arange(0.0, U, delta) + T
    Z = Zval(t)
    absZ = np.abs(Z)
    # zeros + slopes
    sc = np.where(Z[:-1]*Z[1:] < 0)[0]
    frac = np.abs(Z[sc])/(np.abs(Z[sc])+np.abs(Z[sc+1]))
    gammas = t[sc] + frac*delta
    slopes = np.abs(Z[sc+1]-Z[sc])/delta
    harmonic = float(np.sum(2.0/slopes)/U)
    nz = len(gammas)
    # measure(lambda) piecewise-linear exact
    lams = np.array([1e-3, 2e-3, 5e-3, 1e-2, 2e-2, 5e-2, 0.1, 0.2, 0.35, 0.5, 0.7])
    a = absZ[:-1]; b = absZ[1:]
    cross = Z[:-1]*Z[1:] < 0
    lo = np.minimum(a, b); hi = np.maximum(a, b)
    meas = []
    for lam in lams:
        # non-crossing: linear |Z| lo->hi
        with np.errstate(divide='ignore', invalid='ignore'):
            m_nc = np.clip((lam-lo)/np.where(hi > lo, hi-lo, np.inf), 0, 1)
        m_nc = np.where(lo >= lam, 0.0, np.where(hi <= lam, 1.0, m_nc))
        # crossing: V down a->0 over f, up 0->b over 1-f
        f = a/(a+b)
        m_c = f*np.minimum(1, lam/np.where(a > 0, a, np.inf)) + \
              (1-f)*np.minimum(1, lam/np.where(b > 0, b, np.inf))
        m = np.where(cross, m_c, m_nc)*delta
        meas.append(float(np.sum(m)))
    # component widths at each lambda (grid-level runs)
    thick_frac = []; zero_comp_frac = []
    for lam in lams:
        mask = absZ < lam
        # runs
        d = np.diff(mask.astype(np.int8))
        starts = np.where(d == 1)[0]+1; ends = np.where(d == -1)[0]+1
        if mask[0]: starts = np.r_[0, starts]
        if mask[-1]: ends = np.r_[ends, mask.size]
        widths = (ends-starts)*delta
        tot = widths.sum()
        if tot == 0:
            thick_frac.append(None); zero_comp_frac.append(None); continue
        thick = widths[widths >= hacc/2].sum()
        # components containing a zero
        zc = 0.0
        gi = np.searchsorted(t, gammas)
        gset = np.sort(gi)
        for s0, e0, w in zip(starts, ends, widths):
            k = np.searchsorted(gset, s0)
            if k < gset.size and gset[k] < e0: zc += w
        thick_frac.append(float(thick/tot)); zero_comp_frac.append(float(zc/tot))
    # moments of log|Z| (raw 1..6), spike-aware
    logs = np.log(np.where(absZ > 1e-300, absZ, 1e-300))
    Mk = np.zeros(7)
    # trapezoid on intervals with lo>0.05 and no crossing; closed-form otherwise
    safe = (~cross) & (lo > 0.05)
    mid = 0.5*(logs[:-1]+logs[1:])
    for k in range(1, 7):
        Mk[k] += np.sum(np.where(safe, mid**k, 0.0))*delta
    # singular intervals: linear model on each side of min/crossing
    idxs = np.where(~safe)[0]
    for i in idxs:
        aa, bb = a[i], b[i]
        if cross[i]:
            fl = aa/(aa+bb); L1 = fl*delta; L2 = (1-fl)*delta
            for (Aend, L) in ((aa, L1), (bb, L2)):
                if L <= 0 or Aend <= 0: continue
                v = logpow_int(Aend/L, L)  # |Z| = (A/L)*x
                for k in range(1, 7): Mk[k] += v[k]
        else:
            # no crossing but small values: treat |Z| linear lo->hi
            if hi[i] <= 0: continue
            if hi[i] == lo[i] or lo[i] <= 0:
                # degenerate: linear from ~0: same closed form
                v = logpow_int(max(hi[i], 1e-12)/delta, delta)
                for k in range(1, 7): Mk[k] += v[k]
            else:
                c = (hi[i]-lo[i])/delta
                vhi = logpow_int(c, hi[i]/c); vlo = logpow_int(c, lo[i]/c)
                for k in range(1, 7): Mk[k] += (vhi[k]-vlo[k])
    Mk /= U
    mean = Mk[1]
    # central moments via binomial
    def central(kk):
        s = 0.0
        for j in range(kk+1):
            s += math.comb(kk, j)*Mk[j]*((-mean)**(kk-j))
        return s
    mu2 = central(2); mu4 = central(4); mu6 = central(6)
    sigma2_theory = 0.5*math.log(math.log(T))
    return dict(T=T, U=U, delta=delta, hacc=hacc, n_zeros=nz,
                zero_density=nz/U, harmonic_cfl=harmonic,
                lams=lams.tolist(), meas_frac=[m/U for m in meas],
                cfl_at_lam=[m/U/l for m, l in zip(meas, lams)],
                thick_frac=thick_frac, zero_comp_frac=zero_comp_frac,
                mean_logZ=mean, mu2=mu2, mu4=mu4, mu6=mu6,
                mu2_over_theory=mu2/sigma2_theory,
                mu4_ratio=mu4/(3*mu2**2), mu6_ratio=mu6/(15*mu2**3),
                sigma2_theory=sigma2_theory)

def main():
    out = []
    for (T, U, delta) in [(1e6, 3000.0, 0.001), (1e7, 1500.0, 0.001),
                          (1e8, 600.0, 0.002)]:
        hacc = 0.25/math.log(math.sqrt(T/(2*math.pi)))
        r = analyze(T, U, delta, hacc)
        out.append(r)
        print(json.dumps(r), flush=True)
    # validation vs mpmath at T=1e6
    try:
        import mpmath
        mpmath.mp.dps = 25
        ts = [1e6+7.3, 1e6+123.456, 1e6+999.99, 1e6+2500.1, 1e6+2999.5]
        errs = []
        for tv in ts:
            zm = float(mpmath.siegelz(tv))
            zn = float(Zval(np.array([tv]))[0])
            errs.append(abs(zm-zn))
        print(json.dumps({"validation_maxerr": max(errs)}), flush=True)
    except Exception as e:
        print(json.dumps({"validation": "failed: "+str(e)}), flush=True)

if __name__ == "__main__":
    main()
