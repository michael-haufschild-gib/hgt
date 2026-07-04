#!/usr/bin/env python3
"""Doc 76 probe, zeta side: mid-band valley persistence across truncation levels.

Events: non-crossing valleys of Z_n(t) = 2 sum_{k<=n} k^{-1/2} cos(theta(t) - t log k).
Tracked across levels n in [N-W, N+W] at fixed heights; lifetime, death mode
(absorbed = crossing appears at t_v; vanished = critical point gone), relay
(re-creation at same t within <=3 levels of a death), null-model survival
(added amplitude with uniform phase). Predictions P-X1..P-X5 pre-registered in
76-xld-two-level.md BEFORE this run.
"""
import numpy as np, json, math

W = 40                 # level half-window
MATCH = 0.3            # matching tolerance in spacings
BAND = (0.05, 0.35)    # mid-band eta/spacing at birth
LOOSE = (0.005, 1.5)   # loose detection band for tracking

def theta(t):
    return t/2*np.log(t/(2*np.pi)) - t/2 - np.pi/8 + 1/(48*t) + 7/(5760*t**3)

def valleys(t, Z, dt, spacing):
    """Non-crossing valleys: critical points with Z*Z'' > 0. Vectorized."""
    Zp = (np.roll(Z, -1) - np.roll(Z, 1)) / (2*dt)
    Zpp = (np.roll(Z, -1) - 2*Z + np.roll(Z, 1)) / dt**2
    sgn = np.sign(Zp)
    crit = np.where(sgn[:-1] * sgn[1:] < 0)[0]
    crit = crit[(crit > 5) & (crit < len(t) - 6)]
    keep = Z[crit] * Zpp[crit] > 0
    crit = crit[keep]
    eta = np.sqrt(2*np.abs(Z[crit]) / np.abs(Zpp[crit]))
    band = (eta/spacing >= LOOSE[0]) & (eta/spacing <= LOOSE[1])
    crit, eta = crit[band], eta[band]
    shift = np.clip(-Zp[crit]/Zpp[crit], -dt, dt)
    tv = t[crit] + shift
    order = np.argsort(tv)
    return tv[order], eta[order], Z[crit][order]

def run(T, U, dt):
    N = int(math.isqrt(int(T/(2*math.pi))))
    spacing = 2*np.pi/np.log(T/(2*np.pi))
    tol = MATCH*spacing
    t = np.arange(0.0, U, dt) + T
    th = theta(t)
    n_lo, n_hi = N - W, N + W
    ks = np.arange(1, n_lo + 1, dtype=np.float64)
    Z = np.zeros(t.size)
    B = max(1, int(4e7 // max(1, ks.size)))
    for i in range(0, t.size, B):
        sl = slice(i, min(i+B, t.size))
        Z[sl] = 2*np.sum(np.cos(th[sl,None] - t[sl,None]*np.log(ks)[None,:])
                         / np.sqrt(ks)[None,:], axis=1)
    active, recent_dead, done = [], [], []
    for n in range(n_lo, n_hi + 1):
        if n > n_lo:
            Z += 2*np.cos(th - t*np.log(n)) / math.sqrt(n)
        tv, eta, zm = valleys(t, Z, dt, spacing)
        inw = (tv > T + 2*spacing) & (tv < T + U - 2*spacing)
        tv, eta, zm = tv[inw], eta[inw], zm[inw]
        used = np.zeros(tv.size, dtype=bool)
        if n > n_lo:
            still = []
            for ch in active:
                tv0 = ch['t_hist'][-1]
                j = np.searchsorted(tv, tv0)
                bj = -1
                for jj in (j-1, j):
                    if 0 <= jj < tv.size and not used[jj] and abs(tv[jj]-tv0) < tol:
                        if bj < 0 or abs(tv[jj]-tv0) < abs(tv[bj]-tv0):
                            bj = jj
                if bj >= 0:
                    used[bj] = True
                    ch['t_hist'].append(float(tv[bj]))
                    ch['eta_hist'].append(float(eta[bj]))
                    ch['zmin_hist'].append(float(zm[bj]))
                    still.append(ch)
                else:
                    ch['death_n'] = n
                    ch['relay'] = False
                    i0 = int(round((tv0 - T)/dt))
                    r = max(2, int(tol/dt))
                    seg = Z[max(0, i0-r): i0+r]
                    ch['death_mode'] = ('absorbed' if np.any(np.sign(seg[:-1])
                        * np.sign(seg[1:]) < 0) else 'vanished')
                    recent_dead.append(ch)
            active = still
            keep_rd = []
            for ch in recent_dead:
                if not ch['relay']:
                    tv0 = ch['t_hist'][-1]
                    j = np.searchsorted(tv, tv0)
                    for jj in (j-1, j):
                        if 0 <= jj < tv.size and abs(tv[jj]-tv0) < tol:
                            ch['relay'] = True
                            break
                if n - ch['death_n'] >= 3 or ch['relay']:
                    done.append(ch)
                else:
                    keep_rd.append(ch)
            recent_dead = keep_rd
        for j in range(tv.size):
            if not used[j]:
                active.append(dict(birth_n=n, t_hist=[float(tv[j])],
                                   eta_hist=[float(eta[j])],
                                   zmin_hist=[float(zm[j])], death_n=None,
                                   death_mode=None, relay=None))
    for ch in active:
        ch['censored'] = True
    for ch in recent_dead:
        done.append(ch)
    chains = done + active
    mb = [ch for ch in chains
          if BAND[0] <= ch['eta_hist'][0]/spacing <= BAND[1]
          and ch['birth_n'] > n_lo]
    lifetimes = np.array([len(ch['t_hist']) for ch in mb])
    censored = np.array([ch.get('censored', False) for ch in mb])
    surv1_meas, surv1_null, surv2_given1 = [], [], []
    for ch in mb:
        nb = ch['birth_n']
        a1 = 2/math.sqrt(nb + 1)
        p_cross = math.acos(min(1.0, abs(ch['zmin_hist'][0])/a1))/math.pi
        if nb < n_hi:
            surv1_null.append(1 - p_cross)
            surv1_meas.append(len(ch['t_hist']) >= 2)
            if len(ch['t_hist']) >= 2 and nb + 1 < n_hi:
                surv2_given1.append(len(ch['t_hist']) >= 3)
    covers_matched = sum(1 for ch in mb
                         if ch['birth_n'] <= N < ch['birth_n'] + len(ch['t_hist']))
    relays = [ch for ch in chains if ch['relay'] is not None]
    out = dict(T=T, N=N, U=U, W=W, spacing=spacing,
               n_chains_all=len(chains), n_midband=len(mb),
               life_median=float(np.median(lifetimes)) if len(mb) else None,
               life_p95=float(np.percentile(lifetimes, 95)) if len(mb) else None,
               life_max=int(lifetimes.max()) if len(mb) else None,
               frac_censored=float(censored.mean()) if len(mb) else None,
               clock_3N13=3*N**(1/3),
               surv1_measured=float(np.mean(surv1_meas)) if surv1_meas else None,
               surv1_null=float(np.mean(surv1_null)) if surv1_null else None,
               surv2_given_surv1=(float(np.mean(surv2_given1))
                                  if surv2_given1 else None),
               death_absorbed=sum(1 for ch in mb if ch['death_mode'] == 'absorbed'),
               death_vanished=sum(1 for ch in mb if ch['death_mode'] == 'vanished'),
               relay_rate=(float(np.mean([ch['relay'] for ch in relays]))
                           if relays else None),
               covers_matched=covers_matched)
    print(json.dumps(out), flush=True)
    return out

for (T, U, dt) in [(2.5e4, 4000.0, 0.002), (1e5, 3000.0, 0.002),
                   (1e6, 1500.0, 0.002), (1e7, 600.0, 0.002)]:
    run(T, U, dt)
