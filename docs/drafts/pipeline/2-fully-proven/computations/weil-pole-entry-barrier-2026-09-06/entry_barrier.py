"""Exploratory actual-prime entry test. No output is a Lean proof input."""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '1'
os.environ['OMP_NUM_THREADS'] = '1'
import csv, gzip, json, math, time
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor
import numpy as np

N = 2_000_000
WORKERS = min(8, os.cpu_count() or 1)
GAMMA = 0.577215664901532860606512090082402431
KAPPA = -GAMMA - math.log(2*math.pi)
KA = abs(KAPPA)+(2*math.log(2)+math.pi+1)+4+2*(math.log(4)+5)+2*(math.log(4)+4)
R0 = max(2, math.log(KA+17))
MIN_N = math.ceil(math.exp(2*R0))


def evaluate(chunk):
    n, lam, psi, m1, H = chunk.T
    r, e = 1/n, np.sqrt(n)
    em, a = 1/e, np.log(n)/2
    L2, L4 = -np.log1p(-r), -np.log1p(-r*r)
    primitive = (1-r)*np.log1p(-r)-(1+r)*np.log1p(r)+2*r
    F = e/2*(2-2*math.log(2)-primitive)
    G = em*(-math.log(2)-np.log(r)+np.arctanh(r)/r+0.5*np.log1p(-r*r))
    B1, B1p = F+G, F-G+em*L4+2*e*np.arctanh(r)
    # Incoming frozen coefficients: entering atom has zero value, nonzero slope.
    psi_pre, m1_pre = psi-lam, m1-lam/n
    Ap = (KAPPA+3+4*a-2*m1_pre)*e+(KAPPA+2*a-3-2*psi_pre)*em+B1p
    Cp = 2*KAPPA+4*a+2*(n-r)-2*(psi_pre+m1_pre)+2*L2
    v = 2*(Ap+Cp)
    J = 4*lam*(1+em)**2
    A = KAPPA*(e-em)-e+(1-2*a)*em+B1-2*e*(m1-2*a)+2*em*psi
    FA = 8*(e+em)-4*em-4*em*(1+n*n)/(n*n-1)
    FC = 4*(n+r)+4-4/(n-1)
    curvature = 2*(A+FA+FC)
    # B0 = pi^2/6-Li_2(1/n); omitted tail <= r^13/(169*(1-r)).
    li2 = sum(r**k/k**2 for k in range(1,13))
    B0 = math.pi**2/6-li2
    C = KAPPA*(2*a)+2*a*a+(e-em)**2+B0-(2*a*(psi+m1)-H)
    energy = 2*(A+C)
    incoming = energy-v*v/(2*curvature)
    outgoing = energy-(v-J)**2/(2*curvature)
    jump = J*(2*v-J)/(2*curvature)
    return np.column_stack([n,lam,v,J,curvature,energy,incoming,outgoing,jump])


def main():
    start = time.time()
    prime = np.ones(N+1,dtype=bool)
    prime[:2] = False
    for p in range(2,math.isqrt(N)+1):
        if prime[p]:
            prime[p*p::p] = False
    primes = np.flatnonzero(prime)
    weights = np.zeros(N+1)
    for p in primes:
        q, l = int(p), math.log(int(p))
        while q<=N:
            weights[q] = l
            q *= int(p)
    entries = np.flatnonzero(weights)
    l = weights[entries]
    # Prefixes only over actual nonzero prime-power entries.
    psi, m1 = np.cumsum(l), np.cumsum(l/entries)
    H = np.cumsum(l*(1+1/entries)*np.log(entries))
    data = np.column_stack([entries,l,psi,m1,H])
    data = data[entries>=MIN_N]
    with ProcessPoolExecutor(max_workers=WORKERS) as pool:
        rows = np.vstack(list(pool.map(evaluate,np.array_split(data,WORKERS*4))))
    names = ['n','Lambda','incoming_velocity','jump_magnitude','curvature','even_energy',
             'incoming_barrier','outgoing_barrier','barrier_jump']
    with gzip.open('entries.csv.gz','wt',newline='') as f:
        w=csv.writer(f); w.writerow(names); w.writerows(rows)
    negative = rows[rows[:,8]<0]
    picks = np.unique(np.concatenate([negative[:8,0],
        rows[np.argsort(rows[:,8])[:4],0],rows[np.argsort(rows[:,7])[:4],0]])).astype(int)
    with open('selected.csv','w',newline='') as f:
        w=csv.writer(f); w.writerow(names)
        w.writerows(rows[np.isin(rows[:,0],picks)])
    summary = dict(N=N,workers=WORKERS,curvature_threshold=R0,min_n=MIN_N,
        entries_tested=len(rows),negative_barrier_jumps=len(negative),
        first_negative_jump=dict(zip(names,negative[0].tolist())) if len(negative) else None,
        minimum_jump=dict(zip(names,rows[np.argmin(rows[:,8])].tolist())),
        minimum_outgoing_barrier=dict(zip(names,rows[np.argmin(rows[:,7])].tolist())),
        nonpositive_curvature=int(np.sum(rows[:,4]<=0)),
        negative_even_energies=int(np.sum(rows[:,5]<0)),
        negative_outgoing_barriers=int(np.sum(rows[:,7]<0)),seconds=time.time()-start)
    Path('summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2),flush=True)
    # Independent high-precision sums over the original actual prime powers at selected entries.
    import mpmath as mp
    mp.mp.dps=80
    checks=[]
    for n in picks:
        n=int(n); p=next(int(p) for p in primes if n%int(p)==0)
        lm=mp.log(p); nn=mp.mpf(n); aa=mp.log(nn)/2; ee=mp.sqrt(nn); mm=1/ee; rr=1/nn
        pp=mp.mpf('0'); ss=mp.mpf('0'); hh=mp.mpf('0')
        for p0 in primes:
            p0=int(p0)
            if p0>n: break
            q=p0; logp=mp.log(p0)
            while q<=n:
                pp+=logp; ss+=logp/q; hh+=logp*(1+mp.mpf(1)/q)*mp.log(q)
                q*=p0
        kap=-mp.euler-mp.log(2*mp.pi)
        jj=(1-rr)*mp.log1p(-rr)-(1+rr)*mp.log1p(rr)+2*rr
        f=ee/2*(2-2*mp.log(2)-jj)
        g=mm*(-mp.log(2)-mp.log(rr)+mp.atanh(rr)/rr+mp.log1p(-rr*rr)/2)
        bp=f-g-mm*mp.log1p(-rr*rr)+2*ee*mp.atanh(rr)
        ap=(kap+3+4*aa-2*(ss-lm/nn))*ee+(kap+2*aa-3-2*(pp-lm))*mm+bp
        cp=2*kap+4*aa+2*(nn-rr)-2*(pp-lm+ss-lm/nn)-2*mp.log1p(-rr)
        vel=2*(ap+cp); jump=4*lm*(1+mm)**2
        diag=kap*(ee-mm)-ee+(1-2*aa)*mm+f+g-2*ee*(ss-2*aa)+2*mm*pp
        force=2*(diag+8*(ee+mm)-4*mm-4*mm*(1+nn*nn)/(nn*nn-1)+4*(nn+rr)+4-4/(nn-1))
        cross=kap*2*aa+2*aa*aa+(ee-mm)**2+mp.pi**2/6-mp.polylog(2,rr)-(2*aa*(pp+ss)-hh)
        en=2*(diag+cross)
        record=dict(n=n,incoming_velocity=mp.nstr(vel,65),jump_magnitude=mp.nstr(jump,65),
            barrier_jump=mp.nstr(jump*(2*vel-jump)/(2*force),65),
            even_energy=mp.nstr(en,65),outgoing_barrier=mp.nstr(en-(vel-jump)**2/(2*force),65))
        checks.append(record)
        print('confirmed',n,record['barrier_jump'],flush=True)
    Path('high_precision.json').write_text(json.dumps(checks,indent=2)+'\n')
    # Independent quadrature check of boundary primitive formulas at two sampled apertures.
    boundary=[]
    for n in [MIN_N,int(picks[0])]:
        aa=mp.log(n)/2; rr=mp.mpf(1)/n
        Fq=mp.exp(aa)/2*mp.quad(lambda t:mp.exp(-t)*(-mp.log(-mp.expm1(-2*t))),[0,aa,2*aa])
        Gq=mp.exp(-aa)*mp.quad(lambda t:mp.exp(t)*mp.atanh(mp.exp(-t)),[0,aa,2*aa])
        jj=(1-rr)*mp.log1p(-rr)-(1+rr)*mp.log1p(rr)+2*rr
        Fc=mp.exp(aa)/2*(2-2*mp.log(2)-jj)
        Gc=mp.exp(-aa)*(-mp.log(2)-mp.log(rr)+mp.atanh(rr)/rr+mp.log1p(-rr*rr)/2)
        boundary.append(dict(n=n,F_difference=mp.nstr(Fq-Fc,20),G_difference=mp.nstr(Gq-Gc,20)))
    Path('boundary_checks.json').write_text(json.dumps(boundary,indent=2)+'\n')
    print('done',time.time()-start,flush=True)

if __name__=='__main__': main()
