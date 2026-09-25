"""High precision guidance for the minimax and potential-theory leads. Runpod only."""
import os
for name in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[name]='1'
import json
from concurrent.futures import ProcessPoolExecutor
import mpmath as mp


def refine(item):
    mp.mp.dps=70
    m=item['m']
    def basis(t):
        ts=[mp.mpf(1),t]
        for j in range(2,m+1): ts.append(2*t*ts[-1]-ts[-2])
        ds=[mp.mpf(0),mp.mpf(1)]
        for j in range(2,m+1): ds.append(2*ts[j-1]+2*t*ds[-1]-ds[-2])
        return ts[:m+1],ds[:m+1]
    def values(c,aa):
        ts,ds=basis(2*c*(2-c)-1)
        p=sum(a*t for a,t in zip(aa,ts))
        d=sum(a*t for a,t in zip(aa,ds))
        return c**m*p, m*c**(m-1)*p+c**m*(4-4*c)*d
    def equations(*z):
        aa=list(z[:m])+[mp.mpf(1)]
        tau=z[m]; nodes=list(z[m+1:])+[mp.mpf(1)]
        vals=[values(c,aa) for c in nodes]
        return tuple([v[0]-(-1)**(m-i)*tau for i,v in enumerate(vals)]+[v[1] for v in vals[:-1]])
    seed=[mp.mpf(str(v)) for v in item['a'][:-1]+[item['dense_norm']]+item['contacts']]
    z=mp.findroot(equations,tuple(seed),tol=mp.mpf('1e-60'),maxsteps=50)
    aa=list(z[:m])+[mp.mpf(1)]
    penult=aa[0]-aa[1] if m==1 else 2**(2*m-3)*aa[m-1]-m*2**(2*m-2)
    delta=z[m]/(4**(m-1)*abs(penult))
    return {'m':m,'delta':str(delta),'norm':str(z[m]),'a':[str(v) for v in aa],
            'contacts':[str(v) for v in z[m+1:]],
            'equation_residual':str(max(abs(v) for v in equations(*z)))}


if __name__=='__main__':
    with open('minimax-results.json') as f: data=json.load(f)
    with ProcessPoolExecutor(max_workers=24) as pool: results=list(pool.map(refine,data['best']))
    mp.mp.dps=70
    theta=mp.findroot(lambda t:2*(mp.pi-t)-3*mp.pi*mp.sin(t),(.5,.7))
    b=mp.cos(theta)
    integral=mp.quad(lambda t:mp.log(1-b*mp.cos(t)),[0,mp.pi/2])
    rho=b*b/16*mp.exp(2*integral/mp.pi)
    gaps=[mp.mpf(r['delta']) for r in results]
    ratios=[gaps[i+1]/gaps[i] for i in range(len(gaps)-1)]
    scaled=[(g/gaps[0])**2/rho**(2*i) for i,g in enumerate(gaps)]
    hankel={}
    for shift in (0,1):
        for size in (2,3,4):
            h=mp.matrix([[scaled[i+j+shift] for j in range(size)] for i in range(size)])
            hankel[f'{shift}:{size}']=str(mp.det(h))
    out={'results':results,'theta':str(theta),'support_b':str(b),'physical_contact_limit':str(1-b),
         'rho':str(rho),'rho_squared':str(rho*rho),'ratios':[str(v) for v in ratios],
         'scaled_hankel_determinants':hankel,
         'scaled_gaps': [str((i+1)*g/rho**(i+1)) for i,g in enumerate(gaps)]}
    with open('refined-results.json','w') as f:json.dump(out,f,indent=2)
    print(json.dumps({k:v for k,v in out.items() if k!='results'},indent=2))
