from concurrent.futures import ProcessPoolExecutor,as_completed
from pathlib import Path
import json,time
import mpmath as m
import experiment as e

def check(job):
 row,cut=job;start=time.monotonic();seed=row['seed'];F,p=e.make(seed,190);z=e.dec(row['t']);lam=m.mpf(seed['lam'])*m.mpf(row['ratio'])
 hs=[{int(k):m.mpf(v) for k,v in p[n].items()} for n in ['h1','h2','h12']]
 a,b=map(m.mpf,seed['direction']);norm=m.sqrt(a*a+b*b);a/=norm;b/=norm;kap=seed['interaction']
 def source(x):
  y=m.exp(2*x);mu=m.exp(x/2)*sum(2*m.pi*(2*m.pi*n**4*y*y-3*n*n*y)*m.exp(-m.pi*n*n*y) for n in range(1,17))
  h=[sum(c*m.cos(k*x) for k,c in hh.items()) for hh in hs]
  return mu*(1+lam*(a*h[0]+b*h[1])+kap*lam*lam*a*b*h[2])
 out=dict(seed=seed,ratio=row['ratio'],t=row['t'],cutoff=cut,dps=190,checks=[])
 for off in [0,m.mpf('.01')]:
  t=z+off;expected=F(t,lam);actual=2*m.exp(m.pi*t/4)*m.quad(lambda x:source(x)*m.cos(t*x),[0,.25,.5,.75,1,1.5,2,3,m.mpf(cut)])
  out['checks'].append(dict(offset=str(off),error=m.nstr(abs(actual-expected),90),actual=e.enc(actual),expected=e.enc(expected)))
 out['seconds']=time.monotonic()-start;return out
if __name__=='__main__':
 jobs=[(r,c) for r in json.loads(Path('points.json').read_text()) for c in ['3.5','4']]
 with ProcessPoolExecutor(max_workers=14) as pool,open('source-validation.jsonl','w',buffering=1) as f:
  for fut in as_completed([pool.submit(check,j) for j in jobs]):
   r=fut.result();f.write(json.dumps(r)+'\n');print(r['seed']['n'],r['cutoff'],r['seconds'],flush=True)
