from concurrent.futures import ProcessPoolExecutor,as_completed
from pathlib import Path
import json,time
import mpmath as m
import analytic as e

def locate(cell):
 start=time.monotonic();seed=cell['seed'];F,p=e.make(seed,50);lam=m.mpf(seed['lam'])*m.mpf(cell['fraction']);lo=m.mpf(cell['lo']);hi=m.mpf(cell['hi'])
 samples=cell['contours'][-1]['samples'][:cell['contours'][-1]['n']]
 vals=[abs(e.dec(x['f'])) for x in samples];ix=[i for i in range(1,len(vals)-1) if vals[i]<vals[i-1] and vals[i]<vals[i+1]]
 ix=sorted(ix,key=lambda i:vals[i])[:6];found=[];fails=0;dest=[]
 for i in ix:
  for y in ['.3','1']:
   z0=m.mpc(samples[i]['z'][0],y)
   try:
    z=m.findroot(lambda z:F(z,lam),(z0,z0+m.mpf('.01')),tol=m.mpf('1e-38'),maxsteps=20)
    if m.im(z)<0:z=m.conj(z)
    if lo<m.re(z)<hi and m.mpf('.03')<m.im(z)<2 and all(abs(z-e.dec(x['t']))>m.mpf('1e-20') for x in found):
     found.append(dict(t=e.enc(z),residual=str(abs(F(z,lam)))))
    else:dest.append(e.enc(z))
   except Exception:fails+=1
 return dict(seed=seed,fraction=cell['fraction'],lo=str(lo),hi=str(hi),roots=found,failed_seeds=fails,other_destinations=dest,seconds=time.monotonic()-start)

def validate(item):
 seed,fraction,z0=item;start=time.monotonic();out=dict(seed=seed,fraction=fraction,screen_root=z0,precision=[])
 for dps in [100,160]:
  F,p=e.make(seed,dps);lam=m.mpf(seed['lam'])*m.mpf(fraction);z=e.dec(z0)
  z=m.findroot(lambda z:F(z,lam),(z,z+m.mpf('1e-8')),tol=m.mpf(10)**(-dps+10),maxsteps=20)
  out['precision'].append(dict(dps=dps,t=e.enc(z),residual=str(abs(F(z,lam))),shift=str(abs(z-e.dec(z0)))))
 F,p=e.make(seed,190);z=e.dec(out['precision'][-1]['t']);lam=m.mpf(seed['lam'])*m.mpf(fraction)
 a,b=map(m.mpf,seed['direction']);norm=m.sqrt(a*a+b*b);a/=norm;b/=norm;kap=seed['interaction']
 hs=[{int(k):m.mpf(v) for k,v in p[n].items()} for n in ['h1','h2','h12']]
 def source(x):
  y=m.exp(2*x);q=seed['q'];parity=1 if q==4 else 0;chi=[0,1,0,-1] if q==4 else [0,1,-1,-1,1];mu=2*m.exp((parity+m.mpf('.5'))*x)*sum(chi[n%q]*n**parity*m.exp(-m.pi*n*n*y/q) for n in range(1,41) if chi[n%q])
  h=[sum(c*m.cos(k*x) for k,c in hh.items()) for hh in hs]
  return mu*(1+lam*(a*h[0]+b*h[1])+kap*lam*lam*a*b*h[2])
 out['source_checks']=[]
 for off in [0,m.mpf('.01')]:
  t=z+off;expect=F(t,lam);actual=2*m.exp(m.pi*t/4)*m.quad(lambda x:source(x)*m.cos(t*x),[0,.25,.5,.75,1,1.5,2,3,4])
  out['source_checks'].append(dict(offset=str(off),error=str(abs(actual-expect)),actual=e.enc(actual),expected=e.enc(expect)))
 out['positivity_bound']=str(abs(lam)*m.sqrt(2)+kap*lam*lam/2*m.mpf(p['h12_l1']));out['seconds']=time.monotonic()-start;return out
if __name__=='__main__':
 cells=json.loads(Path('cells.json').read_text());rows=[]
 with ProcessPoolExecutor(max_workers=14) as pool,open('located.jsonl','w',buffering=1) as f:
  for fut in as_completed([pool.submit(locate,c) for c in cells]):
   r=fut.result();f.write(json.dumps(r)+'\n');rows.append(r);print('locate',r['seed']['n'],r['fraction'],r['lo'],len(r['roots']),r['seconds'],flush=True)
  selected=[]
  for r in sorted(rows,key=lambda r:(float(r['fraction']),r['seed']['n'],r['seed']['interaction'])):
   for z in sorted(r['roots'],key=lambda z:float(z['t'][0])):
    selected.append((r['seed'],r['fraction'],z['t']))
  with open('validation.jsonl','w',buffering=1) as f:
   for fut in as_completed([pool.submit(validate,x) for x in selected[:2]]):
    r=fut.result();f.write(json.dumps(r)+'\n');print('validated',r['fraction'],r['precision'][-1]['t'],flush=True)
