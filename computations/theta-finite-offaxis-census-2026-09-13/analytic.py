import json,os,time,math
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed
import mpmath as m
PARAM=json.loads(Path('parameters.json').read_text())
SEEDS=json.loads(Path('seeds.json').read_text())
MODE=Path('mode.txt').read_text().strip()
DEAD=float(os.environ.get('CAMPAIGN_DEADLINE',time.monotonic()+575))
def enc(z):return [m.nstr(m.re(z),m.mp.dps),m.nstr(m.im(z),m.mp.dps)]
def dec(z):return m.mpc(*z)
def carrier(t,q):
 s=m.mpf('.5')+1j*t
 if q==0:return s*(s-1)/2*m.exp(-s*m.log(m.pi)/2+m.loggamma(s/2))*m.zeta(s)
 a=1 if q==4 else 0;chi=[0,1,0,-1] if q==4 else [0,1,-1,-1,1]
 return m.exp((s+a)*m.log(q/m.pi)/2+m.loggamma((s+a)/2)-s*m.log(q))*sum(chi[r]*m.zeta(s,m.mpf(r)/q) for r in range(1,q) if chi[r])
def make(seed,dps):
 m.mp.dps=dps;q=seed.get('q',0);prec='70' if dps==50 else ('120' if dps==100 else '180')
 p=PARAM[str(q)][prec] if q else PARAM[prec]
 h=[{int(k):m.mpf(v) for k,v in p[n].items()} for n in ['h1','h2','h12']]
 a,b=map(m.mpf,seed['direction']);norm=m.sqrt(a*a+b*b);a/=norm;b/=norm;kappa=seed['interaction']
 def F(t,lam):
  if time.monotonic()>DEAD-6:raise TimeoutError('cooperative family deadline')
  if not (-3<m.re(t)<180 and abs(m.im(t))<12):raise ValueError('left finite tracking domain')
  weights={0:m.mpf(1)}
  for hh,coef in zip(h,[lam*a,lam*b,kappa*lam*lam*a*b]):
   if not coef:continue
   for k,c in hh.items():
    for kk in [k,-k]:weights[kk]=weights.get(kk,0)+coef*c/2
  return m.exp(m.pi*t/4)*sum(c*carrier(t+k,q) for k,c in weights.items() if c)
 return F,p

def track(job):
 seed,sign,way=job;start=time.monotonic();F,p=make(seed,50);lc=m.mpf(seed['lam']);tc=m.mpf(seed['t'])
 key='%s_%s_%s_%s_%s_%s'%(seed.get('q',0),seed['n'],''.join(map(str,seed['direction'])),seed['interaction'],sign,way)
 row=dict(key=key,seed=seed,sign=sign,way=way,dps=50,points=[])
 try:
  fl=m.diff(lambda l:F(tc,l),lc);ftt=m.diff(lambda t:F(t,lc),tc,2)
  ratio=m.mpf('.999') if way=='back' else m.mpf('1.001')
  target=m.mpf(0) if way=='back' else m.mpf('1.25');direction=-1 if way=='back' else 1
  z=tc+sign*m.sqrt(-2*(ratio-1)*lc*fl/ftt)
  z=m.findroot(lambda t:F(t,ratio*lc),(z,z+m.mpf('1e-4')),tol=m.mpf('1e-40'),maxsteps=20)
  step=m.mpf('.02');previous=None
  for attempt in range(180):
   row['points'].append(dict(ratio=str(ratio),t=enc(z),residual=m.nstr(abs(F(z,ratio*lc)),15)))
   Path('partial-'+key+'.json').write_text(json.dumps(row))
   if ratio==target:row['complete']=True;break
   nxt=max(target,ratio-step) if direction<0 else min(target,ratio+step)
   predictor=z if previous is None else z+(z-previous[1])*(nxt-ratio)/(ratio-previous[0])
   try:
    zn=m.findroot(lambda t:F(t,nxt*lc),(predictor,predictor+m.mpf('1e-5')),tol=m.mpf('1e-40'),maxsteps=15)
    if abs(zn-predictor)>m.mpf('.35') or abs(zn-z)>m.mpf('.6'):raise ValueError('jump threshold')
   except (ValueError,ZeroDivisionError):
    step/=2
    if step<m.mpf('1e-5'):raise ValueError('minimum continuation step; ancestry inconclusive')
    continue
   previous=(ratio,z);ratio,z=nxt,zn;step=min(m.mpf('.05'),step*m.mpf('1.25'))
  row['endpoint']=enc(z);row['final_ratio']=str(ratio)
 except Exception as e:row['error']=str(e)[:200]
 row['seconds']=time.monotonic()-start
 return row

def validate(job):
 seed,point,dps=job;start=time.monotonic();F,p=make(seed,dps);lam=m.mpf(seed['lam'])*m.mpf(point['ratio']);z0=dec(point['t'])
 out=dict(seed=seed,ratio=point['ratio'],dps=dps)
 try:
  z=m.findroot(lambda t:F(t,lam),(z0,z0+m.mpf('1e-8')),tol=m.mpf(10)**(-dps+10),maxsteps=15)
  out.update(t=enc(z),shift=m.nstr(abs(z-z0),dps),residual=m.nstr(abs(F(z,lam)),dps),probe=enc(F(z+m.mpf('.01'),lam)))
 except Exception as e:out['error']=str(e)[:180]
 out['seconds']=time.monotonic()-start;return out
if __name__=='__main__':
 start=time.monotonic();jobs=[(s,sg,w) for s in SEEDS for w in ['back','forward'] for sg in [-1,1]]
 rows=[]
 with ProcessPoolExecutor(max_workers=14) as pool,open('tracks.jsonl','w',buffering=1) as f:
  pending={pool.submit(track,j):j for j in jobs}
  for fut in as_completed(pending):
   r=fut.result();rows.append(r);f.write(json.dumps(r)+'\n');print(r['key'],r.get('complete'),r.get('error'),r['seconds'],flush=True)
   if time.monotonic()>DEAD-140:break
  for fut in pending:fut.cancel()
  validation=[]
  for r in rows:
   if r.get('complete') and r['sign']==1:
    # Fixed interior point for ancestry, final off-axis point for forward branch.
    point=min(r['points'],key=lambda p:abs(float(p['ratio'])-(.5 if r['way']=='back' else 1.25)))
    validation += [(r['seed'],point,dps) for dps in [100,160]]
  with open('validation.jsonl','w',buffering=1) as f:
   for fut in as_completed([pool.submit(validate,j) for j in validation]):
    r=fut.result();f.write(json.dumps(r)+'\n');print('validation',r['seed'].get('q',0),r['dps'],r.get('error'),flush=True)
 Path('summary.json').write_text(json.dumps(dict(seconds=time.monotonic()-start,tracks=len(rows),complete=sum(bool(r.get('complete')) for r in rows)),indent=2))
