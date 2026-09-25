import json,time,os
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed
import mpmath as m
import deformation as d
import control as c
import collision as k
P=json.loads(Path('parameters.json').read_text())
POINTS=json.loads(Path('points.json').read_text())
DEAD=float(os.environ.get('CAMPAIGN_DEADLINE',time.monotonic()+575))
ORIGINAL=d.xi_jets

def solve(job):
 point,kap,dps=job;start=time.monotonic();m.mp.dps=dps;seed=point['seed'];q=seed.get('q',0)
 c.CURRENT_Q=q;d.xi_jets=c.carrier_jets if q else ORIGINAL
 prec='70' if dps==50 else ('120' if dps==100 else '180');params=P[str(q)][prec] if q else P[prec]
 fun=k.setup(seed['direction'],params);t0=m.mpf(point['precision'][-1]['t'][0]);l0=m.mpf(seed['lam'])*m.mpf(point['fraction'])*m.mpf('.95')
 def checked(t,l):
  if time.monotonic()>DEAD-5:raise TimeoutError('whole-family deadline')
  return fun(t,l,m.mpf(kap))
 out=dict(seed=seed,reference_t=point['precision'][-1]['t'],reference_fraction=point['fraction'],kappa=kap,dps=dps)
 try:
  t,l=m.findroot(lambda t,l:tuple(checked(t,l)[0][:2]),(t0,l0),J=lambda t,l:checked(t,l)[1],tol=m.mpf(10)**(-dps+12),maxsteps=20)
  F,J,Fk,bound=checked(t,l)
  out.update(t=m.nstr(t,dps),lam=m.nstr(l,dps),residual=m.nstr(max(abs(z) for z in F[:2]),dps),Ftt=m.nstr(F[2],dps),positive_bound=m.nstr(bound,dps),admitted=bool(l>0 and bound<1 and abs(t-t0)<4),reference_lambda_ratio=m.nstr(l/m.mpf(seed['lam']),30))
 except Exception as e:out['error']=str(e)[:180]
 out['seconds']=time.monotonic()-start;return out

def source(row):
 start=time.monotonic();m.mp.dps=190;seed=row['seed'];q=seed.get('q',0);params=P[str(q)]['180'] if q else P['180'];hs=[{int(j):m.mpf(v) for j,v in params[n].items()} for n in ['h1','h2','h12']]
 c.CURRENT_Q=q;d.xi_jets=c.carrier_jets if q else ORIGINAL;fun=k.setup(seed['direction'],params)
 a,b=map(m.mpf,seed['direction']);norm=m.sqrt(a*a+b*b);a/=norm;b/=norm;lam=m.mpf(row['lam']);kap=m.mpf(row['kappa'])
 def src(x):
  y=m.exp(2*x)
  if q:
   parity=1 if q==4 else 0;chi=c.CHARS[q];mu=2*m.exp((parity+m.mpf('.5'))*x)*sum(chi[n%q]*n**parity*m.exp(-m.pi*n*n*y/q) for n in range(1,41) if chi[n%q])
  else:mu=m.exp(x/2)*sum(2*m.pi*(2*m.pi*n**4*y*y-3*n*n*y)*m.exp(-m.pi*n*n*y) for n in range(1,17))
  h=[sum(v*m.cos(j*x) for j,v in hh.items()) for hh in hs]
  return mu*(1+lam*(a*h[0]+b*h[1])+kap*lam*lam*a*b*h[2])
 out=dict(row=row,checks=[])
 for off in ['0','.125']:
  t=m.mpf(row['t'])+m.mpf(off);scale=m.exp(-m.pi*t/4)*(1+t*t)**m.mpf('.875');expected=fun(t,lam,kap)[0]
  for der in [0,1]:
   integrand=(lambda x:src(x)*m.cos(t*x)) if der==0 else (lambda x:-x*src(x)*m.sin(t*x))
   val=2*m.quad(integrand,[0,.25,.5,.75,1,1.5,2,3,4])/scale
   out['checks'].append(dict(offset=off,derivative=der,actual=m.nstr(val,190),error=m.nstr(abs(val-expected[der]),100)))
 out['seconds']=time.monotonic()-start;return out

if __name__=='__main__':
 start=time.monotonic();jobs=[(p,kap,50) for p in POINTS for kap in ['0','.25','.5','.75','1']];rows=[]
 with ProcessPoolExecutor(max_workers=14) as pool,open('screen.jsonl','w',buffering=1) as f:
  # Pilot is one coupling-matched candidate per source point.
  pilot=[(p,str(p['seed']['interaction']),50) for p in POINTS];done=set();times=[]
  for fut in as_completed([pool.submit(solve,j) for j in pilot]):
   r=fut.result();rows.append(r);times.append(r['seconds']);f.write(json.dumps(r)+'\n');done.add((tuple(r['reference_t']),r['kappa']));print('pilot',r.get('t'),r.get('error'),flush=True)
  rest=[j for j in jobs if (tuple(j[0]['precision'][-1]['t']),j[1]) not in done]
  estimate=max(times)*len(rest)/14;remaining=DEAD-time.monotonic();Path('pilot.json').write_text(json.dumps(dict(estimate=estimate,remaining=remaining,admitted=estimate<remaining/3)))
  if estimate<remaining/3:
   for fut in as_completed([pool.submit(solve,j) for j in rest]):
    r=fut.result();rows.append(r);f.write(json.dumps(r)+'\n');print('screen',r.get('t'),r['kappa'],r.get('error'),flush=True)
  good=[r for r in rows if r.get('admitted')];ref=[]
  with open('validation.jsonl','w',buffering=1) as f:
   jobs2=[]
   for r in good:
    point=next(p for p in POINTS if p['precision'][-1]['t']==r['reference_t']);jobs2 += [(point,r['kappa'],prec) for prec in [100,160]]
   for fut in as_completed([pool.submit(solve,j) for j in jobs2]):
    r=fut.result();ref.append(r);f.write(json.dumps(r)+'\n')
  with open('source-validation.jsonl','w',buffering=1) as f:
   for fut in as_completed([pool.submit(source,r) for r in ref if r['dps']==160 and r.get('admitted')]):
    r=fut.result();f.write(json.dumps(r)+'\n');print('independent',r['row']['t'][:16],r['row']['kappa'],flush=True)
 Path('summary.json').write_text(json.dumps(dict(seconds=time.monotonic()-start,screen=len(rows),admitted=len(good),refined=len(ref))))
