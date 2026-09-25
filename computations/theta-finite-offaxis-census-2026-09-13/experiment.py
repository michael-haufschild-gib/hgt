import json,time,os
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed
import mpmath as m
import analytic as e

def contour(job):
 seed,frac,lo,hi=job;start=time.monotonic();F,p=e.make(seed,50);lam=m.mpf(seed['lam'])*m.mpf(frac)
 rect=[m.mpc(lo,'.03'),m.mpc(hi,'.03'),m.mpc(hi,'2'),m.mpc(lo,'2')]
 out=dict(seed=seed,fraction=frac,lo=lo,hi=hi,dps=50,contours=[])
 cache={}
 def value(z):
  key=(m.nstr(z.real,55),m.nstr(z.imag,55))
  if key not in cache:cache[key]=F(z,lam)
  return cache[key]
 try:
  for n in [32,64,128]:
   zs=[rect[j]+m.mpf(k)/n*(rect[(j+1)%4]-rect[j]) for j in range(4) for k in range(n)]
   vals=[value(z) for z in zs];ph=[m.arg(vals[(i+1)%len(vals)]/v) for i,v in enumerate(vals)]
   winding=sum(ph)/(2*m.pi);peak=max(abs(v) for v in ph)
   out['contours'].append(dict(n=n,winding=str(winding),max_phase=str(peak),minimum=str(min(abs(v) for v in vals)),samples=[dict(z=e.enc(z),f=e.enc(v)) for z,v in zip(zs,vals)]))
   if n==64 and all(abs(m.mpf(r['winding']))<m.mpf('.1') for r in out['contours']) and peak<m.mpf('2'):break
  counts=[int(m.nint(m.mpf(r['winding']))) for r in out['contours']]
  out['stable']=len(set(counts[-2:]))==1 and m.mpf(out['contours'][-1]['max_phase'])<2
  out['count']=counts[-1];out['positivity_bound']=str(abs(lam)*m.sqrt(2)+seed['interaction']*lam*lam/2*m.mpf(p['h12_l1']))
 except Exception as exc:out['error']=str(exc)[:220]
 out['seconds']=time.monotonic()-start;return out

if __name__=='__main__':
 start=time.monotonic();seeds=e.SEEDS;theta=e.MODE=='theta'
 edges=['13.2','53.2','93.2','133.2','174'] if theta else ['4.2','14.2','24.2','34.2','44.2']
 # Pilot covers every carrier/direction/coupling, one tile at half of known collision.
 pilot=[(s,'.5',edges[1],edges[2]) for s in seeds]
 rest=[(s,f,edges[j],edges[j+1]) for f in ['.5','.9','.25'] for j in range(4) for s in seeds if not (f=='.5' and j==1)]
 done=0
 with ProcessPoolExecutor(max_workers=14) as pool,open('results.jsonl','w',buffering=1) as out:
  pilot_times=[]
  for fut in as_completed([pool.submit(contour,j) for j in pilot]):
   r=fut.result();out.write(json.dumps(r)+'\n');done+=1;pilot_times.append(r['seconds']);print('pilot',r['seed'].get('q',0),r['seed']['n'],r.get('count'),r.get('error'),r['seconds'],flush=True)
  remaining=float(os.environ['CAMPAIGN_DEADLINE'])-time.monotonic()-70
  maxjobs=max(0,min(len(rest),int(remaining*14/(max(pilot_times)*1.3))))
  Path('admission-result.json').write_text(json.dumps(dict(pilot_seconds=pilot_times,planned=len(rest),admitted=maxjobs,remaining_seconds=remaining)))
  for fut in as_completed([pool.submit(contour,j) for j in rest[:maxjobs]]):
   r=fut.result();out.write(json.dumps(r)+'\n');done+=1;print('cell',done,r['fraction'],r['lo'],r.get('count'),r.get('stable'),r.get('error'),flush=True)
 Path('summary.json').write_text(json.dumps(dict(seconds=time.monotonic()-start,completed=done)))
