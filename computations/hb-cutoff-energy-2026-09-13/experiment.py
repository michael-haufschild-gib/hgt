import json,time,os
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed
import numpy as np
import mpmath as m
import source as a
BASE=json.loads(Path('baseline.json').read_text())

def packet(job):
 label,dps,margin,q,j=job;start=time.monotonic();t,A=a.init(BASE[label]['item']['t'],dps);nodes,weights=np.polynomial.legendre.leggauss(q)
 lo=m.log(4)*j/32;hi=m.log(4)*(j+1)/32;tot=[m.mpf(0)]*4
 try:
  for x,w in zip(nodes,weights):
   v=(lo+hi)/2+(hi-lo)*m.mpf(float(x))/2;y=m.exp(v);weight=(hi-lo)*m.mpf(float(w))/2/y
   c=a.coefficients(t,A,y,margin);z=c[len(c)//2]**2;Q=m.fsum(x*x for i,x in enumerate(c) if i!=len(c)//2)
   vals=[z,z*z+2*z*Q,z+Q,(z+Q)**2];tot=[v+weight*x for v,x in zip(tot,vals)]
  return dict(label=label,dps=dps,margin=margin,q=q,cell=j,values=list(map(str,tot)),seconds=time.monotonic()-start)
 except Exception as ex:return dict(label=label,dps=dps,margin=margin,q=q,cell=j,error=str(ex)[:200],seconds=time.monotonic()-start)

def check(label):
 start=time.monotonic();t,A=a.init(BASE[label]['item']['t'],160);out=[]
 for y in [m.mpf('1.1'),m.mpf('1.7'),m.mpf('3.8')]:
  c=a.coefficients(t,A,y,100);f=a.conv(c,c);k=len(f)//2;z=c[len(c)//2]**2;Q=f[k]-z
  fullmean=f[k];fullenergy=m.fsum(x*x for x in f);part=a.moments(c)
  errors=[abs(fullmean-part[0]-z),abs(fullenergy-part[1]-(z*z+2*z*Q)),abs(fullmean-part[2]-(z+Q)),abs(fullenergy-part[3]-(z+Q)**2)]
  out.append(dict(y=str(y),errors=list(map(str,errors))))
 return dict(label=label,checks=out,seconds=time.monotonic()-start)

if __name__=='__main__':
 start=time.monotonic();variants=[(50,60,12),(50,100,12),(50,60,24),(50,100,24),(100,100,24),(160,100,24)];rows=[]
 with ProcessPoolExecutor(max_workers=14) as pool,open('packets.jsonl','w',buffering=1) as out:
  jobs=[(label,d,margin,q,j) for label in BASE for d,margin,q in variants for j in range(32)]
  for fut in as_completed([pool.submit(packet,j) for j in jobs]):
   r=fut.result();rows.append(r);out.write(json.dumps(r)+'\n')
   if len(rows)%32==0:print('packets',len(rows),'of',len(jobs),flush=True)
  with open('curves.jsonl','w',buffering=1) as out:
   for label in BASE:
    for d,margin,q in variants:
     parts=sorted([r for r in rows if (r['label'],r['dps'],r['margin'],r['q'])==(label,d,margin,q)],key=lambda r:r['cell']);m.mp.dps=d;t,A=a.init(BASE[label]['item']['t'],d)
     row=dict(label=label,dps=d,margin=margin,q=q,points=[])
     if len(parts)!=32 or any('error' in p for p in parts):row['error']='incomplete packets'
     else:
      totals=[m.mpf(BASE[label]['values'][kind][field]) for kind in ['principal','constant_fourier'] for field in ['mean','energy']]
      for j in range(33):
       if j:totals=[v+m.mpf(x) for v,x in zip(totals,parts[j-1]['values'])]
       H=m.exp(m.log(4)*j/32);values={}
       for kind,i in [('principal',0),('constant_fourier',2)]:
        M,E=totals[i:i+2];V=E-M*M/(m.pi/3);values[kind]=dict(mean=str(M),energy=str(E),ratio=str(t*t*M*M/(2176*(m.pi/3)*V)))
       exact=2*m.log(H)+(m.sin(2*m.arg(A)+2*t*m.log(H))-m.sin(2*m.arg(A)))/t
       err=abs(totals[0]-m.mpf(BASE[label]['values']['principal']['mean'])-exact)
       row['points'].append(dict(H=str(H),values=values,exact_mean_error=str(err)))
     out.write(json.dumps(row)+'\n')
  with open('identity-checks.jsonl','w',buffering=1) as out:
   for fut in as_completed([pool.submit(check,label) for label in BASE]):out.write(json.dumps(fut.result())+'\n')
 Path('summary.json').write_text(json.dumps(dict(seconds=time.monotonic()-start,packets=len(rows))))
