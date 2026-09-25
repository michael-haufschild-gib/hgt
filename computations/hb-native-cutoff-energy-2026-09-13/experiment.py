import json,time,math
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed
import mpmath as m
import numpy as np
import source as a
B=json.loads(Path('baseline.json').read_text());PROFILES=['native','late','early','sharp2','sharp2.5','sharp3']
def chi(y,p):
 if p.startswith('sharp'):return m.mpf(y>m.mpf(p[5:]))
 if y<=2:c=m.mpf(0)
 elif y>=3:c=m.mpf(1)
 else:c=1/(1+m.exp(1/(y-2)-1/(3-y)))
 return c*c if p=='late' else 1-(1-c)**2 if p=='early' else c

def packet(job):
 label,dps,margin,res,batch=job;start=time.monotonic();t,A=a.init(B[label]['item']['t'],dps);tot=[[m.mpf(0)]*4 for _ in PROFILES]
 try:
  for y,w in batch:
   y=m.mpf(y);w=m.mpf(w)/y**2;c=a.coefficients(t,A,y,margin);z=c[len(c)//2]**2;Q=m.fsum(x*x for i,x in enumerate(c) if i!=len(c)//2)
   for j,p in enumerate(PROFILES):
    h=(1-chi(y,p))*z;k=(1-chi(y,p))*(z+Q)
    tot[j]=[v+w*x for v,x in zip(tot[j],[h,2*h*Q+h*h,k,k*k])]
  return dict(label=label,dps=dps,margin=margin,res=res,values=[[str(x) for x in row] for row in tot],seconds=time.monotonic()-start)
 except Exception as ex:return dict(label=label,dps=dps,margin=margin,res=res,error=str(ex),seconds=time.monotonic()-start)

def check(label):
 start=time.monotonic();t,A=a.init(B[label]['item']['t'],160);out=[]
 for y in [m.mpf('1.3'),m.mpf('2.3'),m.mpf('2.7')]:
  c=a.coefficients(t,A,y,100);f=a.conv(c,c);j=len(f)//2;z=c[len(c)//2]**2;Q=f[j]-z;base=a.moments(c)
  for p in PROFILES:
   h=(1-chi(y,p))*z;k=(1-chi(y,p))*(z+Q);fp=f[:];fc=f[:];fp[j]-=chi(y,p)*z;fc[j]-=chi(y,p)*(z+Q)
   actual=[fp[j],m.fsum(x*x for x in fp),fc[j],m.fsum(x*x for x in fc)]
   expected=[base[0]+h,base[1]+2*h*Q+h*h,base[2]+k,base[3]+k*k]
   out.append(dict(y=str(y),profile=p,max_error=str(max(abs(x-v) for x,v in zip(actual,expected)))))
 return dict(label=label,checks=out,seconds=time.monotonic()-start)
if __name__=='__main__':
 start=time.monotonic();jobs=[];expect={};variants=[(50,60,1),(50,100,1),(50,60,2),(50,100,2),(100,100,2),(160,100,2)]
 for label,b in B.items():
  for d,margin,res in variants:
   q=math.ceil(.5*float(b['item']['t'])+32)*res;x,w=np.polynomial.legendre.leggauss(q);pts=[]
   for lo,hi in [(1,2),(2,2.5),(2.5,3)]:
    pts +=[(repr(float((hi+lo)/2+(hi-lo)*xx/2)),repr(float((hi-lo)*ww/2))) for xx,ww in zip(x,w)]
   batches=[pts[i:i+12] for i in range(0,len(pts),12)];expect[(label,d,margin,res)]=len(batches);jobs +=[(label,d,margin,res,v) for v in batches]
 rows=[]
 with ProcessPoolExecutor(max_workers=14) as pool,open('packets.jsonl','w',buffering=1) as out:
  for fut in as_completed([pool.submit(packet,j) for j in jobs]):
   r=fut.result();rows.append(r);out.write(json.dumps(r)+'\n')
   if len(rows)%40==0:print('packets',len(rows),'/',len(jobs),flush=True)
  with open('energy.jsonl','w',buffering=1) as out:
   for (label,d,margin,res),count in expect.items():
    pp=[r for r in rows if (r['label'],r['dps'],r['margin'],r['res'])==(label,d,margin,res)];m.mp.dps=d;t=m.mpf(B[label]['item']['t']);row=dict(label=label,dps=d,margin=margin,res=res,profiles={})
    if len(pp)!=count or any('error' in p for p in pp):row['error']='incomplete packets'
    else:
     for j,p in enumerate(PROFILES):
      vals={}
      for kind,i in [('principal',0),('constant_fourier',2)]:
       M=m.mpf(B[label]['values'][kind]['mean'])+m.fsum(m.mpf(r['values'][j][i]) for r in pp);E=m.mpf(B[label]['values'][kind]['energy'])+m.fsum(m.mpf(r['values'][j][i+1]) for r in pp);V=E-M*M/(m.pi/3)
       vals[kind]=dict(mean=str(M),energy=str(E),variance=str(V),ratio=str(t*t*M*M/(2176*(m.pi/3)*V)))
      row['profiles'][p]=vals
    out.write(json.dumps(row)+'\n')
  with open('independent.jsonl','w',buffering=1) as out:
   for f in as_completed([pool.submit(check,l) for l in B]):out.write(json.dumps(f.result())+'\n')
 Path('summary.json').write_text(json.dumps(dict(seconds=time.monotonic()-start,packets=len(rows))))
