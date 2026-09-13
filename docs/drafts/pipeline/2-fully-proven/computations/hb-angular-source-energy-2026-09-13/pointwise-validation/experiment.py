import json,time,math
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed
import numpy as np
import mpmath as m
import source as a
CASES=json.loads(Path('cases.json').read_text())
def point(job):
 name,item,batch=job;start=time.monotonic();t,A=a.init(item['t'],50);out=np.zeros(4)
 try:
  for kind,v,w in batch:
   if kind=='compact':
    lower=float(v);y=math.sqrt(1-lower*lower);weight=float(w)*lower/(1-lower*lower)**1.5
   else:lower=None;y=math.exp(float(v));weight=float(w)/y
   cc=a.coefficients(t,A,m.mpf(y),100);N=len(cc)//2;c=np.array([float(x) for x in cc[N:]])
   if lower is None:
    nx=1
    while nx<=4*N:nx*=2
    x=np.arange(nx)/nx-.5;weights=np.full(nx,1/nx)
   else:
    nx=int(math.ceil(2*math.pi*N))+24;xx,ww=np.polynomial.legendre.leggauss(nx)
    x=(lower+.5)/2+(.5-lower)*xx/2;weights=(.5-lower)*ww
   S=c[0]+np.cos(2*np.pi*np.outer(x,np.arange(1,N+1)))@(2*c[1:]);square=S*S
   if lower is None and y>item['cutoff']:
    fp=square-c[0]*c[0];fc=square-float(weights@square)
   else:fp=fc=square
   out+=weight*np.array([weights@fp,weights@(fp*fp),weights@fc,weights@(fc*fc)])
  return dict(name=name,values=out.tolist(),seconds=time.monotonic()-start)
 except Exception as ex:return dict(name=name,error=str(ex)[:180],seconds=time.monotonic()-start)
if __name__=='__main__':
 start=time.monotonic();jobs=[];expected={}
 for item in CASES:
  name=item['name'];t=float(item['t']);q=int(math.ceil(.7*t+24));nodes,weights=np.polynomial.legendre.leggauss(q);points=[]
  for x,w in zip(nodes,weights):points.append(('compact',float((x+1)/4),float(w/4)))
  Y=(t+100)/(2*math.pi)+2;breaks=sorted(set([0,math.log(item['cutoff']),math.log(Y)]+[k*math.log(2) for k in range(1,int(math.log(Y)/math.log(2))+1)]))
  for lo,hi in zip(breaks,breaks[1:]):
   if hi==lo:continue
   for x,w in zip(nodes,weights):points.append(('tail',float((lo+hi)/2+(hi-lo)*x/2),float((hi-lo)*w/2)))
  packets=[points[j:j+8] for j in range(0,len(points),8)];expected[name]=len(packets)
  jobs +=[(name,item,pk) for pk in packets]
 rows=[]
 with ProcessPoolExecutor(max_workers=14) as pool,open('packets.jsonl','w',buffering=1) as out:
  for fut in as_completed([pool.submit(point,j) for j in jobs]):
   r=fut.result();rows.append(r);out.write(json.dumps(r)+'\n')
  with open('validation.jsonl','w',buffering=1) as out:
   for item in CASES:
    parts=[r for r in rows if r['name']==item['name']];r=dict(case=item)
    if len(parts)!=expected[item['name']] or any('error' in x for x in parts):r['error']='incomplete packets'
    else:
     totals=[math.fsum(p['values'][i] for p in parts) for i in range(4)];vals={}
     for kind,i in [('principal',0),('constant_fourier',2)]:
      M,E=totals[i:i+2];V=E-M*M/(math.pi/3);vals[kind]=dict(mean=M,energy=E,ratio=float(item['t'])**2*M*M/(2176*(math.pi/3)*V))
     r['values']=vals
    out.write(json.dumps(r)+'\n');print(r,flush=True)
 Path('summary.json').write_text(json.dumps(dict(seconds=time.monotonic()-start,packets=len(rows))))
