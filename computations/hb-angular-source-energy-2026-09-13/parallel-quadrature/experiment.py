import os,time,json
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed
import mpmath as m
import numpy as np
import source as a

def packet(job):
 name,item,res,margin,dps,batch=job;start=time.monotonic();t,A=a.init(item['t'],dps);total=[m.mpf(0)]*4
 try:
  for kind,x,weight in batch:
   if kind=='compact':
    x=m.mpf(x);y=m.sqrt(1-x*x);w=m.mpf(weight)*x/(1-x*x)**m.mpf('1.5');vals=a.moments(a.coefficients(t,A,y,margin),x)
   else:
    y=m.exp(m.mpf(x));w=m.mpf(weight)/y;vals=a.moments(a.coefficients(t,A,y,margin))
   total=[v+w*z for v,z in zip(total,vals)]
  return dict(name=name,values=list(map(str,total)),nodes=len(batch),seconds=time.monotonic()-start)
 except Exception as ex:return dict(name=name,error=str(ex)[:180],seconds=time.monotonic()-start)

if __name__=='__main__':
 start=time.monotonic();items=a.S['heights'][:2];jobs=[];variants={};m.mp.dps=50
 for item in items:
  for res,margin,dps in [(1,60,50),(1,100,50),(2,60,50),(2,100,50),(2,100,100),(2,100,160)]:
   t=m.mpf(item['t']);q=int(np.ceil(.7*float(t)+24))*res;nodes,weights=np.polynomial.legendre.leggauss(q);points=[]
   for x,w in zip(nodes,weights):points.append(('compact',repr(float((x+1)/4)),repr(float(w/4))))
   end=m.log((t+100)/(2*m.pi)+2);panels=int(m.ceil(end/m.log(2)))
   for j in range(panels):
    lo=end*j/panels;hi=end*(j+1)/panels
    for x,w in zip(nodes,weights):points.append(('tail',str((lo+hi)/2+(hi-lo)*m.mpf(float(x))/2),str((hi-lo)*m.mpf(float(w))/2)))
   name=item['label']+'-'+str(res)+'-'+str(margin)+'-'+str(dps)
   variants[name]=dict(item=item,resolution=res,margin=margin,dps=dps,q=q,expected_nodes=len(points))
   for j in range(0,len(points),12):jobs.append((name,item,res,margin,dps,points[j:j+12]))
 Path('parameters.json').write_text(json.dumps(variants,indent=2))
 rows=[]
 with ProcessPoolExecutor(max_workers=14) as pool,open('packets.jsonl','w',buffering=1) as out:
  for fut in as_completed([pool.submit(packet,j) for j in jobs]):
   r=fut.result();rows.append(r);out.write(json.dumps(r)+'\n')
   if len(rows)%40==0:print('packets',len(rows),'of',len(jobs),'elapsed',time.monotonic()-start,flush=True)
  with open('energy.jsonl','w',buffering=1) as out:
   for name,v in variants.items():
    parts=[r for r in rows if r['name']==name];m.mp.dps=v['dps']
    result=dict(name=name,**v)
    if sum(r.get('nodes',0) for r in parts)!=v['expected_nodes']:result['error']='incomplete packets'
    else:
     total=[m.fsum(m.mpf(r['values'][i]) for r in parts) for i in range(4)];vals={};t=m.mpf(v['item']['t'])
     for kind,i in [('principal',0),('constant_fourier',2)]:
      M,E=total[i:i+2];V=E-M*M/(m.pi/3);R=t*t*M*M/(2176*(m.pi/3)*V)
      vals[kind]=dict(mean=str(M),energy=str(E),variance=str(V),ratio=str(R))
     result['values']=vals
    out.write(json.dumps(result)+'\n');print('energy',name,result.get('error'),flush=True)
  with open('independent.jsonl','w',buffering=1) as out:
   for fut in as_completed([pool.submit(a.independent,(it,160)) for it in items]):out.write(json.dumps(fut.result())+'\n')
 Path('summary.json').write_text(json.dumps(dict(seconds=time.monotonic()-start,packets=len(rows),variants=len(variants))))
