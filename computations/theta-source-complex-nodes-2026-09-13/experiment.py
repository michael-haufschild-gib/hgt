from source import *
from concurrent.futures import ProcessPoolExecutor,as_completed

def work(job):
    x,y=job;mp.mp.dps=50;start=time.monotonic();r=dict(start=[x,y],dps=50)
    try:
        z,info=solve(mp.mpc(str(x),str(y)));v,nn,N,e=jets(z,extra=20);r.update(status='ok',root=enc(z),term_refinement_residual=str(abs(v[0])/nn),**info)
    except Exception as ex:r.update(status='error',error=repr(ex))
    r['seconds']=time.monotonic()-start;save('root-%s-%s.json'%(x,y),r);return r
if __name__=='__main__':
    jobs=[(x,y) for x in [0,.05,.1,.2,.35,.5,.7,1,1.5,2] for y in [0,.25,.5,.6,.65,.7,.73,.75,.765,.775,.781,.784]];rows=[];start=time.monotonic()
    with ProcessPoolExecutor(max_workers=14) as ex:
        pilot=list(ex.map(work,[(.2,.7),(1,.775)]));rows.extend(pilot);save('pilot.json',dict(rows=pilot,seconds=time.monotonic()-start))
        for f in as_completed([ex.submit(work,j) for j in jobs if j not in [( .2,.7),(1,.775)]]):
            r=f.result();rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print(r['start'],r.get('root',r.get('error')),flush=True)
