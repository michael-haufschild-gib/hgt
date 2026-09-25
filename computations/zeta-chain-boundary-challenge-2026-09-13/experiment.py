from common import *
from independent import independent_points,em
from discovery import startpoint,classify
from concurrent.futures import ProcessPoolExecutor,as_completed

def work(job):
    n,kind,dps=job;mp.mp.dps=dps;start=time.monotonic();r=dict(n=n,kind=kind,dps=dps)
    try:
        s,info=lift(startpoint(n),lambda u:target(kind,u),.012)
        independent=independent_points(info['path'],kind,dps)
        r.update(status='ok',endpoint=enc(s),endpoint_label=classify(s),trivial_distance=str(abs(s+4)),independent=independent,**info)
    except Exception as e:r.update(status='error',error=repr(e))
    r['seconds']=time.monotonic()-start;save('check-%d-%s-%d.json'%(n,kind,dps),r)
    return {k:v for k,v in r.items() if k!='path'}
if __name__=='__main__':
    jobs=[(n,k,d) for n,k in [(-1,'circle'),(-1,'small'),(-3,'circle'),(-7,'circle'),(-9,'circle'),(128,'circle'),(320,'circle')] for d in [100,160]]
    rows=[];start=time.monotonic()
    with ProcessPoolExecutor(max_workers=14) as ex:
        for f in as_completed([ex.submit(work,j) for j in jobs]):
            r=f.result();rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print(r['n'],r['kind'],r['dps'],r['status'],flush=True)
