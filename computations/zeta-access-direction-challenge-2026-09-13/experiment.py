from common import *
from discovery import path
from independent import em
from concurrent.futures import ProcessPoolExecutor,as_completed

def work(job):
    n,label,dps=job;mp.mp.dps=dps;angle=label*mp.pi/3;start=time.monotonic();r=dict(n=n,angle_thirds_pi=label,dps=dps)
    try:
        end,info=lift(zeros()[n],lambda u:path(angle,u),.002)
        checks=[];mp.mp.dps=dps+60
        for ix in sorted(set(round(j*(len(info['path'])-1)/8) for j in range(9))):
            row=info['path'][ix];u=mp.mpf(row[0]);s=mp.mpc(row[1],row[2]);N=max(96,int(abs(mp.im(s)))+80)
            a=em(s,N,dps+25);bb=em(s,N+40,dps+45)
            w=path(angle,u);eps=abs(1-w)
            checks.append(dict(u=str(u),truncation_disagreement=str(abs(a-bb)),native_disagreement=str(abs(bb-mp.zeta(s))),target_residual=str(abs(bb-w)),relative_target_distance_residual=str(abs(bb-w)/eps)))
        mp.mp.dps=dps;r.update(status='ok',endpoint=enc(end),checks=checks,**info)
        if mp.re(end)<10:
            s=end
            for _ in range(8):s-=(zeta(s)-1)/zeta(s,1)
            r['finite_one_point']=enc(s);mp.mp.dps=dps+60;N=max(96,int(abs(mp.im(s)))+80)
            r['finite_one_independent_residual']=str(abs(em(s,N,dps+25)-1));mp.mp.dps=dps
    except Exception as e:r.update(status='error',error=repr(e))
    r['seconds']=time.monotonic()-start;save('check-%d-%d-%d.json'%(n,label,dps),r)
    return {k:v for k,v in r.items() if k!='path'}
if __name__=='__main__':
    jobs=[(n,a,d) for n,a in [(2,0),(2,-1),(3,0),(3,-1),(57,-1),(57,0)] for d in [100,160]]
    rows=[];start=time.monotonic()
    with ProcessPoolExecutor(max_workers=14) as ex:
        for f in as_completed([ex.submit(work,j) for j in jobs]):
            r=f.result();rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print(r['n'],r['angle_thirds_pi'],r['dps'],r['status'],flush=True)
