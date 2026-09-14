from common import *
from independent import em
from concurrent.futures import ProcessPoolExecutor,as_completed

def work(job):
    seed,dps,epsstr,step=job;mp.mp.dps=dps;start=time.monotonic();r=dict(seed=seed,dps=dps,epsilon=epsstr,step=step)
    try:
        s=dec(json.loads(Path('seeds.json').read_text())[str(seed)])
        for _ in range(10):s-=zeta(s,1)/zeta(s,2)
        c=zeta(s);eps=mp.mpf(epsstr);delta=mp.sqrt(-2*c*eps/zeta(s,2));branches=[]
        for sign in [-1,1]:
            p=s+sign*delta;w=c*(1-eps)
            for _ in range(12):p-=(zeta(p)-w)/zeta(p,1)
            end,info=lift(p,lambda u:c*(1-eps)*(1-u),step)
            checkpoints=[]
            mp.mp.dps=dps+30
            for ix in sorted(set(round(j*(len(info['path'])-1)/6) for j in range(7))):
                row=info['path'][ix];u=mp.mpf(row[0]);sp=mp.mpc(row[1],row[2]);N=max(96,int(abs(mp.im(sp)))+80);M=dps+25
                a=em(sp,N,M);b=em(sp,N+40,M+20)
                checkpoints.append(dict(u=str(u),truncation_disagreement=str(abs(a-b)),target_residual=str(abs(b-c*(1-eps)*(1-u))),zeta_disagreement=str(abs(b-mp.zeta(sp)))))
            mp.mp.dps=dps
            branches.append(dict(endpoint=enc(end),nearest_zero=closest(end),independent=checkpoints,**info))
        r.update(status='ok',critical_point=enc(s),critical_value=enc(c),critical_residual=str(abs(zeta(s,1))),branches=branches)
    except Exception as e:r.update(status='error',error=repr(e))
    r['seconds']=time.monotonic()-start;save('check-%d-%d-%s.json'%(seed,dps,epsstr),r)
    return {k:v for k,v in r.items() if k!='branches'}
if __name__=='__main__':
    jobs=[(seed,dps,eps,step) for seed in [29,38,55,59] for dps in [100,160] for eps,step in [('1e-5',.012),('1e-7',.006)]]
    rows=[];start=time.monotonic()
    with ProcessPoolExecutor(max_workers=14) as ex:
        for f in as_completed([ex.submit(work,j) for j in jobs]):
            r=f.result();rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print(r['seed'],r['dps'],r['epsilon'],r['status'],flush=True)
