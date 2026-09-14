from experiment import Transform
from common import *
from concurrent.futures import ProcessPoolExecutor,as_completed

def jets(T,w):
    c=mp.cos(w*T.h);s=mp.sin(w*T.h);cj=mp.mpc(1);sj=mp.mpc(0);out=[mp.mpc(0) for _ in range(3)]
    for x,a in zip(T.x,T.weights):
        out[0]+=a*cj;out[1]-=a*x*sj;out[2]-=a*x*x*cj;cj,sj=cj*c-sj*s,sj*c+cj*s
    return out

def work(job):
    start=time.monotonic();r=dict(job=job,dps=80);folds=[];fails=[]
    try:
        T=Transform(job['base'],128,80);U=Transform(job['base']+[job['extra']],128,80)
        def W(w):
            budget();a=jets(T,w);b=jets(U,w);return mp.re(a[0]*b[1]-a[1]*b[0]),mp.re(a[0]*b[2]-a[2]*b[0]),a,b
        grid=[]
        for j in range(241):
            w=10+mp.mpf(j)/4;v,_,_,_=W(w);grid.append((w,v))
        intervals=[(grid[k-1][0],grid[k][0]) for k in range(1,len(grid)) if grid[k-1][1]*grid[k][1]<0]
        for lo,hi in intervals:
            try:
                x=(lo+hi)/2
                for it in range(45):
                    v,d,a,b=W(x);step=v/d
                    if abs(step)<mp.mpf('1e-24'):break
                    xx=x-step
                    if not(lo<xx<hi):xx=(lo+hi)/2
                    vv,_,_,_=W(xx);vl,_,_,_=W(lo)
                    if vv*vl<0:hi=xx
                    else:lo=xx
                    x=xx
                v,d,a,b=W(x);lam=mp.re(-a[0]/(b[0]-a[0]));curv=mp.re((1-lam)*a[2]+lam*b[2]);gain=mp.re(-2*(b[0]-a[0])/curv)
                if not(mp.mpf('1e-8')<lam<1-mp.mpf('1e-8')):continue
                if any(abs(x-dec(q['w']))<mp.mpf('1e-10') for q in folds):continue
                branches=[];delta=min(mp.mpf('.01'),lam/4,(1-lam)/4)
                for side in [-1,1]:
                    ll=lam+side*delta;wp=x+mp.sqrt(mp.mpc(gain*side*delta))
                    for k in range(30):
                        aa=jets(T,wp);bb=jets(U,wp);f=(1-ll)*aa[0]+ll*bb[0];df=(1-ll)*aa[1]+ll*bb[1];ss=f/df;wp-=ss
                        if abs(ss)<mp.mpf('1e-24'):break
                    branches.append(dict(lambda_value=str(ll),root=enc(wp),correction=str(abs(ss)),residual=str(abs(f))))
                folds.append(dict(w=enc(x),lambda_value=str(lam),gain=str(gain),direction='healing-as-extra-deletion-increases' if gain>0 else 'complexification-as-extra-deletion-increases',fold_residual=str(abs((1-lam)*a[0]+lam*b[0])),derivative_residual=str(abs((1-lam)*a[1]+lam*b[1])),W_correction=str(abs(v/d)),branches=branches))
            except TimeoutError:raise
            except Exception as e:fails.append(dict(interval=[str(lo),str(hi)],error=repr(e)))
        r.update(status='ok',bracket_count=len(intervals),moments=[str(T.m2),str(U.m2)])
    except Exception as e:r.update(status='error',error=repr(e))
    r.update(folds=folds,failures=fails,seconds=time.monotonic()-start);save('case-'+job['label']+'.json',r);return r
if __name__=='__main__':
    jobs=json.loads(Path('jobs.json').read_text());rows=[];start=time.monotonic()
    with ProcessPoolExecutor(max_workers=14) as ex:
        for f in as_completed([ex.submit(work,j) for j in jobs]):
            r=f.result();rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print(r['job']['label'],r['status'],len(r['folds']),flush=True)
