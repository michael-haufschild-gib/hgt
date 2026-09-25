from source import *
from independent import Independent,phi_independent
from concurrent.futures import ProcessPoolExecutor,as_completed

def refine_node(z):
    z=dec(z)
    for k in range(12):
        v,n,e,N=raw_jets('D',z,2,True);ds=v[0]/v[1];z-=ds
        if abs(ds)<mp.mpf(10)**(-mp.mp.dps+20):break
    return z

def refined_job(job,hden,dps):
    j=dict(job);zz=json.loads(Path('nodes.json').read_text());h=job['host'];rem=[];ins=[]
    if 'dh_node' in job:
        dh=refine_node(job['dh_node']);j['refined_dh_node']=enc(dh)
        if h=='D':
            rem=[enc(dh)]
            if 'donor_index' in job:
                scale=mp.sqrt(Transform('D',hden=hden,dps=dps).m2/Transform('R',hden=hden,dps=dps).m2) if job['mode']=='variance' else 1
                ins=[enc(dec(zz[job['donor_index']])*scale)]
        else:rem=[zz[job['removed_index']]];ins=[enc(dh)]
    else:
        scale=mp.sqrt(Transform(h,hden=hden,dps=dps).m2/Transform('R',hden=hden,dps=dps).m2) if job.get('mode')=='variance' else 1
        ins=[enc(dec(zz[i])*scale) for i in job.get('donor_indices',[])]
    j.update(remove=rem,insert=ins);return j

def jets(T,w):
    c=mp.cos(w*T.h);s=mp.sin(w*T.h);cj=mp.mpc(1);sj=mp.mpc(0);a=[mp.mpc(0)]*3
    for x,v in zip(T.x,T.weights):
        a[0]+=v*cj;a[1]-=v*x*sj;a[2]-=v*x*x*cj;cj,sj=cj*c-sj*s,sj*c+cj*s
    return a

def root_refine(T,w,dps):
    for k in range(15):
        v,d=T.val(w);step=v/d;w-=step
        if abs(step)<mp.mpf(10)**(-dps+40):break
    return w

def inserted_completion(job,w):
    co=[mp.mpf(1)]
    for zz in job['insert']:
        z=dec(zz)
        pp=[1,0,1/mp.im(z)**2] if abs(mp.re(z))<mp.mpf('1e-40') else [1,0,-2*mp.re(1/z**2),0,1/abs(z)**4]
        out=[mp.mpf(0)]*(len(co)+len(pp)-1)
        for k,a in enumerate(co):
            for l,b in enumerate(pp):out[k+l]+=a*b
        co=out
    s=mp.mpf('.5')+1j*w
    return mp.fsum(v*mp.diff(lambda z:completed(job['host'],(z-mp.mpf('.5'))/1j),s,k) for k,v in enumerate(co) if v)

def work(task):
    row,dps=task;mp.mp.dps=dps;start=time.monotonic();r=dict(row=row,dps=dps)
    try:
        hd=128 if dps==100 else 256
        if row['kind']=='node':
            z=refine_node(row['root']);v,n,e,N=raw_jets('D',z,2,False);scale=n*mp.exp(mp.re(e));iv=phi_independent('D',z);r.update(root=enc(z),native_residual=str(abs(v[0])/n),independent_residual=str(abs(iv)/scale),terms=N)
            vals=[phi_independent('D',z+mp.mpf('.002')*mp.exp(2j*mp.pi*j/32)) for j in range(32)];ph=[mp.arg(vals[(j+1)%32]/vals[j]) for j in range(32)];r['winding']=str(mp.fsum(ph)/(2*mp.pi))
        else:
            job=refined_job(row['job'],hd,dps);r['refined_job']=job;T=Transform(job['host'],job['remove'],job['insert'],hd,dps)
            if row['kind']=='root':
                w=root_refine(T,dec(row['root']),dps);r.update(root=enc(w),native_residual=str(abs(T.val(w,False))));checks=[]
                for sh in ['.15','-.1']:
                    I=Independent(T,hd,sh);iv,id=I.val(w);checks.append(dict(shift=sh,residual=str(abs(iv)),inferred_root_error=str(abs(iv/id))))
                r['independent_checks']=checks
                if not job['remove']:
                    mp.mp.dps=dps+20;v=inserted_completion(job,w)/T.mass;mp.mp.dps=dps;r['completion_operator_residual']=str(abs(v));r['completion_operator_root_error']=str(abs(v/T.val(w)[1]))
            else:
                U=T;T=Transform('D',hden=hd,dps=dps);x=dec(row['root'])
                for k in range(20):
                    a=jets(T,x);b=jets(U,x);W=a[0]*b[1]-a[1]*b[0];dW=a[0]*b[2]-a[2]*b[0];step=W/dW
                    if abs(step)>1:step/=abs(step)
                    x-=step
                    if abs(step)<mp.mpf(10)**(-dps+40):break
                a=jets(T,x);b=jets(U,x);lam=mp.re(-a[0]/(b[0]-a[0]));gain=mp.re(-2*(b[0]-a[0])/((1-lam)*a[2]+lam*b[2]));assert 0<lam<1
                r.update(w=enc(x),lambda_value=str(lam),gain=str(gain));IT=Independent(T,hd,'.15');IU=Independent(U,hd,'.15');at=IT.val(x);bu=IU.val(x);r['independent_fold_F']=str(abs((1-lam)*at[0]+lam*bu[0]));r['independent_fold_D']=str(abs((1-lam)*at[1]+lam*bu[1]));delta=min(mp.mpf('.01'),lam/4,(1-lam)/4);branches=[]
                for side in [-1,1]:
                    ll=lam+side*delta
                    for sign in [-1,1]:
                        w=x+sign*mp.sqrt(mp.mpc(gain*side*delta))
                        for k in range(30):
                            a=jets(T,w);b=jets(U,w);v=(1-ll)*a[0]+ll*b[0];dv=(1-ll)*a[1]+ll*b[1];st=v/dv;w-=st
                            if abs(st)<mp.mpf(10)**(-dps+40):break
                        aa=IT.val(w);bb=IU.val(w);v=(1-ll)*aa[0]+ll*bb[0];dv=(1-ll)*aa[1]+ll*bb[1];branches.append(dict(lambda_value=str(ll),root=enc(w),independent_residual=str(abs(v)),inferred_root_error=str(abs(v/dv))))
                r['branches']=branches
        r['status']='ok'
    except Exception as e:r.update(status='error',error=repr(e))
    r['seconds']=time.monotonic()-start;save('check-%d-%d.json'%(row['id'],dps),r);return r
if __name__=='__main__':
    rows=[];start=time.monotonic();tasks=[(r,p) for r in json.loads(Path('validation-jobs.json').read_text()) for p in [100,160]]
    with ProcessPoolExecutor(max_workers=14) as ex:
        for f in as_completed([ex.submit(work,t) for t in tasks]):
            r=f.result();rows.append(r);save('summary.json',dict(planned=len(tasks),rows=rows,seconds=time.monotonic()-start));print(r['row']['id'],r['dps'],r['status'],flush=True)
