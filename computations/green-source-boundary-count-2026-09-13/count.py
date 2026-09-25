from green import *

def work(job):
    start=time.monotonic();r=dict(job=job,dps=80);checks=[]
    try:
        G=Green(job['host'],80,128);X=mp.mpf('2.6');Y=mp.mpf(job['Y']);corners=[-X-1j*Y,X-1j*Y,X+1j*Y,-X+1j*Y];prev=None
        for N in [512,1024,2048]:
            vals=[];ratios=[]
            for side in range(4):
                a=corners[side];bb=corners[(side+1)%4]
                for j in range(N):
                    budget();z=a+(bb-a)*j/N;v,der,n=G.val(z,job['mode']);vals.append(v);ratios.append(abs(v)/n)
            phases=[mp.arg(vals[(j+1)%len(vals)]/vals[j]) for j in range(len(vals))];w=mp.fsum(phases)/(2*mp.pi);mx=max(abs(q) for q in phases)
            checks.append(dict(N_per_edge=N,winding=str(w),max_phase_step=str(mx),min_normalized_magnitude=str(min(ratios))))
            save('boundary-'+job['label']+'-'+str(N)+'.json',dict(job=job,values=[enc(v) for v in vals],check=checks[-1]))
            if prev is not None and abs(w-prev)<mp.mpf('1e-30') and mx<mp.mpf('.5'):break
            prev=w
        r.update(status='ok',numerically_resolved=bool(len(checks)>=2 and abs(mp.mpf(checks[-1]['winding'])-mp.mpf(checks[-2]['winding']))<mp.mpf('1e-30') and mp.mpf(checks[-1]['max_phase_step'])<mp.mpf('.5')))
    except Exception as e:r.update(status='error',error=repr(e))
    r.update(checks=checks,seconds=time.monotonic()-start);save('case-'+job['label']+'.json',r);return r
if __name__=='__main__':
    start=time.monotonic();pairs=[('R','.5'),('R','1.5'),('R','mixed'),('B4','mixed'),('L5','mixed'),('D','mixed')];jobs=[dict(host=h,mode=m,Y=y,label=h+'-'+m+'-'+y) for h,m in pairs for y in ['.7','.78','.784']];save('jobs.json',jobs);rows=[]
    with ProcessPoolExecutor(max_workers=14) as ex:
        for f in as_completed([ex.submit(work,j) for j in jobs]):
            r=f.result();rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print(r['job']['label'],r['status'],r['checks'][-1] if r['checks'] else r.get('error'),flush=True)
