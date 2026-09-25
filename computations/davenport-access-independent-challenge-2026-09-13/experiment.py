from independent import *
from concurrent.futures import ProcessPoolExecutor,as_completed

def work(job):
    label,kind,dps=job;configure(dps);start=time.monotonic();r=dict(label=label,kind=kind,dps=dps)
    try:
        s=dec(catalog()[label])
        for _ in range(7):s-=D(s)/D(s,1)
        r['start']=enc(s);r['start_check']=check(s,mp.mpf(0),dps)
        isaccess=kind.startswith('access')
        fun=(lambda u:access(int(kind.split('_')[-1])*mp.pi/3,u)) if isaccess else (lambda u:target(kind,u))
        end,info=c.lift(s,fun,.003 if isaccess else .008)
        r.update(endpoint=enc(end),**info)
        if isaccess:
            row=min(info['path'],key=lambda rr:abs(mp.mpf(rr[0])*48-32));s32=mp.mpc(row[1],row[2]);slope=(mp.re(end)-mp.re(s32))/(48-mp.mpf(row[0])*48);delta=abs(end-s32)
            cat='escape_like' if mp.re(end)>40 and abs(slope-1)<.02 else ('finite_like' if delta<mp.mpf('1e-6') else 'unresolved')
            r.update(category=cat,late_real_slope=str(slope),late_displacement=str(delta))
            if cat=='finite_like':
                z=end
                for _ in range(8):z-=(D(z)-1)/D(z,1)
                r.update(finite_one_point=enc(z),finite_one_check=check(z,mp.mpf(1),dps))
        else:r['endpoint_label']=classify(end)
        checks=[]
        for ix in sorted(set(round(j*(len(info['path'])-1)/6) for j in range(7))):
            row=info['path'][ix];u=mp.mpf(row[0]);sp=mp.mpc(row[1],row[2]);configure(dps+60);w=fun(u);configure(dps)
            checks.append(dict(u=str(u),**check(sp,w,dps,relative=isaccess)))
        r.update(status='ok',checks=checks)
    except Exception as e:r.update(status='error',error=repr(e))
    r['seconds']=time.monotonic()-start;save('check-%s-%s-%d.json'%(label,kind,dps),r);return {k:v for k,v in r.items() if k!='path'}
if __name__=='__main__':
    choices=[('off_left','access_0'),('off_right','access_0'),('off_left','circle'),('off_right','circle'),('off_right','access_-1'),('off_right','access_1'),('off_left','access_1')]
    jobs=[(a,k,dps) for a,k in choices for dps in [100,160]];start=time.monotonic();rows=[]
    with ProcessPoolExecutor(max_workers=14) as ex:
        for f in as_completed([ex.submit(work,j) for j in jobs]):
            r=f.result();rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print(r['label'],r['kind'],r['dps'],r['status'],flush=True)
