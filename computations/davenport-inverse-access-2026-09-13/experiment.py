from carrier import *
from concurrent.futures import ProcessPoolExecutor,as_completed

def work(job):
    label,kind=job;configure(60);start=time.monotonic();r=dict(label=label,kind=kind,dps=60)
    try:
        s=dec(catalog()[label]);
        for _ in range(4):s-=D(s)/D(s,1)
        if kind.startswith('access'):
            ang=int(kind.split('_')[-1]);fun=lambda u:access(ang*mp.pi/3,u);step=.004
        else:fun=lambda u:target(kind,u);step=.018
        end,info=c.lift(s,fun,step)
        r.update(status='ok',endpoint=enc(end),**info)
        if kind.startswith('access'):
            row=min(info['path'],key=lambda rr:abs(mp.mpf(rr[0])*48-32));s32=mp.mpc(row[1],row[2]);slope=(mp.re(end)-mp.re(s32))/(48-mp.mpf(row[0])*48);delta=abs(end-s32)
            cat='escape_like' if mp.re(end)>40 and abs(slope-1)<.02 else ('finite_like' if delta<mp.mpf('1e-6') else 'unresolved')
            r.update(category=cat,late_real_slope=str(slope),late_displacement=str(delta))
            if cat=='finite_like':
                z=end
                for _ in range(8):z-=(D(z)-1)/D(z,1)
                r.update(finite_one_point=enc(z),finite_one_residual=str(abs(D(z)-1)))
        else:r['endpoint_label']=classify(end)
    except Exception as e:r.update(status='error',error=repr(e))
    r['seconds']=time.monotonic()-start;save('path-%s-%s.json'%(label,kind),r)
    return {k:v for k,v in r.items() if k!='path'}
if __name__=='__main__':
    start=time.monotonic();zz=prepare();jobs=[(label,kind) for label in zz for kind in ['circle','reverse','small','flat','tall','access_0','access_-1','access_1']];rows=[]
    with ProcessPoolExecutor(max_workers=14) as ex:
        pilots=[('off_right','circle'),('off_left','access_0')];pp=list(ex.map(work,pilots));rows.extend(pp);save('pilot.json',dict(rows=pp,preparation_plus_pilot_seconds=time.monotonic()-start))
        for f in as_completed([ex.submit(work,j) for j in jobs if j not in pilots]):
            r=f.result();rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print(r['label'],r['kind'],r.get('category',r.get('endpoint_label',r.get('error'))),flush=True)
