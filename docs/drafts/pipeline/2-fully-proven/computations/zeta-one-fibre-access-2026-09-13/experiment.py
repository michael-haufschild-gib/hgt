from common import *
from concurrent.futures import ProcessPoolExecutor,as_completed

def path(angle,u):return 1-mp.exp(-48*mp.log(2)*u+1j*angle*min(12*u,1))
def work(job):
    n,angle_label=job;mp.mp.dps=80;angle=angle_label*mp.pi/3;start=time.monotonic();r=dict(n=n,angle_thirds_pi=angle_label,dps=80)
    try:
        end,info=lift(zeros()[n],lambda u:path(angle,u),.004)
        marks=[]
        for R in [8,16,32,48]:
            row=min(info['path'],key=lambda row:abs(mp.mpf(row[0])*48-R));marks.append(dict(R=str(mp.mpf(row[0])*48),s=[row[1],row[2]],residual=row[3]))
        s32=dec(marks[2]['s']);diff=abs(end-s32);slope=(mp.re(end)-mp.re(s32))/(48-mp.mpf(marks[2]['R']))
        category='unresolved'
        if mp.re(end)>40 and abs(slope-1)<mp.mpf('.02'):category='escape_like'
        elif diff<mp.mpf('1e-6'):category='finite_like'
        r.update(status='ok',endpoint=enc(end),category=category,late_displacement=str(diff),late_real_slope=str(slope),marks=marks,**info)
        if category=='finite_like':
            s=end
            for _ in range(8):s-=(zeta(s)-1)/zeta(s,1)
            r['finite_one_point']=enc(s);r['finite_one_residual']=str(abs(zeta(s)-1))
    except Exception as e:r.update(status='error',error=repr(e))
    r['seconds']=time.monotonic()-start;save('access-%03d-%d.json'%(n,angle_label),r)
    return {k:v for k,v in r.items() if k!='path'}
if __name__=='__main__':
    jobs=[(n,a) for n in range(1,65) for a in [0,-1,1]];rows=[];start=time.monotonic()
    with ProcessPoolExecutor(max_workers=14) as ex:
        pilots=[jobs[0],jobs[15]];pilot=list(ex.map(work,pilots));rows.extend(pilot)
        save('pilot.json',dict(rows=pilot,seconds=time.monotonic()-start,estimated_worker_wall=max(r['seconds'] for r in pilot)*len(jobs)/14))
        for f in as_completed([ex.submit(work,j) for j in jobs if j not in pilots]):
            r=f.result();rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print(r['n'],r['angle_thirds_pi'],r.get('category',r.get('error')),flush=True)
