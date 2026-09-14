from independent import *
from concurrent.futures import ProcessPoolExecutor,as_completed

def work(job):
    label,dps,epsstr=job;configure(dps);start=time.monotonic();r=dict(label=label,dps=dps,epsilon=epsstr)
    try:
        s=dec(json.loads(Path('critical-seeds.json').read_text())[label]['critical_point'])
        for _ in range(8):s-=D(s,1)/D(s,2)
        cv=D(s);r.update(critical_point=enc(s),critical_value=enc(cv),critical_check=check(s,cv,dps,derivative=True));eps=mp.mpf(epsstr);delta=mp.sqrt(-2*cv*eps/D(s,2));branches=[]
        for sign in [-1,1]:
            p=s+sign*delta;w=cv*(1-eps)
            for _ in range(10):p-=(D(p)-w)/D(p,1)
            end,info=c.lift(p,lambda u:cv*(1-eps)*(1-u),.008)
            checks=[]
            for ix in sorted(set(round(j*(len(info['path'])-1)/6) for j in range(7))):
                row=info['path'][ix];u=mp.mpf(row[0]);sp=mp.mpc(row[1],row[2]);configure(dps+60);w=cv*(1-eps)*(1-u);configure(dps)
                checks.append(dict(u=str(u),**check(sp,w,dps)))
            branches.append(dict(sign=sign,endpoint=enc(end),endpoint_label=classify(end),checks=checks,**info))
            save('partial-%s-%d-%s.json'%(label,dps,epsstr),dict(branches=branches))
        r.update(status='ok',branches=branches)
    except Exception as e:r.update(status='error',error=repr(e))
    r['seconds']=time.monotonic()-start;save('check-%s-%d-%s.json'%(label,dps,epsstr),r)
    out={k:v for k,v in r.items() if k!='branches'}
    if 'branches'in r:out.update(endpoints=[x['endpoint_label'] for x in r['branches']],checks=[z for x in r['branches'] for z in x['checks']])
    return out
if __name__=='__main__':
    seeds=json.loads(Path('critical-seeds.json').read_text());jobs=[(k,dps,ep) for k in seeds for dps,ep in [(100,'1e-5'),(160,'1e-7')]]
    # The off-line-pair incidence additionally crosses both departure scales at both precisions.
    jobs += [('off_pair',100,'1e-7'),('off_pair',160,'1e-5')];start=time.monotonic();rows=[]
    with ProcessPoolExecutor(max_workers=14) as ex:
        for f in as_completed([ex.submit(work,j) for j in jobs]):
            r=f.result();rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print(r['label'],r['dps'],r['epsilon'],r['status'],flush=True)
