from density import *

def work_phase(job):
    mp.mp.dps=int(job.get('dps',50));start=time.monotonic();row=dict(job=job)
    Code.phase_a=mp.mpf(job['a']);Code.phase_b=mp.mpf(job['b'])
    try:
        row.update(compare(job))
        x,y,delta=[mp.mpf(job[k]) for k in ['x','y','delta']];d=int(job['dim']);N=int(job['N']);method=job.get('method','recurrence')
        base=Code(x,y,0,delta,d,N);G=overlap(base,base,method)
        controls={}
        for label,point in [('T',(x+1,y,mp.mpf(0))),('S',(-x/(x*x+y*y),y/(x*x+y*y),-mp.arg(x+1j*y)))]:
            other=Code(*point,delta,d,N);B=overlap(other,other,method);X=overlap(base,other,method)
            f=mp.fsum(mp.svd(X,compute_uv=False))/mp.sqrt(mp.re(trace(G)*trace(B)))
            controls[label]=str(f)
        invariant=(d%2==0 and job['a']=='0' and job['b']=='0') or (d%2==1 and job['a']=='.5' and job['b']=='.5')
        if invariant:
            for z in controls.values():assert abs(mp.mpf(z)-1)<mp.mpf('1e-20')
        row.update(modular_generator_root_fidelities=controls,expected_invariant_section=invariant,status='ok')
    except Exception as e:row.update(status='error',error=repr(e))
    row['seconds']=time.monotonic()-start;save('case-'+str(job['id'])+'.json',row);return row

if __name__=='__main__':
    jobs=json.loads(Path('jobs.json').read_text());start=time.monotonic();rows=[]
    r=work_phase(jobs[0]);rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print('pilot',r['status'],r['seconds'],flush=True)
    if r['status']!='ok' or r['seconds']>75:raise SystemExit('pilot failed or oversized')
    with ProcessPoolExecutor(max_workers=14) as ex:
        for f in as_completed([ex.submit(work_phase,j) for j in jobs[1:]]):
            r=f.result();rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print(r['job']['id'],r['status'],r.get('density',{}).get('ratio'),r.get('error',''),flush=True)
