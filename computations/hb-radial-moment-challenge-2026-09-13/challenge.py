import concurrent.futures as cf
import json
import time
import mpmath as mp
import moment as m

def locate(job):
    start=time.monotonic();branch,side,lo,hi=job;mp.mp.dps=100
    out=dict(kind='locate',job=job,roots=[],rejected=[],failures=[])
    try:
        c=m.contour(branch,side,lo,hi,48);out['contour']=c
        if abs(float(c['winding']))>.5 or float(c['max_phase_step'])>2:
            nearest=min(c['samples'],key=lambda r:abs(m.cc(r['value'])))
            seeds=[m.cc(nearest['rho']),mp.mpc('.5',(mp.mpf(lo)+mp.mpf(hi))/2)]
            for z in seeds:
                try:
                    r=mp.findroot(lambda x:m.value(x,branch,side),(z,z+mp.mpf('.001')),tol=mp.mpf('1e-90'),maxsteps=60)
                    row=dict(rho=m.cstr(r),residual=mp.nstr(abs(m.value(r,branch,side)),100))
                    if mp.mpf('.01')<r.real<mp.mpf('.99') and mp.mpf('.1')<r.imag<16:
                        out['roots'].append(row)
                    else:out['rejected'].append(row)
                except Exception as e:out['failures'].append(str(e)[:200])
    except Exception as e:out['error']=str(e)[:200]
    out['seconds']=time.monotonic()-start
    return out

def validate(job):
    out=m.validate(job)
    if 'error' not in out:
        mp.mp.dps=160;r=m.cc(out['precision'][-1]['rho'])
        out['all_channels']=[dict(branch=b,side=s,normalized=m.cstr(m.value(r,b,s))) for b in [False,True] for s in [False,True]]
    return out

def emit(out):
    with open('results.jsonl','a') as f:f.write(json.dumps(out)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ['contour','precision','all_channels']}),flush=True)

def main():
    start=time.monotonic();mp.mp.dps=100
    jobs=[(b,b,str(mp.mpf('.1')+mp.mpf('15.9')*i/16),str(mp.mpf('.1')+mp.mpf('15.9')*(i+1)/16)) for b in [False,True] for i in range(16)]
    rows=[]
    with cf.ProcessPoolExecutor(max_workers=14) as pool:
        futures=[pool.submit(locate,job) for job in jobs]
        for f in cf.as_completed(futures):
            row=f.result();emit(row);rows.append(row)
        candidates=[]
        for row in sorted(rows,key=lambda r:jobs.index(tuple(r['job']))):
            for r in row['roots']:
                candidate=(row['job'][0],row['job'][1],r['rho'])
                if not any(x[:2]==candidate[:2] and abs(m.cc(x[2])-m.cc(candidate[2]))<mp.mpf('1e-40') for x in candidates):candidates.append(candidate)
        emit(dict(kind='candidates',candidates=candidates))
        futures=[pool.submit(validate,job) for job in candidates[:8]]
        for f in cf.as_completed(futures):emit(f.result())
        futures=[pool.submit(m.contour,b,b,'.1','16',192) for b in [False,True]]
        for b,f in zip([False,True],futures):emit(dict(kind='full_contour',branch=b,side=b,contour=f.result()))
    emit(dict(kind='complete',seconds=time.monotonic()-start))

if __name__=='__main__':main()
