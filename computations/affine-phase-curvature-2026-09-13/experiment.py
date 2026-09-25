import concurrent.futures as cf
import json,os,time
from pathlib import Path
import mpmath as mp

DEADLINE=float(os.environ['CAMPAIGN_DEADLINE'])
ZEROS={int(a):b for a,b in (l.split() for l in Path('zeros.tsv').read_text().splitlines() if not l.startswith('#'))}
CHARS={4:[0,1,0,-1],5:[0,1,-1,-1,1]}

def budget():
    if time.monotonic()>DEADLINE-5:raise TimeoutError('family compute deadline')

def enc(z):return [mp.nstr(mp.re(z),mp.mp.dps),mp.nstr(mp.im(z),mp.mp.dps)]
def cc(z):return mp.mpc(*z)

def L(s,q):
    budget()
    if q==1:return mp.zeta(s)
    return mp.power(q,-s)*sum(CHARS[q][r]*mp.zeta(s,mp.mpf(r)/q) for r in range(1,q) if CHARS[q][r])

def positions(n):
    z=mp.mpf(ZEROS[n]);right=mp.mpf(ZEROS[n+1])-z
    left=z-mp.mpf(ZEROS[n-1]) if n>1 else right
    h=mp.sqrt(left*right)/4;mid=z+right/2
    return h,[z-h,z,z+h,mid-h,mid,mid+h]

def task(job):
    start=time.monotonic();n,q,dps=job;mp.mp.dps=dps
    out=dict(kind='sample',n=n,q=q,dps=dps)
    try:
        h,tt=positions(n);rows=[]
        for t in tt:
            vv={k:L(mp.mpc('.25',mp.mpf(k)*t/2),q) for k in [1,3,5,7]}
            if min(map(abs,vv.values()))<mp.mpf('1e-35'):raise ArithmeticError('near-zero phase normalization')
            u={k:v/abs(v) for k,v in vv.items()}
            r=mp.re(u[5]*u[1]*mp.conj(u[3])**2)
            ctrl=mp.re(u[7]*u[1]*mp.conj(u[3])**2)
            rows.append(dict(t=mp.nstr(t,dps),values={str(k):enc(v) for k,v in vv.items()},R=mp.nstr(r,dps),N=mp.nstr(ctrl,dps)))
        contrasts={}
        for name in ['R','N']:
            x=[mp.mpf(r[name]) for r in rows]
            contrasts[name]=mp.nstr(x[1]-(x[0]+x[2])/2-x[4]+(x[3]+x[5])/2,dps)
        out.update(h=mp.nstr(h,dps),rows=rows,contrasts=contrasts)
    except Exception as e:out['error']=str(e)[:200]
    out['seconds']=time.monotonic()-start
    return out

def hurwitz_em(s,a,N,M):
    budget();v=sum(mp.power(n+a,-s) for n in range(N));b=N+a
    v+=mp.power(b,1-s)/(s-1)+mp.power(b,-s)/2
    rising=mp.mpc(1);prev=0
    for k in range(1,M+1):
        for j in range(prev,2*k-1):rising*=s+j
        prev=2*k-1
        v+=mp.bernoulli(2*k)/mp.factorial(2*k)*rising*mp.power(b,-s-2*k+1)
    return v

def independent(job):
    start=time.monotonic();n,q,k=job;mp.mp.dps=190
    out=dict(kind='independent',n=n,q=q,k=k)
    try:
        s=mp.mpc('.25',mp.mpf(k)*mp.mpf(ZEROS[n])/2);N=max(512,int(2*abs(s.imag))+512)
        def calc(N,M):
            if q==1:return hurwitz_em(s,mp.mpf(1),N,M)
            return mp.power(q,-s)*sum(CHARS[q][r]*hurwitz_em(s,mp.mpf(r)/q,N,M) for r in range(1,q) if CHARS[q][r])
        a=calc(N,160);b=calc(N+64,176);ref=L(s,q)
        out.update(N=N,M=160,value=enc(a),scaled_error=mp.nstr(abs(a-ref)/max(1,abs(ref)),190),refinement=mp.nstr(abs(a-b)/max(1,abs(b)),190))
    except Exception as e:out['error']=str(e)[:200]
    out['seconds']=time.monotonic()-start;return out

def emit(row):
    with open('results.jsonl','a') as f:f.write(json.dumps(row)+'\n')
    print(json.dumps({k:v for k,v in row.items() if k not in ['rows','value']}),flush=True)

def gate(rows,indices):
    if len(rows)!=192 or any('error' in r for r in rows):return dict(passed=False,reason='incomplete/error stage')
    means={};blocks={}
    for q in [1,4,5]:
        rr=sorted([r for r in rows if r['q']==q],key=lambda r:r['n'])
        for name in ['R','N']:
            vals=[float(r['contrasts'][name]) for r in rr]
            means[str(q)+name]=sum(vals)/64
            blocks[str(q)+name]=[sum(vals[j:j+8])/8 for j in range(0,64,8)]
    value=means['1R'];consistent=sum(x*value>0 for x in blocks['1R'])
    passed=abs(value)>=.05 and consistent>=6 and all(abs(value)>=2*abs(means[k]) for k in ['1N','4R','5R'])
    return dict(passed=passed,means=means,blocks=blocks,consistent=consistent,indices=[indices[0],indices[-1]])

def main():
    started=time.monotonic();all_selected=[];stage_sign=None
    with cf.ProcessPoolExecutor(max_workers=14) as pool:
        pilot_jobs=[(n,q,50) for n in [1,64] for q in [1,4,5]];pilot=[]
        for f in cf.as_completed([pool.submit(task,j) for j in pilot_jobs]):
            row=f.result();emit(row);pilot.append(row)
        estimate=max(r['seconds'] for r in pilot)*192/14
        emit(dict(kind='pilot',estimated_stage_seconds=estimate))
        if estimate>150:raise RuntimeError('pilot rejected cost; preserve partial')
        for indices in [list(range(1,65)),list(range(65,129)),list(range(257,321))]:
            rows=list(pilot) if indices[0]==1 else []
            present={(r['n'],r['q']) for r in rows}
            jobs=[(n,q,50) for n in indices for q in [1,4,5] if (n,q) not in present]
            for f in cf.as_completed([pool.submit(task,j) for j in jobs]):
                row=f.result();emit(row);rows.append(row)
            g=gate(rows,indices);g['kind']='stage_gate';emit(g)
            if all('error' not in r for r in rows):
                for q in [1,4,5]:
                    r=max((r for r in rows if r['q']==q),key=lambda r:abs(float(r['contrasts']['R'])))
                    all_selected.append((r['n'],q))
            if not g['passed']:break
            if stage_sign is not None and stage_sign*g['means']['1R']<=0:
                emit(dict(kind='retired',reason='sign reversal'));break
            stage_sign=g['means']['1R']
        emit(dict(kind='challenge_selection',selected=all_selected))
        jobs=[(n,q,d) for n,q in all_selected for d in [100,160]]
        for f in cf.as_completed([pool.submit(task,j) for j in jobs]):emit(f.result())
        jobs=[(n,q,k) for n,q in all_selected for k in [1,3,5,7]]
        for f in cf.as_completed([pool.submit(independent,j) for j in jobs]):emit(f.result())
    emit(dict(kind='complete',seconds=time.monotonic()-started))

if __name__=='__main__':main()
