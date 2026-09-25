"""Compare code support with the normalized density of an encoded mixture."""
from metric import *


def tensor_summary(g,y):
    q=mp.matrix(2,2)
    for i in range(2):
        for j in range(2):
            q[i,j]=g[i,j]-g[i,2]*g[2,j]/g[2,2]
    return dict(metric=matenc(g),rotation_quotient=matenc(q),
                ratio=str(q[0,0]/q[1,1]),cross=str(q[0,1]/mp.sqrt(q[0,0]*q[1,1])),
                scale=str(y*y*mp.sqrt(mp.det(q))),
                metric_eigenvalues=[str(v) for v in mp.eigsy(g,eigvals_only=True)])


def compare(job):
    d=int(job['dim']);x,y,delta=[mp.mpf(job[k]) for k in ['x','y','delta']]
    h=mp.mpf(job.get('h','1e-6'));N=int(job['N']);method=job.get('method','recurrence')
    pts=[]
    for i in range(3):
        for sign in [-1,1]:
            z=[x,y,mp.mpf(0)];z[i]+=sign*h
            pts.append(Code(*z,delta,d,N))
    grams=[overlap(a,a,method) for a in pts]
    invs=[G**-1 for G in grams]
    tr=[mp.re(trace(G)) for G in grams]
    pair={}
    def reads(a,b):
        if a==b:return mp.mpf(d),mp.mpf(1)
        key=tuple(sorted((a,b)))
        if key not in pair:
            a,b=key;X=overlap(pts[a],pts[b],method)
            pp=mp.re(trace(invs[a]*X*invs[b]*X.H))
            ev=mp.eighe(X.H*X,eigvals_only=True)
            threshold=mp.mpf(10)**(-mp.mp.dps+15)*max(abs(v) for v in ev)
            assert min(ev)>=-threshold
            rootfid=mp.fsum(mp.sqrt(max(v,0)) for v in ev)/mp.sqrt(tr[a]*tr[b])
            pair[key]=(pp,rootfid)
        return pair[key]
    mats=[]
    for channel,denom in [(0,8),(1,4)]:
        g=mp.matrix(3,3)
        for i in range(3):
            for j in range(i,3):
                a=reads(2*i+1,2*j+1)[channel]-reads(2*i+1,2*j)[channel]
                a-=reads(2*i,2*j+1)[channel]-reads(2*i,2*j)[channel]
                g[i,j]=g[j,i]=a/(denom*h*h)
        mats.append(tensor_summary(g,y))
    centre=Code(x,y,mp.mpf(0),delta,d,N);G=overlap(centre,centre,method)
    ev=mp.eighe(G,eigvals_only=True);s=mp.fsum(ev)
    return dict(projector=mats[0],density=mats[1],gram=matenc(G),
                gram_eigenvalues=[str(v) for v in ev],
                gram_condition=str(max(ev)/min(ev)),
                density_eigenvalues=[str(v/s) for v in ev],
                purity=str(mp.fsum((v/s)**2 for v in ev)),
                pair_readers={str(k):[str(z) for z in v] for k,v in pair.items()},
                mixed_interaction=str(mp.mpf(mats[1]['ratio'])/mp.mpf(mats[0]['ratio'])))


def work_density(job):
    mp.mp.dps=int(job.get('dps',50));start=time.monotonic();row=dict(job=job)
    try:row.update(compare(job));row['status']='ok'
    except Exception as e:row.update(status='error',error=repr(e))
    row['seconds']=time.monotonic()-start;save('case-'+str(job['id'])+'.json',row);return row


if __name__=='__main__':
    jobs=json.loads(Path('jobs.json').read_text());start=time.monotonic();rows=[]
    r=work_density(jobs[0]);rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print('pilot',r['status'],r['seconds'],flush=True)
    if r['status']!='ok' or r['seconds']>75:raise SystemExit('pilot failed or oversized')
    with ProcessPoolExecutor(max_workers=14) as ex:
        for f in as_completed([ex.submit(work_density,j) for j in jobs[1:]]):
            r=f.result();rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print(r['job']['id'],r['status'],r.get('density',{}).get('ratio'),r['seconds'],flush=True)
