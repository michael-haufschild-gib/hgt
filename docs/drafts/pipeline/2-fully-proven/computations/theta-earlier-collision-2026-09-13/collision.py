import json
import multiprocessing as mp
import os
import time
from pathlib import Path
import mpmath as m
import deformation as d
import discriminant as e

def setup(direction,params):
    dx,dy=direction;norm=m.sqrt(dx*dx+dy*dy);a=m.mpf(dx)/norm;b=m.mpf(dy)/norm
    hs=[{int(k):m.mpf(v) for k,v in params[n].items()} for n in ['h1','h2','h12']]
    shifts={0}
    for h in hs:
        for k in h:shifts.update([k,-k])
    cache={}
    def pieces(t,lam,kappa):
        if not 2<t<180:raise ValueError('height left admitted region')
        key=m.nstr(t,m.mp.dps+3)
        if key not in cache:
            vals={k:d.xi_jets(t+k) for k in shifts}
            H=[tuple(sum(c*(vals[k][j]+vals[-k][j])/2 for k,c in h.items()) for j in range(3)) for h in hs]
            cache[key]=(vals[0],tuple(a*H[0][j]+b*H[1][j] for j in range(3)),tuple(a*b*H[2][j] for j in range(3)))
        X,D,W=cache[key]
        scale=m.exp(-m.pi*t/4)*(1+t*t)**m.mpf('.875')
        ld=-m.pi/4+m.mpf('1.75')*t/(1+t*t)
        F=[(X[j]+lam*D[j]+kappa*lam*lam*W[j])/scale for j in range(3)]
        Fl=[(D[j]+2*kappa*lam*W[j])/scale for j in range(2)]
        Fk=[lam*lam*W[j]/scale for j in range(2)]
        J=m.matrix([[F[1]-ld*F[0],Fl[0]],[F[2]-ld*F[1],Fl[1]]])
        bound=abs(lam*a)+abs(lam*b)+abs(kappa*lam*lam*a*b)*m.mpf(params['h12_l1'])
        return F,J,Fk,bound
    return pieces

def track(args):
    seed,params=args;begin=time.monotonic();m.mp.dps=50
    fun=setup(seed['direction'],params)
    t=m.mpf(seed['t']);lam=m.mpf(seed['lam']);k=m.mpf(seed['interaction'])
    target=1-k;sign=1 if target>k else -1;step=m.mpf('.05')
    rows=[];failures=[];stopped=None
    for _ in range(121):
        F,J,Fk,bound=fun(t,lam,k)
        rows.append(dict(kappa=m.nstr(k,50),t=m.nstr(t,50),lam=m.nstr(lam,50),
                         residual=m.nstr(max(abs(v) for v in F[:2]),30),jacobian_det=m.nstr(m.det(J),30),positivity_bound=m.nstr(bound,30)))
        if k==target:break
        if len(rows)>=120:stopped='point cap';break
        if not lam>0 or not bound<1:stopped='left positive-multiplier region';break
        while True:
            knew=k+sign*min(step,abs(target-k));delta=knew-k
            try:
                velocity=m.lu_solve(J,-m.matrix(Fk))
                guess=(t+delta*velocity[0],lam+delta*velocity[1])
                sol=m.findroot(lambda tt,ll:tuple(fun(tt,ll,knew)[0][:2]),guess,
                               J=lambda tt,ll:fun(tt,ll,knew)[1],tol=m.mpf('1e-35'),maxsteps=14,verify=True)
                if abs(sol[0]-t)>m.mpf('.5') or abs(sol[1]-lam)>m.mpf('.03'):raise ValueError('correction jump')
                t,lam=sol;k=knew;step=min(m.mpf('.05'),step*2);break
            except Exception as ex:
                failures.append(dict(kappa=m.nstr(knew,30),error=str(ex)[:100]));step/=2
                if step<m.mpf(1)/640:stopped='minimum step; no branch exclusion';break
        if stopped:break
    return dict(seed=seed,points=rows,failures=failures,stop_reason=stopped,
                reached_endpoint=bool(k==target),seconds=time.monotonic()-begin)

def endpoint_refine(args):
    row,dps,params=args;m.mp.dps=dps;start=time.monotonic()
    last=row['points'][-1];seed=row['seed'];k=m.mpf(last['kappa'])
    fun=setup(seed['direction'],params)
    root=m.findroot(lambda t,l:tuple(fun(t,l,k)[0][:2]),(m.mpf(last['t']),m.mpf(last['lam'])),
                    J=lambda t,l:fun(t,l,k)[1],tol=m.mpf(10)**(-dps+15),maxsteps=15,verify=True)
    F,J,Fk,bound=fun(root[0],root[1],k)
    return dict(n=seed['n'],origin_interaction=seed['interaction'],direction=seed['direction'],interaction=int(k),dps=dps,
                t=m.nstr(root[0],dps),lam=m.nstr(root[1],dps),residual=[m.nstr(v,dps) for v in F[:2]],
                positivity_bound=m.nstr(bound,dps),seconds=time.monotonic()-start)

def anchor(args):
    row,params=args
    m.mp.dps=190
    shifted=dict(row);shifted['t']=m.nstr(m.mpf(row['t'])+m.mpf('.125'),190)
    result=e.source_check((shifted,params));result['offset']='.125'
    return result

if __name__=='__main__':
    start=time.monotonic();params=d.prepare(70)
    seeds=[json.loads(s) for s in Path('seeds.jsonl').read_text().splitlines() if json.loads(s)['dps']==160]
    seeds.sort(key=lambda r:(r['n'],r['interaction']))
    rows=[]
    with mp.Pool(14) as pool,open('tracks.jsonl','w',buffering=1) as out:
        for group in [seeds[:1],seeds[1:]]:
            durations=[]
            for row in pool.imap_unordered(track,[(seed,params) for seed in group]):
                rows.append(row);durations.append(row['seconds']);out.write(json.dumps(row)+'\n')
            print('tracks',len(rows),'elapsed',time.monotonic()-start,flush=True)
            if len(rows)==1 and 3*max(durations)>float(os.environ['CAMPAIGN_DEADLINE'])-time.monotonic():
                print('pilot rejects remaining tracks',flush=True);break
        p100=d.prepare(120);p160=d.prepare(180)
        Path('parameters.json').write_text(json.dumps({'70':params,'120':p100,'180':p160},indent=2)+'\n')
        return_seeds=[]
        for row in rows:
            if row['reached_endpoint']:
                last=row['points'][-1]
                return_seeds.append(dict(n=row['seed']['n'],direction=row['seed']['direction'],interaction=int(m.mpf(last['kappa'])),
                                         t=last['t'],lam=last['lam'],original_seed=row['seed']))
        with open('return-tracks.jsonl','w',buffering=1) as back:
            for row in pool.imap_unordered(track,[(seed,params) for seed in return_seeds]):
                if row['reached_endpoint']:
                    original=row['seed']['original_seed'];last=row['points'][-1]
                    row['return_errors']={key:m.nstr(abs(m.mpf(last[key])-m.mpf(original[key])),40) for key in ['t','lam']}
                back.write(json.dumps(row)+'\n')
        print('return checks finished',time.monotonic()-start,flush=True)
        validated=[]
        with open('validation.jsonl','w',buffering=1) as out2:
            for row in pool.imap_unordered(endpoint_refine,[(r,prec,p) for r in rows if r['reached_endpoint'] for prec,p in [(100,p100),(160,p160)]]):
                out2.write(json.dumps(row)+'\n');validated.append(row)
        print('refined',len(validated),'elapsed',time.monotonic()-start,flush=True)
        with open('source-validation.jsonl','w',buffering=1) as out3:
            for row in pool.imap_unordered(anchor,[(r,p160) for r in validated if r['dps']==160]):out3.write(json.dumps(row)+'\n')
    Path('summary.json').write_text(json.dumps(dict(seconds=time.monotonic()-start),indent=2)+'\n')
