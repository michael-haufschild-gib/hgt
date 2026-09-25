import json
import multiprocessing as mp
import os
import time
from pathlib import Path
import mpmath as m
import deformation as d
import control as c

THETA_JETS=d.xi_jets

def configure(q):
    c.CURRENT_Q=q
    d.xi_jets=THETA_JETS if q==0 else c.carrier_jets

def evaluator(q,direction,params):
    configure(q)
    dx,dy=direction;norm=m.sqrt(dx*dx+dy*dy);a=m.mpf(dx)/norm;b=m.mpf(dy)/norm
    hs=[{int(k):m.mpf(v) for k,v in params[n].items()} for n in ['h1','h2','h12']]
    shifts={0}
    for h in hs:
        for k in h:shifts.update([k,-k])
    cache={}
    def pieces(t):
        key=(m.mp.dps,m.nstr(t,m.mp.dps+3))
        if key in cache:return cache[key]
        vals={k:d.xi_jets(t+k) for k in shifts}
        scale=m.exp(-m.pi*t/4)*(1+t*t)**m.mpf('.875')
        X=[v/scale for v in vals[0]]
        hsvals=[[sum(v*(vals[k][j]+vals[-k][j])/2 for k,v in h.items())/scale for j in range(3)] for h in hs]
        D=[a*hsvals[0][j]+b*hsvals[1][j] for j in range(3)]
        W=[a*b*hsvals[2][j] for j in range(3)]
        cache[key]=(X,D,W);return X,D,W
    def data(t):
        X,D,W=pieces(t)
        A=X[0]*W[1]-X[1]*W[0];B=D[0]*W[1]-D[1]*W[0];C=X[0]*D[1]-X[1]*D[0]
        Ap=X[0]*W[2]-X[2]*W[0];Bp=D[0]*W[2]-D[2]*W[0];Cp=X[0]*D[2]-X[2]*D[0]
        lam=-A/B;kappa=B*C/(A*A)
        kp=(Bp*C+B*Cp-2*B*C*Ap/A)/(A*A)
        lp=-(Ap*B-A*Bp)/(B*B)
        F=[X[j]+lam*D[j]+kappa*lam*lam*W[j] for j in range(3)]
        Fl=D[0]+2*kappa*lam*W[0]
        bound=abs(lam*a)+abs(lam*b)+abs(kappa*lam*lam*a*b)*m.mpf(params['h12_l1'])
        return dict(lam=lam,kappa=kappa,kappa_prime=kp,lambda_prime=lp,F=F,F_lambda=Fl,positivity_bound=bound,A=A,B=B)
    return data,pieces

def encoded(values,dps):
    return {k:[m.nstr(v,dps) for v in value] if isinstance(value,list) else m.nstr(value,dps) for k,value in values.items()}

def scan(args):
    q,direction,interval,params=args;begin=time.monotonic();m.mp.dps=50
    data,_=evaluator(q,direction,params);lo,hi=map(m.mpf,interval)
    grid=[lo+(hi-lo)*j/64 for j in range(65)]
    vals=[data(t)['kappa_prime'] for t in grid];found=[];errors=[]
    for j in range(64):
        if vals[j]*vals[j+1]>=0:continue
        try:
            t=m.findroot(lambda t:data(t)['kappa_prime'],(grid[j],grid[j+1]),solver='anderson',tol=m.mpf('1e-35'),maxsteps=60,verify=True)
            if not grid[j]<=t<=grid[j+1]:raise ValueError('root left bracket')
            v=data(t)
            if max(abs(x) for x in v['F'][:2])>m.mpf('1e-25'):raise ValueError('original equations failed')
            found.append(dict(t=m.nstr(t,50),admitted=bool(0<v['kappa']<1 and v['lam']>0 and v['positivity_bound']<1),**encoded(v,50)))
        except Exception as ex:errors.append(str(ex)[:120])
    return dict(q=q,direction=direction,interval=interval,dps=50,roots=found,errors=errors,seconds=time.monotonic()-begin)

def refine(args):
    row,prec,params=args;begin=time.monotonic();m.mp.dps=prec
    data,_=evaluator(row['q'],row['direction'],params);t=m.mpf(row['t'])
    t=m.findroot(lambda t:data(t)['kappa_prime'],(t-m.mpf('1e-5'),t+m.mpf('1e-5')),tol=m.mpf(10)**(-prec+15),maxsteps=30,verify=True)
    vals=data(t);vals['kappa_second']=m.diff(lambda u:data(u)['kappa_prime'],t)
    return dict(q=row['q'],direction=row['direction'],interval=row['interval'],dps=prec,t=m.nstr(t,prec),**encoded(vals,prec),seconds=time.monotonic()-begin)

def integral_check(args):
    item,params,offset=args;start=time.monotonic();m.mp.dps=190
    q=item['q'];t=m.mpf(item['t'])+m.mpf(offset);lam=m.mpf(item['lam']);kap=m.mpf(item['kappa'])
    dx,dy=item['direction'];norm=m.sqrt(dx*dx+dy*dy);a=dx/norm;b=dy/norm
    hs=[{int(k):m.mpf(v) for k,v in params[n].items()} for n in ['h1','h2','h12']]
    def kernel(x):
        y=m.exp(2*x)
        if q==0:
            return m.exp(x/2)*sum(2*m.pi*(2*m.pi*n**4*y*y-3*n*n*y)*m.exp(-m.pi*n*n*y) for n in range(1,17))
        parity=1 if q==4 else 0
        return 2*m.exp((parity+m.mpf('.5'))*x)*sum(c.CHARS[q][n%q]*n**parity*m.exp(-m.pi*n*n*y/q) for n in range(1,41) if c.CHARS[q][n%q])
    def multiplier(x,derivative=False):
        h=[sum(v*m.cos(k*x) for k,v in row.items()) for row in hs]
        D=a*h[0]+b*h[1];W=a*b*h[2]
        return D+2*kap*lam*W if derivative else 1+lam*D+kap*lam*lam*W
    bounds=[0,m.mpf('.25'),m.mpf('.5'),m.mpf('.75'),1,m.mpf('1.5'),2,3,4]
    actual=[2*m.quad(lambda x:kernel(x)*multiplier(x)*m.cos(t*x),bounds),
            -2*m.quad(lambda x:x*kernel(x)*multiplier(x)*m.sin(t*x),bounds),
            -2*m.quad(lambda x:x*x*kernel(x)*multiplier(x)*m.cos(t*x),bounds),
            2*m.quad(lambda x:kernel(x)*multiplier(x,True)*m.cos(t*x),bounds)]
    _,pieces=evaluator(q,item['direction'],params);X,D,W=pieces(t)
    expected=[X[j]+lam*D[j]+kap*lam*lam*W[j] for j in range(3)]+[D[0]+2*kap*lam*W[0]]
    scale=m.exp(-m.pi*t/4)*(1+t*t)**m.mpf('.875')
    return dict(q=q,direction=item['direction'],t=m.nstr(t,190),offset=offset,lam=item['lam'],kappa=item['kappa'],
                labels=['F','F_t','F_tt','F_lambda'],scaled_integrals=[m.nstr(x/scale,80) for x in actual],
                scaled_errors=[m.nstr(abs(x/scale-y),80) for x,y in zip(actual,expected)],dps=190,cutoff=4,seconds=time.monotonic()-start)

if __name__=='__main__':
    start=time.monotonic();params={}
    for q in [0,5]:
        configure(q);params[q]={prec:d.prepare(prec) for prec in [70,120,180]}
    Path('parameters.json').write_text(json.dumps(params,indent=2)+'\n')
    cells=[(0,(1,-1),('31.5','33.5')),(0,(1,-1),('39.5','42')),
           (0,(1,1),('87.6','88.6')),(0,(-1,1),('87.6','88.6')),(5,(-1,1),('16','18'))]
    found=[]
    with mp.Pool(14) as pool,open('scan.jsonl','w',buffering=1) as out:
        for group in [cells[:2],cells[2:]]:
            durations=[]
            for row in pool.imap_unordered(scan,[(q,v,i,params[q][70]) for q,v,i in group]):
                out.write(json.dumps(row)+'\n');durations.append(row['seconds'])
                found.extend(dict(q=row['q'],direction=row['direction'],interval=row['interval'],**x) for x in row['roots'] if x['admitted'])
            print('scan stage',len(found),'elapsed',time.monotonic()-start,flush=True)
            if group==cells[:2] and 5*max(durations)>float(os.environ['CAMPAIGN_DEADLINE'])-time.monotonic():
                print('pilot rejects remaining cells',flush=True);break
        refined=[]
        with open('validation.jsonl','w',buffering=1) as out2:
            for row in pool.imap_unordered(refine,[(r,prec,params[r['q']][pp]) for r in found for prec,pp in [(100,120),(160,180)]]):
                out2.write(json.dumps(row)+'\n');refined.append(row)
        print('refined',len(refined),'elapsed',time.monotonic()-start,flush=True)
        with open('source-validation.jsonl','w',buffering=1) as out3:
            for row in pool.imap_unordered(integral_check,[(r,params[r['q']][180],offset) for r in refined if r['dps']==160 for offset in ['0','.125']]):out3.write(json.dumps(row)+'\n')
    Path('summary.json').write_text(json.dumps(dict(seconds=time.monotonic()-start),indent=2)+'\n')
