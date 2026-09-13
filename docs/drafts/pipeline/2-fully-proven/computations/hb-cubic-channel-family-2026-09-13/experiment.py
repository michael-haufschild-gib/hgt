"""Exact local mixed cubic Einstein coefficients. Missing global fields stay unknown."""
import functools
import json
import multiprocessing as mp
import os
import time
from pathlib import Path
import sympy as sp

z = sp.Symbol('z')
r,y,B = sp.symbols('r y B')
jets = sp.symbols('S Sx Sy Sxx Sxy Sxxx Sxxy')
S,Sx,Sy,Sxx,Sxy,Sxxx,Sxxy = jets
f=r*r-1

def cut(v):
    v=sp.expand(v)
    return v.coeff(z,0)+z*v.coeff(z,1)

def mc(A): return A.applyfunc(cut)

def field(s,a,b):
    T=s*(s-3)/2+s*(s+1)/(2*r*r)
    R=-s*(r*r-s)/(r*f)
    A=(-r*r-s*(s+1)/2)/y**2
    H=a*B*S*sp.Matrix([[T,R,0,0],[R,T/f**2,0,0],[0,0,A,0],[0,0,0,A]])
    for j,V in enumerate((Sy,-Sx)):
        H[0,j+2]=H[j+2,0]=-b*s*B*V/r
        H[1,j+2]=H[j+2,1]=-b*s*B*V/f
    return H

def local_correction(s,a,b):
    K=sp.zeros(4)
    C=s*s*((s+1)**2-4*r*r)/(8*r**4)
    K[0,1]=K[1,0]=a*a*B**2*C*S*S
    K[1,1]=2*K[0,1]/f
    for j,V in enumerate((Sy,-Sx)):
        K[0,j+2]=K[j+2,0]=a*b*f*B**2*s*(s+1)*S*V/(2*r**3)
    return K

def partial(v,k,s):
    lam=(s+1)*(s+2)
    if k==0:return sp.diff(v,B)*s*B
    if k==1:return sp.diff(v,r)+sp.diff(v,B)*s*B/(r*f)
    vals=(Sx,Sxx,Sxy,Sxxx,Sxxy) if k==2 else (Sy,Sxy,lam*S/y**2-Sxx,Sxxy,lam*Sx/y**2-Sxxx)
    return (sp.diff(v,y) if k==3 else 0)+sum(sp.diff(v,q)*v1 for q,v1 in zip(jets[:5],vals))

def task(args):
    point,pair,qpair,corrected=args
    begin=time.monotonic()
    s,rad=[(sp.Rational(-5,4),sp.Integer(2)),(sp.Rational(-2,3),sp.Rational(3,2))][point]
    sq=-3-s
    substitutions={r:rad,y:1,B:1,**dict(zip(jets,[1,2,3,5,7,11,13]))}
    def at(A):return A.applyfunc(lambda v: v.subs(substitutions))
    def jetted(A,rate):
        d=[A.applyfunc(lambda v:partial(v,k,rate)) for k in range(4)]
        dd=[[d[i].applyfunc(lambda v:partial(v,k,rate)) for i in range(4)] for k in range(4)]
        return at(A),[at(x) for x in d],[[at(x) for x in row] for row in dd]
    G=sp.diag(-f,1/f,r*r/y**2,r*r/y**2)
    gj=jetted(G,s)
    pj=jetted(field(s,*pair),s)
    qj=jetted(field(sq,*qpair),sq)
    kj=jetted(local_correction(s,*pair)*corrected,s)
    metric=[gj[0],pj[0]+z*qj[0],kj[0],sp.zeros(4)]
    first=[[gj[1][k] for k in range(4)],
           [pj[1][k]+z*qj[1][k] for k in range(4)],kj[1],[sp.zeros(4) for _ in range(4)]]
    second=[gj[2],[[pj[2][k][i]+z*qj[2][k][i] for i in range(4)] for k in range(4)],
            kj[2],[[sp.zeros(4) for _ in range(4)] for _ in range(4)]]
    inv=[metric[0].inv()]
    for n in range(1,4):
        inv.append(mc(-sum((inv[n-j]*metric[j]*inv[0] for j in range(1,n+1)),sp.zeros(4))))
    invd=[[mc(-sum((inv[a]*first[b][k]*inv[n-a-b] for a in range(n+1)
                   for b in range(n-a+1)),sp.zeros(4))) for k in range(4)] for n in range(4)]
    @functools.lru_cache(None)
    def conn(n,u,i,j):
        return cut(sum(inv[n-b][u,m]*(first[b][i][m,j]+first[b][j][m,i]-first[b][m][i,j])
                       for b in range(n+1) for m in range(4))/2)
    @functools.lru_cache(None)
    def cd(n,k,u,i,j):
        return cut(sum(invd[n-b][k][u,m]*(first[b][i][m,j]+first[b][j][m,i]-first[b][m][i,j])+
                       inv[n-b][u,m]*(second[b][k][i][m,j]+second[b][k][j][m,i]-second[b][k][m][i,j])
                       for b in range(n+1) for m in range(4))/2)
    @functools.lru_cache(None)
    def ricci(n,i,j):
        return cut(sum(cd(n,u,u,j,i)-cd(n,j,u,u,i)+
                       sum(conn(a,u,u,m)*conn(n-a,m,j,i)-conn(a,u,j,m)*conn(n-a,m,u,i)
                           for a in range(n+1) for m in range(4)) for u in range(4)))
    Ric=[sp.Matrix(4,4,lambda i,j:ricci(n,i,j)) for n in range(4)]
    scalar=[cut(sum((inv[a]*Ric[n-a]).trace() for a in range(n+1))) for n in range(4)]
    E=[mc(Ric[n]-sum((scalar[a]*metric[n-a]/2 for a in range(n+1)),sp.zeros(4))-3*metric[n]) for n in range(4)]
    assert E[0]==sp.zeros(4) and E[1]==sp.zeros(4), 'background/linear equation failed'
    def contract(A,C):return cut(sum(A[i,j]*C[i,j] for i in range(4) for j in range(4)))
    rows=[]
    for rate_name,rate in [('same',s),('opposite',sq)]:
        for reader_name,amps in [('S',(1,0)),('V',(0,1))]:
            reader=field(rate,*amps).subs({r:rad,y:1,B:1,S:2,Sx:3,Sy:-2})
            weight=inv[0]*reader*inv[0].T
            slope=mc((inv[0]*metric[1]).trace()/2*weight-
                     inv[0]*metric[1]*inv[0]*reader*inv[0].T-
                     inv[0]*reader*(inv[0]*metric[1]*inv[0]).T)
            direct=sp.expand(contract(weight,E[3])).coeff(z,1)
            changing=sp.expand(contract(slope,E[2])).coeff(z,1)
            rows.append(dict(reader=rate_name+'_'+reader_name,direct=str(direct),
                             changing_weight=str(changing),total=str(direct+changing)))
    result=dict(point=point,s=str(s),r=str(rad),P=pair,Q=qpair,corrected=corrected,
                rows=rows, E2=[str(v) for v in E[2]],E3=[str(v) for v in E[3]],
                seconds=time.monotonic()-begin,
                unknowns=['linear L++-','second(P,K+-missing)','second(Q,K++missing)',
                          'weightSlope(Q,M):linear K++missing','weightSlope(P,M):linear K+-missing',
                          'all integrated boundary faces','onset and causal restoration','reader remainder'])
    return result

if __name__=='__main__':
    started=time.monotonic()
    jobs=[(point,p,q,c) for point in [0,1] for p in [(1,0),(0,1),(1,1)]
          for q in [(1,0),(0,1)] for c in [0,1]]
    count=0
    with open('raw.jsonl','w',buffering=1) as out,mp.Pool(14) as pool:
        for batch in (jobs[:2],jobs[2:]):
            begin=time.monotonic()
            for row in pool.imap_unordered(task,batch):
                out.write(json.dumps(row)+'\n');count+=1
            print('stage',count,'elapsed',time.monotonic()-started,flush=True)
            if count==2 and 2*(time.monotonic()-begin)>float(os.environ['CAMPAIGN_DEADLINE'])-time.monotonic():
                print('pilot predicts remaining budget exceeded; stop without expansion',flush=True)
                break
    Path('summary.json').write_text(json.dumps(dict(count=count,seconds=time.monotonic()-started),indent=2)+'\n')
