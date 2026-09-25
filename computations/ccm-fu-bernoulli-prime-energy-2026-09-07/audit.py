"""Independent 80-digit literal-source check at M=1024. Guidance only."""
import json,pathlib,mpmath as mp,time
mp.mp.dps=80
out=pathlib.Path(__file__).parent;M=1024;start=time.monotonic()
D=[mp.mpf(0)]*M;logs=mp.mpf(0);taus=0
for n in range(1,M):
    logs+=mp.log(n);taus+=sum(n%d==0 for d in range(1,n+1))
    D[n]=logs-taus+2*mp.euler*n
w=[mp.sqrt(k+1)-mp.sqrt(k) for k in range(M)]
H=[];Q=[];S=[]
for d in range(1,M):
    n=d;factors=[];squarefree=True;p=2
    while p*p<=n:
        e=0
        while n%p==0:e+=1;n//=p
        if e:factors.append(p)
        if e>1:squarefree=False
        p+=1
    if n>1:factors.append(n)
    if not squarefree:continue
    mu=(-1)**len(factors)
    K=mp.fsum(w[k]*D[k//d] for k in range(d,M))
    H.append(mu*K/mp.mpf(2)**len(factors));Q.append(K*K);S.append(mu*K)
H=mp.fsum(H);Q=mp.fsum(Q);S=mp.fsum(S)
a={'M':M,'precision':mp.mp.dps,'literal_half_mean':str(H),'literal_diagonal':str(Q),
   'mean_square_minus_diagonal':str(H*H-Q),'mean_square_ratio':str(H*H/Q),
   'final_square_ratio':str(S*S/Q),'seconds':time.monotonic()-start}
(out/'direct-audit.json').write_text(json.dumps(a,indent=2)+'\n');print(json.dumps(a,indent=2))
