import math, csv, json
from pathlib import Path
import mpmath as mp
mp.mp.dps=80
N=100
mu=[0]+[1]*N
for p in range(2,N+1):
    if all(p%d for d in range(2,math.isqrt(p)+1)):
        for n in range(p,N+1,p): mu[n]*=-1
        for n in range(p*p,N+1,p*p): mu[n]=0
for n in range(1,N+1):
    assert sum(mu[d] for d in range(1,n+1) if n%d==0)==int(n==1)
D=[mp.mpf(0)]+[mp.log(mp.factorial(q))-sum(q//d for d in range(1,q+1))+2*mp.euler*q for q in range(1,N+1)]
C=[0.0]*(N+1)
rows=[]
positives=[]
for M in range(1,N+1):
    if M>=2:
        k=M-1
        w=math.sqrt(M)-math.sqrt(k)
        for d in range(1,M): C[d]+=mu[d]*w*float(D[k//d])
    groups=[[] for _ in range(M+1)]
    for d in range(1,M+1):
        for e in range(d+1,M+1):
            groups[math.gcd(d,e)].append(2*C[d]*C[e])
    G=[math.fsum(x) for x in groups]
    S=math.fsum(C[1:M+1]); Q=math.fsum(c*c for c in C[1:M+1])
    assert abs(math.fsum(G)-(S*S-Q))<1e-10*max(1,Q)
    for r in range(1,M+1):
        rows.append((M,r,G[r],S*S-Q))
        if G[r]>1e-12*max(1,Q): positives.append((M,r,G[r],S*S-Q))
p=Path('/tmp/ccm_fu_gcd_screen.csv')
with p.open('w') as f:
    w=csv.writer(f);w.writerow(['M','r','G_r','total_off_diagonal']);w.writerows(rows)
print('Complete endpoints:',N,'component rows:',len(rows),'positive components:',len(positives))
print('First positive components:',positives[:12])
if positives:
    M,r,*_=positives[0]
    Cmp={d:mu[d]*mp.fsum((mp.sqrt(k+1)-mp.sqrt(k))*D[k//d] for k in range(d,M)) for d in range(1,M+1)}
    Gmp={g:2*mp.fsum(Cmp[d]*Cmp[e] for d in range(1,M+1) for e in range(d+1,M+1) if math.gcd(d,e)==g) for g in range(1,M+1)}
    print('80-digit first endpoint channels:',{d:mp.nstr(c,45) for d,c in Cmp.items() if c})
    print('80-digit first endpoint gcd components:',{g:mp.nstr(v,45) for g,v in Gmp.items() if v})
    print('80-digit total:',mp.nstr(mp.fsum(Gmp.values()),50))
