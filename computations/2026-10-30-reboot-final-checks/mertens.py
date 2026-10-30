import math
N=2_000_000
# von Mangoldt sieve
lam=[0.0]*(N+1)
isp=bytearray([1])*(N+1); isp[0]=isp[1]=0
for p in range(2,N+1):
    if isp[p]:
        for q in range(p*p,N+1,p): isp[q]=0
        pk=p
        while pk<=N:
            lam[pk]=math.log(p); pk*=p
A=[0.0]*(N+1)
for t in range(1,N+1): A[t]=A[t-1]+lam[t]/t
g=0.5772156649015329
def R(y): return A[y]-math.log(y)+g
for M in [10**4,10**5,10**6,2*10**6]:
    tot=0.0; band={}
    for n in range(1,M+1):
        y=M//n
        v=(A[y]+math.log(n)-(math.log(M)-g))**2/n
        tot+=v
        for Y in (2,4,16,256):
            if y<Y: band[Y]=band.get(Y,0)+v
    print(f"N={M}: |residual|^2={tot:.4f}  log N={math.log(M):.2f}  rel={tot/math.log(M):.4f}  share from y<2,4,16,256: "+", ".join(f"{band[Y]/tot:.3f}" for Y in (2,4,16,256)))
print("R(y) small y:", [round(R(y),3) for y in (1,2,3,4,5,8,16,100,1000,10**5)])
