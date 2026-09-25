"""Frozen PE1/PE2 screen. Floating point guidance, never a Lean proof input."""
import csv,json,math,pathlib,time
out=pathlib.Path(__file__).parent
N=1024
gamma=.5772156649015328606065120900824
tau=[0]*(N+1); mu=[1]*(N+1); prime=[True]*(N+1)
prime[0]=prime[1]=False; mu[0]=0
for d in range(1,N+1):
    for k in range(d,N+1,d):tau[k]+=1
primes=[]
for p in range(2,N+1):
    if prime[p]:
        primes.append(p)
        for k in range(p,N+1,p):
            mu[k]=-mu[k]
            if k>p:prime[k]=False
        for k in range(p*p,N+1,p*p):mu[k]=0
D=[0.]*(N+1); H=[0.]*(N+2); L=T=0.
for n in range(1,N+1):
    L+=math.log(n);T+=tau[n];D[n]=L-T+2*gamma*n
    H[n+1]=H[n]+D[n]/(math.sqrt(n+1)+math.sqrt(n))
first_step=first_cap=None; max_cap=(0,None); count_step=count_cap=0
start=time.monotonic()
with (out/'stages.csv').open('w') as f:
    writer=csv.writer(f);writer.writerow(['M','prime','stage_energy','original_energy','previous_energy','relative_to_original'])
    for M in range(1,N+1):
        K={}
        for d in range(1,M+1):
            if not mu[d]:continue
            q=M//d
            K[d]=math.sqrt(d)*H[q]+(math.sqrt(M)-math.sqrt(d*q))*D[q]
        E0=prev=sum(x*x for x in K.values())
        for p in primes:
            if p>M:break
            K={d:x-K.get(p*d,0.) for d,x in K.items() if d%p}
            E=sum(x*x for x in K.values())
            ratio=E/E0 if E0 else 0.
            writer.writerow([M,p,E,E0,prev,ratio])
            tolerance=1e-12*max(1.,E0)
            if E>prev+tolerance:
                count_step+=1
                if first_step is None:first_step={'M':M,'p':p,'previous':prev,'next':E,'increase':E-prev}
            if E>E0+tolerance:
                count_cap+=1
                if first_cap is None:first_cap={'M':M,'p':p,'original':E0,'next':E,'ratio':ratio}
            if ratio>max_cap[0] and M>2:max_cap=(ratio,(M,p))
            prev=E
result={'N':N,'first_PE1_failure':first_step,'PE1_increases':count_step,'first_PE2_failure':first_cap,'PE2_failures':count_cap,'largest_PE2_ratio_excluding_M2':max_cap,'seconds':time.monotonic()-start}
(out/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
