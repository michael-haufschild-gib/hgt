"""Frozen PE5 at t=1/2. Numerical guidance, never a Lean input."""
import csv,json,math,pathlib,time
out=pathlib.Path(__file__).parent
old=out.parent/'ccm-fu-adaptive-prime-energy-2026-09-06'
rows={}
for r in csv.DictReader((old/'subset-states.csv').open()):
    rows.setdefault(int(r['M']),[]).append(r)
subset=[]
for M,states in rows.items():
    E0=float(states[0]['energy']); avg=math.fsum(float(r['energy']) for r in states)/len(states)
    subset.append({'M':M,'diagonal':E0,'half_energy':avg,'ratio':avg/E0 if E0 else 0})
start=time.monotonic();limit=2**18
mu=[1]*(limit+1);mu[0]=0;omega=[0]*(limit+1);tau=[0]*(limit+1)
for d in range(1,limit+1):
    for n in range(d,limit+1,d):tau[n]+=1
for p in range(2,limit+1):
    if omega[p]==0:
        for n in range(p,limit+1,p):mu[n]=-mu[n];omega[n]+=1
        for n in range(p*p,limit+1,p*p):mu[n]=0
D=[0.]*(limit+1);A=[0.]*(limit+2);tausum=0
for n in range(1,limit+1):
    tausum+=tau[n]
    D[n]=math.lgamma(n+1)-tausum+2*.5772156649015328606065120900824*n
    A[n+1]=A[n]+D[n]/(math.sqrt(n+1)+math.sqrt(n))
dyadic=[]
for exponent in range(5,19):
    M=2**exponent;rootM=math.sqrt(M);terms=[];squares=[];total=[]
    for d in range(1,M):
        if not mu[d]:continue
        q=M//d;K=math.sqrt(d)*A[q]+(rootM-math.sqrt(d*q))*D[q]
        terms.append(mu[d]*2.**(-omega[d])*K);squares.append(K*K);total.append(mu[d]*K)
    H=math.fsum(terms);Q=math.fsum(squares);S=math.fsum(total)
    dyadic.append({'M':M,'half_mean_head':H,'diagonal':Q,'mean_square_ratio':H*H/Q,'final_square_ratio':S*S/Q})
summary={'t':.5,'subset_results':subset,'dyadic_results':dyadic,'seconds':time.monotonic()-start,
         'first_dyadic_mean_obstruction':next((r for r in dyadic if r['mean_square_ratio']>1),None)}
(out/'screen.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({'last_subset':subset[-1],'dyadic_results':dyadic,'seconds':summary['seconds'],'first_dyadic_mean_obstruction':summary['first_dyadic_mean_obstruction']},indent=2))
