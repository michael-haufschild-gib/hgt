"""Frozen PE3: full subset/path screen, plus separate greedy guidance. No Lean input."""
import csv,json,math,pathlib,time
out=pathlib.Path(__file__).parent
limit=1024
mu=[1]*(limit+1);mu[0]=0
tau=[0]*(limit+1);prime=[True]*(limit+1);prime[0]=prime[1]=False
primes=[]
for d in range(1,limit+1):
    for k in range(d,limit+1,d):tau[k]+=1
for p in range(2,limit+1):
    if prime[p]:
        primes.append(p)
        for k in range(p,limit+1,p):
            mu[k]=-mu[k]
            if k>p:prime[k]=False
        for k in range(p*p,limit+1,p*p):mu[k]=0
D=[0.]*(limit+1);A=[0.]*(limit+2);logs=count=0.
for n in range(1,limit+1):
    logs+=math.log(n);count+=tau[n]
    D[n]=logs-count+2*.5772156649015328606065120900824*n
    A[n+1]=A[n]+D[n]/(math.sqrt(n+1)+math.sqrt(n))
def channels(M):
    return {d:math.sqrt(d)*A[M//d]+(math.sqrt(M)-math.sqrt(d*(M//d)))*D[M//d]
            for d in range(1,M) if mu[d]}
def pair(v,p):return {d:x-v.get(p*d,0.) for d,x in v.items() if d%p}
def energy(v):return math.fsum(x*x for x in v.values())
start=time.monotonic();full=[];greedy=[]
with (out/'subset-states.csv').open('w') as f:
    w=csv.writer(f);w.writerow(['M','mask','processed_primes','energy','reachable_monotonically','incoming_monotone_mask'])
    for M in range(1,33):
        ps=[p for p in primes if p<M];states=[None]*(1<<len(ps));energies=[0.]*len(states)
        reach=[False]*len(states);reach[0]=True;states[0]=channels(M);energies[0]=energy(states[0]);tol=1e-12*max(1,energies[0])
        edges=0
        for mask in range(len(states)):
            if mask:
                bit=mask&-mask;i=bit.bit_length()-1
                states[mask]=pair(states[mask^bit],ps[i]);energies[mask]=energy(states[mask])
            incoming=[]
            for i,p in enumerate(ps):
                if mask>>i&1 and energies[mask]<=energies[mask^(1<<i)]+tol:
                    incoming.append(i);edges+=1
                    if reach[mask^(1<<i)]:reach[mask]=True
            w.writerow([M,mask,' '.join(str(p) for i,p in enumerate(ps) if mask>>i&1),energies[mask],reach[mask],sum(1<<i for i in incoming)])
        full.append({'M':M,'prime_count':len(ps),'states':len(states),'nonincreasing_edges':edges,'reachable_states':sum(reach),'PE3_path_exists':reach[-1],
                     'initial':energies[0],'final':energies[-1]})
with (out/'greedy-stages.csv').open('w') as f:
    w=csv.writer(f);w.writerow(['M','step','prime','previous_energy','next_energy','release','initial_energy'])
    for M in range(1,limit+1):
        ps=[p for p in primes if p<M];v=channels(M);E0=prev=energy(v);order=[];first_increase=None
        while ps:
            choices=[(energy(pair(v,p)),p) for p in ps]
            E,p=min(choices);order.append(p);ps.remove(p)
            if E>prev+1e-12*max(1,E0) and first_increase is None:first_increase={'step':len(order),'p':p,'previous':prev,'next':E}
            w.writerow([M,len(order),p,prev,E,prev-E,E0]);v=pair(v,p);prev=E
        greedy.append({'M':M,'first_increase':first_increase,'order':order,'initial':E0,'final':prev})
(out/'full-path-summary.json').write_text(json.dumps(full,indent=2)+'\n')
(out/'greedy-summary.json').write_text(json.dumps(greedy,indent=2)+'\n')
summary={'full_path_limit':32,'greedy_limit':limit,'first_PE3_path_failure':next((x for x in full if not x['PE3_path_exists']),None),
         'first_greedy_failure':next((x for x in greedy if x['first_increase']),None),'greedy_failed_cutoffs':sum(x['first_increase'] is not None for x in greedy),'seconds':time.monotonic()-start}
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
