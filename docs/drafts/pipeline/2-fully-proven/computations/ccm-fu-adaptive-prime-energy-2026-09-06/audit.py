"""Independent direct-source 80-digit audit of the full M=7 prime-order cube."""
import itertools,json,pathlib
import mpmath as mp
mp.mp.dps=80
out=pathlib.Path(__file__).parent
M=7
D={q:mp.loggamma(q+1)-sum(q//d for d in range(1,q+1))+2*mp.euler*q for q in range(1,M)}
K={d:mp.fsum((mp.sqrt(k+1)-mp.sqrt(k))*D[k//d] for k in range(d,M)) for d in range(1,M)}
mu={1:1,2:-1,3:-1,4:0,5:-1,6:1}
def energy(P):
    prod=1
    for p in P:prod*=p
    F={d:mp.fsum((-1)**len(A)*K[d*mathprod(A)] for j in range(len(P)+1) for A in itertools.combinations(P,j) if d*mathprod(A)<M)
       for d in range(1,M) if mu[d] and all(d%p for p in P)}
    return mp.fsum(v*v for v in F.values()),F
def mathprod(A):
    r=1
    for a in A:r*=a
    return r
states=[]
for j in range(4):
 for P in itertools.combinations([2,3,5],j):
    E,F=energy(P);states.append({'processed':P,'energy':str(E),'F':{d:str(x) for d,x in F.items()}})
paths=[]
for order in itertools.permutations([2,3,5]):
 Es=[energy(order[:j])[0] for j in range(4)]
 paths.append({'order':order,'energies':list(map(str,Es)),'increases':[j for j in range(1,4) if Es[j]>Es[j-1]]})
result={'M':M,'K':{d:str(x) for d,x in K.items()},'states':states,'paths':paths}
(out/'direct-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
