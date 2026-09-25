"""Independent 70-digit direct-source audit of the first PE1 and PE2 failures."""
import json,pathlib
import mpmath as mp
mp.mp.dps=70
out=pathlib.Path(__file__).parent

def audit(M,stages):
    D=[mp.mpf(0)]+[mp.loggamma(n+1)-sum(n//d for d in range(1,n+1))+2*mp.euler*n for n in range(1,M+1)]
    K={d:mp.fsum((mp.sqrt(k+1)-mp.sqrt(k))*D[k//d] for k in range(d,M)) for d in range(1,M+1)}
    mu={}; factors={}
    for n in range(1,M+1):
        q=n; ps=[]; repeated=False
        for p in range(2,n+1):
            if q%p:continue
            ps.append(p);q//=p
            if q%p==0:repeated=True
            while q%p==0:q//=p
            if q==1:break
        mu[n]=0 if repeated else (-1)**len(ps)
        factors[n]=ps
    Q=mp.fsum(K[d]**2 for d in K if mu[d])
    result={'M':M,'original_energy':str(Q),'stages':[]}
    for p in stages:
        F={d:mp.fsum(mu[a]*K[a*d] for a in range(1,M//d+1) if mu[a] and all(q<=p for q in factors[a]))
           for d in range(1,M+1) if mu[d] and all(q>p for q in factors[d])}
        E=mp.fsum(x*x for x in F.values())
        result['stages'].append({'prime':p,'energy':str(E),'ratio_to_original':str(E/Q),'head':str(F[1])})
    return result
r=[audit(5,[2,3]),audit(198,[43])]
(out/'direct-audit.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
