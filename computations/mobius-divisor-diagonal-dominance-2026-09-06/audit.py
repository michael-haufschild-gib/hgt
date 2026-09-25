"""Independent high-precision audit of every reported extremum; Runpod only."""
from pathlib import Path
import json
import time
import mpmath as mp

ROOT=Path(__file__).resolve().parent


def mobius(n):
    sign=1
    p=2
    while p*p<=n:
        if n%p==0:
            n//=p
            sign=-sign
            if n%p==0:
                return 0
        p+=1
    return -sign if n>1 else sign


def endpoint(M,dps):
    mp.mp.dps=dps
    D=[mp.mpf(0)]
    for q in range(1,M+1):
        D.append(mp.log(mp.factorial(q))-sum(q//d for d in range(1,q+1))+2*mp.euler*q)
    channels=[]
    for d in range(1,M+1):
        # Original double sum, not the quotient-block or coefficient-jump implementation.
        k=mp.fsum((mp.sqrt(t+1)-mp.sqrt(t))*D[t//d] for t in range(d,M))
        channels.append(mobius(d)*k/M)
    source=mp.fsum(channels)
    diagonal=mp.fsum(c*c for c in channels)
    return source,diagonal,source*source/diagonal


if __name__=='__main__':
    started=time.monotonic()
    original=json.loads((ROOT/'search.json').read_text())
    results=[]
    for row in original['top_direct']:
        low=endpoint(row['M'],60)
        high=endpoint(row['M'],100)
        assert abs(low[2]-high[2])<mp.mpf('1e-50')
        assert abs(high[2]-row['ratio'])<mp.mpf('1e-9')
        results.append(dict(M=row['M'],source=mp.nstr(high[0],75),
                            diagonal=mp.nstr(high[1],75),ratio=mp.nstr(high[2],75),
                            margin=mp.nstr(1-high[2],75)))
    result=dict(seconds=time.monotonic()-started,precisions=[60,100],extrema=results,
                equality_M2='Symbolically one nonzero channel, so equality is exact.')
    (ROOT/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(seconds=result['seconds'],extrema_checked=len(results),largest=results[0]),indent=2))
