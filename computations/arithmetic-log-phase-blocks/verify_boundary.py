"""High-precision finite-cell formula versus quadrature; Runpod only."""
import concurrent.futures
import json
import mpmath as mp
from boundary import finite

def verify(case):
    sigma_text,n,ratio_text,k=case
    mp.mp.dps=150
    sigma,ratio=mp.mpf(sigma_text),mp.mpf(ratio_text)
    t=2*mp.pi*n*ratio
    a=mp.mpf(n)
    b=n*mp.exp(2*mp.pi*k/t)
    algebra=finite(sigma,n,t,a,b)
    cuts=[a]+[mp.mpf(j) for j in range(n+1,int(mp.ceil(b)))]+[b]
    def integrand(x):
        r=x-mp.floor(x)
        return (r*r-r)/2*(n/x)**(sigma+2)*mp.sin(t*mp.log(x/n))
    direct=mp.fsum(mp.quad(integrand,[left,right]) for left,right in zip(cuts,cuts[1:]))
    return dict(sigma=sigma_text,n=n,ratio=ratio_text,k=k,dps=150,
                finite_primitive=mp.nstr(algebra,90),quadrature=mp.nstr(direct,90),
                method_difference=mp.nstr(abs(algebra-direct),10))

if __name__=='__main__':
    cases=[('-1',4096,'0.5',1),('-1',4096,'0.25',8),
           ('0.001',4096,'0.25',8),('0.001',4096,'0.9999',1)]
    with concurrent.futures.ProcessPoolExecutor(max_workers=4) as pool:
        rows=list(pool.map(verify,cases))
    with open('boundary-verification.json','w') as out:
        json.dump(rows,out,indent=2)
    print(json.dumps(rows,indent=2))
