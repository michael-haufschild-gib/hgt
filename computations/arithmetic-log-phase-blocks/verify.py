"""Independent finite-cell quadrature, executed only on Runpod."""
import concurrent.futures
import json
import mpmath as mp
from scan import tail

def verify(case):
    sigma_text,n,ratio_text,k,is_prefix = case
    mp.mp.dps=150
    sigma,ratio=mp.mpf(sigma_text),mp.mpf(ratio_text)
    t=2*mp.pi*n*ratio
    s=mp.mpc(sigma,t)
    a=mp.mpf(n) if is_prefix else n*mp.exp(2*mp.pi*k/t)
    b=n*mp.exp(2*mp.pi*(k if is_prefix else k+1)/t)
    scale=mp.mpf(n)**(2*sigma+2-s)
    via_tail=mp.im(scale*(tail(mp.conj(s),a)-tail(mp.conj(s),b)))
    cuts=[a]+[mp.mpf(j) for j in range(int(mp.floor(a))+1,int(mp.ceil(b)))]+[b]
    def integrand(x):
        r=x-mp.floor(x)
        return (r*r-r)/2*(n/x)**(sigma+2)*mp.sin(t*mp.log(x/n))
    direct=mp.fsum(mp.quad(integrand,[left,right]) for left,right in zip(cuts,cuts[1:]))
    return dict(sigma=sigma_text,n=n,ratio=ratio_text,k=k,is_prefix=is_prefix,
                start=mp.nstr(a,30),end=mp.nstr(b,30),dps=150,
                tail_difference=mp.nstr(via_tail,90),direct_quadrature=mp.nstr(direct,90),
                method_difference=mp.nstr(abs(direct-via_tail),10))

if __name__=='__main__':
    cases=[('0.05',16,'0.7',1,False),('0.05',16,'0.9999',4,False),
           ('0.5',64,'0.95',5,False),('8',16,'0.95',3,False),
           ('0.05',16,'0.7',2,True),('0.05',64,'0.9999',1,True),
           ('8',64,'0.9999',8,True),('0.5',1,'0.3',1,True)]
    with concurrent.futures.ProcessPoolExecutor(max_workers=8) as pool:
        rows=list(pool.map(verify,cases))
    with open('verification.json','w') as out:
        json.dump(rows,out,indent=2)
    print(json.dumps(rows,indent=2),flush=True)
