"""Additional frozen clock scales, evaluated on Runpod only."""
import concurrent.futures
import json
import mpmath as mp
from scan import work,endpoint_tail

def large(params):
    h_text,r_text=params
    mp.mp.dps=150
    h,r=mp.mpf(h_text),mp.mpf(r_text)
    lam=2*mp.pi*r
    a=1/h
    t=lam/h
    u=mp.mpc(-1,-t)
    value=a*mp.im(a**(-mp.j*t)*endpoint_tail(u,a,a))+a/(12*t)
    error=(1+abs(1-mp.j*t))*mp.exp(-h/r)
    return dict(h=h_text,ratio=r_text,k=1,dps=150,approximation=mp.nstr(value,90),
                centered_tail_bound=mp.nstr(error,15),positive=bool(value>error))

if __name__=='__main__':
    grid=[(h,r,k) for h in ('0.37','0.63','0.83','0.97')
          for r in ('0.25','0.5','0.75','0.99') for k in (1,2,4)]
    with concurrent.futures.ProcessPoolExecutor(max_workers=8) as pool:
        rows=list(pool.map(work,grid))
        far=list(pool.map(large,[(h,r) for h in ('16','64','256','1024') for r in ('0.5','0.99')]))
    with open('extended.json','w') as out:
        json.dump(dict(noninteger_scales=rows,large_scales=far),out,indent=2)
    print(json.dumps(dict(noninteger_positive=[x for x in rows if x['positive']],large=far),indent=2))
