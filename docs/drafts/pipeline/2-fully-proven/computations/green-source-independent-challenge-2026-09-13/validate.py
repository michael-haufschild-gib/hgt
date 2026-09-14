from green import *
from independent import phi_independent

def independent(G,z,a,hd):
    a=mp.mpf(a)
    init=2*mp.quad(lambda x:mp.exp(-a*x)*phi_independent('R',x),[0,.5,1,2,mp.mpf('3.5')])
    def integrand(u,derivative=False):
        budget();t=u*z
        return (mp.cosh(a*(z-t)) if derivative else mp.sinh(a*(z-t)))*phi_independent('R',t)
    I=mp.quad(lambda u:integrand(u),[0,.5,.85,.97,1]);J=mp.quad(lambda u:integrand(u,True),[0,.5,.85,.97,1])
    return init*mp.cosh(a*z)-2*z*I,a*init*mp.sinh(a*z)-2*a*z*J

def work(task):
    row,dps=task;mp.mp.dps=dps;start=time.monotonic();r=dict(row=row,dps=dps)
    try:
        hd=128 if dps==100 else 256;G=Green('R',dps,hd);z=dec(row['root']);mode=row['job']['mode']
        for k in range(12):
            v,der,n=G.val(z,mode);ds=v/der;z-=ds
            if abs(ds)<mp.mpf(10)**(-dps+30):break
        v,der,n=G.val(z,mode);iv,id=independent(G,z,mode,hd);r.update(root=enc(z),native_residual=str(abs(v)/n),independent_residual=str(abs(iv)/n),inferred_root_error=str(abs(iv/id)),derivative_relative_error=str(abs(der-id)/abs(id)))
        assert abs(iv/id)<mp.mpf(10)**(-dps+40)
        if mode=='.5':
            def direct(w):return mp.exp(-w/2)/2-mp.exp(w/2)*(mp.jtheta(3,0,mp.exp(-mp.pi*mp.exp(2*w)))-1)/2
            vv=[direct(z+mp.mpf('.001')*mp.exp(2j*mp.pi*k/32)) for k in range(32)];r['closed_expression_error']=str(abs(direct(z)/id));r['winding']=str(mp.fsum(mp.arg(vv[(k+1)%32]/vv[k]) for k in range(32))/(2*mp.pi));assert abs(mp.mpf(r['winding'])-1)<mp.mpf('1e-20')
        r['status']='ok'
    except Exception as e:r.update(status='error',error=repr(e))
    r['seconds']=time.monotonic()-start;save('check-%d-%d.json'%(row['id'],dps),r);return r
if __name__=='__main__':
    start=time.monotonic();rows=[];tasks=[(r,d) for r in json.loads(Path('validation-jobs.json').read_text()) for d in [100,160]]
    with ProcessPoolExecutor(max_workers=14) as ex:
        for f in as_completed([ex.submit(work,t) for t in tasks]):
            r=f.result();rows.append(r);save('summary.json',dict(planned=len(tasks),rows=rows,seconds=time.monotonic()-start));print(r['row']['id'],r['dps'],r['status'],flush=True)
