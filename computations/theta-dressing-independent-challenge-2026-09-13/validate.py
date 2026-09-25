from dressing import *
from independent import phi_independent

def independent(p,a,z,kind):
    L=mp.log(p);C=mp.log((mp.mp.dps+110)*mp.log(10)/(mp.pi*mp.cos(2*mp.im(z))))/2+3
    lo=int(mp.floor((-C-mp.re(z))/L))-3;hi=int(mp.ceil((C-mp.re(z))/L))+3
    scale=a*mp.re(z) if kind=='full' else 0;total=mp.mpc(0)
    for k in range(lo,hi+1):
        zz=z+k*L
        if mp.re(zz)<0:zz=-zz
        v=phi_independent('R',zz);fac=mp.exp((-a*L*abs(k) if kind=='full' else a*L*k)+scale);total+=fac*v
    return total

def work(task):
    row,dps=task;start=time.monotonic();mp.mp.dps=dps;p=mp.mpf(row['job']['p']);a=mp.mpf(row['job']['alpha']);kind=row['kind'];z=dec(row['root']);r=dict(row=row,dps=dps)
    try:
        for k in range(12):
            vv,n,meta=dress(p,a,z,kind,extra=3);ds=vv[0]/vv[1];z-=ds
            if abs(ds)<mp.mpf(10)**(-dps+20):break
        vv,n,meta=dress(p,a,z,kind,extra=3);iv=independent(p,a,z,kind);vbase,nbase,_=dress(p,a,z,kind);rad=min(mp.mpf('.002'),abs(mp.im(z))/5)
        values=[independent(p,a,z+rad*mp.exp(2j*mp.pi*k/32),kind) for k in range(32)];winding=mp.fsum(mp.arg(values[(k+1)%32]/values[k]) for k in range(32))/(2*mp.pi)
        r.update(root=enc(z),native_residual=str(abs(vv[0])/n),independent_residual=str(abs(iv)/n),inferred_root_error=str(abs(iv/vv[1])),wider_shift_difference=str(abs(vbase[0]-vv[0])/n),winding=str(winding),winding_radius=str(rad),**meta)
        assert abs(iv/vv[1])<mp.mpf(10)**(-dps+25)
        assert abs(winding-1)<mp.mpf('1e-20')
        r['status']='ok'
    except Exception as e:r.update(status='error',error=repr(e))
    r['seconds']=time.monotonic()-start;save('check-%d-%d.json'%(row['id'],dps),r);return r
if __name__=='__main__':
    start=time.monotonic();rows=[];tasks=[(r,d) for r in json.loads(Path('validation-jobs.json').read_text()) for d in [100,160]]
    with ProcessPoolExecutor(max_workers=14) as ex:
        for f in as_completed([ex.submit(work,t) for t in tasks]):
            r=f.result();rows.append(r);save('summary.json',dict(planned=len(tasks),rows=rows,seconds=time.monotonic()-start));print(r['row']['id'],r['dps'],r['status'],flush=True)
