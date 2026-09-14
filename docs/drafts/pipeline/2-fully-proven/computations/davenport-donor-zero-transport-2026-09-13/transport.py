from challenge import jets
from source import *
from concurrent.futures import ProcessPoolExecutor,as_completed

def setup():
    zz=json.loads(Path('nodes.json').read_text());return Transform('D',dps=60),Transform('D',insert=[zz[0]],dps=60)

def fold_scan(T,U):
    def W(x):
        a=jets(T,x);b=jets(U,x);return mp.re(a[0]*b[1]-a[1]*b[0]),mp.re(a[0]*b[2]-a[2]*b[0]),a,b
    grid=[(mp.mpf(75)+mp.mpf(i)/8) for i in range(241)];vv=[W(x)[0] for x in grid];out=[]
    for k in range(1,len(grid)):
        if vv[k-1]*vv[k]>=0:continue
        lo,hi=grid[k-1:k+1];x=(lo+hi)/2
        for it in range(55):
            v,d,a,b=W(x);ds=v/d
            if abs(ds)<mp.mpf('1e-22'):break
            nx=x-ds
            if not(lo<nx<hi):nx=(lo+hi)/2
            nv=W(nx)[0]
            if nv*W(lo)[0]<0:hi=nx
            else:lo=nx
            x=nx
        v,d,a,b=W(x);lam=mp.re(-a[0]/(b[0]-a[0]));out.append(dict(w=enc(x),lambda_value=str(lam),W_correction=str(abs(v/d)),admitted=bool(0<lam<1)))
    return out

def work(job):
    start=time.monotonic();r=dict(job=job,dps=60);hist=[]
    try:
        T,U=setup();sign,eps=job['sign'],mp.mpf(job['epsilon']);w=mp.mpc('85.699348485377592171929',sign*mp.mpf('.308517182456637385553'))
        for k in range(8):v,d=T.val(w);w-=v/d
        u=mp.mpf(0);h=mp.mpf('.02');rej=0
        def lam(u):return u+1j*eps*mp.sin(mp.pi*u)
        while u<1:
            budget();h=min(h,1-u);a,da=T.val(w);b,db=U.val(w);l0=lam(u);l1=lam(u+h);pred=-(l1-l0)*(b-a)/((1-l0)*da+l0*db)
            if abs(pred)>.2:
                h/=2;rej+=1
                if h<mp.mpf('1e-8'):raise ArithmeticError('predictor continuation step floor')
                continue
            c=w+pred;ok=False
            for k in range(10):
                aa,ad=T.val(c);bb,bd=U.val(c);f=(1-l1)*aa+l1*bb;d=(1-l1)*ad+l1*bd;ds=f/d
                if abs(ds)<mp.mpf('1e-22'):ok=True;break
                if abs(ds)>.3:break
                c-=ds
            if not ok or abs(c-(w+pred))>.07:
                h/=2;rej+=1
                if h<mp.mpf('1e-8'):raise ArithmeticError('continuation step floor')
                continue
            if not(50<mp.re(c)<140 and abs(mp.im(c))<60):raise ArithmeticError('continuation domain escape')
            predictor_error=abs(c-(w+pred))
            w=c;u+=h;hist.append(dict(u=str(u),lambda_value=enc(l1),root=enc(w),correction=str(abs(ds)),predictor_error=str(predictor_error)))
            if predictor_error<.015:h=min(h*mp.mpf('1.2'),mp.mpf('.02'))
        r.update(status='ok',endpoint=enc(w),rejected_steps=rej)
    except Exception as e:r.update(status='error',error=repr(e))
    r.update(path=hist,seconds=time.monotonic()-start);save('path-'+job['label']+'.json',r);return r
if __name__=='__main__':
    start=time.monotonic();T,U=setup();folds=fold_scan(T,U);save('fold-candidates.json',folds)
    jobs=[dict(label=str(s)+'-'+e,sign=s,epsilon=e) for s in [-1,1] for e in ['0','.001','-.001','.01','-.01']];save('jobs.json',jobs);rows=[]
    with ProcessPoolExecutor(max_workers=14) as ex:
        for f in as_completed([ex.submit(work,j) for j in jobs]):
            r=f.result();rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print(r['job']['label'],r['status'],r.get('endpoint',r.get('error')),flush=True)
