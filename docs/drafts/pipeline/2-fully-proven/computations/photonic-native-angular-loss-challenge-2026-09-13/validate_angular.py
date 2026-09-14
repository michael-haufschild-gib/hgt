from challenge import *

def experiment(j):
 mp.mp.dps=j['dps'];d=j['dim'];N=j['N'];x,y,delta,ell=[mp.mpf(j[k]) for k in ['x','y','delta','ell']];pa=pb=mp.mpf('.5') if d%2 else mp.mpf(0)
 g=mp.matrix([[1/mp.sqrt(y),x/mp.sqrt(y)],[0,mp.sqrt(y)]]);C=mp.matrix([[mp.cosh(delta),-1j*mp.sinh(delta)],[1j*mp.sinh(delta),mp.cosh(delta)]])
 base=Native(C*g,d,N,pa,pb);G=overlap(base,base,'theta');W,ev=invroot(G);loss=mp.matrix(d,d);rows=[]
 for k in range(j['angles']):
  budget();theta=mp.pi*k/j['angles'];rot=osc(1,theta);M=rot*mp.diag([mp.exp(ell/2),mp.exp(-ell/2)])*rot.T
  target=Native(C*M*g,d,N,pa,pb);Gt=overlap(target,target,'theta');Wt,evt=invroot(Gt);A=M*base.A
  prop=Native(A,d,N,pa,pb,base.pref*mp.sqrt(base.A[0,1]/A[0,1]));K=Wt*overlap(target,prop,'theta')*W;L=(mp.eye(d)-K.H*K)/(ell*ell);L=(L+L.H)/2
  ne=mp.norm(W*overlap(prop,prop,'theta')*W-mp.eye(d));assert ne<mp.mpf('1e-25');assert min(mp.eighe(L,eigvals_only=True))>-mp.mpf('1e-25')
  loss+=L/j['angles'];rows.append(dict(theta=str(theta),K=matenc(K),loss=matenc(L),unitary_gram_error=str(ne)))
 mean=mp.re(trace(loss))/d;res=loss-mean*mp.eye(d)
 return dict(average_loss=matenc(loss),loss_eigenvalues=[str(z) for z in mp.eighe(loss,eigvals_only=True)],mean_loss=str(mean),relative_nonscalar_norm=str(mp.norm(res)/mp.norm(loss)),canonical_mixture_loss=str(mp.re(trace(G*loss)/trace(G))),gram_eigenvalues=[str(z) for z in ev],gram_condition=str(max(ev)/min(ev)),angle_rows=rows)

def work(j):
 start=time.monotonic();r=dict(job=j)
 try:r.update(experiment(j));r['status']='ok'
 except Exception as e:r.update(status='error',error=repr(e))
 r['seconds']=time.monotonic()-start;save('case-'+str(j['id'])+'.json',r);return r
if __name__=='__main__':
 jobs=json.loads(Path('jobs.json').read_text());start=time.monotonic();rows=[];r=work(jobs[0]);rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print('pilot',r['status'],r['seconds'],r.get('error',''),flush=True)
 if r['status']!='ok' or r['seconds']>75:raise SystemExit('pilot failed or oversized')
 with ProcessPoolExecutor(max_workers=14) as ex:
  for f in as_completed([ex.submit(work,j) for j in jobs[1:]]):
   r=f.result();rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print(r['job']['id'],r['status'],r.get('relative_nonscalar_norm'),r['seconds'],r.get('error',''),flush=True)
