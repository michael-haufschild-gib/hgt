from loop import *

def experiment(j):
 d=j['dim'];N=j['N'];x=float(j['x']);y=float(j['y']);delta=float(j['delta']);ell=float(j['ell']);pa=pb=.5 if d%2 else 0
 g=np.array([[1/np.sqrt(y),x/np.sqrt(y)],[0,np.sqrt(y)]]);C=np.array([[np.cosh(delta),-1j*np.sinh(delta)],[1j*np.sinh(delta),np.cosh(delta)]])
 base=Code(C@g,d,N,pa,pb);G=overlap(base,base);W,ev=inverse_root(G);rows=[];loss=np.zeros((d,d),complex);canonical=G/np.trace(G)
 for k in range(j['angles']):
  budget();theta=np.pi*k/j['angles'];rot=osc(1,theta);M=rot@np.diag([np.exp(ell/2),np.exp(-ell/2)])@rot.T
  target=Code(C@M@g,d,N,pa,pb);Gt=overlap(target,target);Wt,evt=inverse_root(Gt)
  Ap=M@base.A;prop=Code(Ap,d,N,pa,pb,base.pref*np.sqrt(base.A[0,1]/Ap[0,1]))
  K=Wt@overlap(target,prop)@W;L=(np.eye(d)-K.conj().T@K)/ell**2;L=(L+L.conj().T)/2
  ne=np.linalg.norm(W@overlap(prop,prop)@W-np.eye(d))
  if ne>1e-7:raise ValueError('unitarity control failed')
  if min(np.linalg.eigvalsh(L)) < -1e-5:raise ValueError('negative loss exceeds cancellation tolerance')
  loss+=L/j['angles'];rows.append(dict(theta=theta,K=matenc(K),loss=matenc(L),unitary_gram_error=float(ne)))
 mean=np.trace(loss).real/d;res=loss-mean*np.eye(d);loss_ev=np.linalg.eigvalsh(loss)
 return dict(average_loss=matenc(loss),loss_eigenvalues=loss_ev.tolist(),mean_loss=float(mean),relative_nonscalar_norm=float(np.linalg.norm(res)/np.linalg.norm(loss)),canonical_mixture_loss=float(np.trace(canonical@loss).real),gram_eigenvalues=ev.tolist(),gram_condition=float(max(ev)/min(ev)),angle_rows=rows)

def work(j):
 start=time.monotonic();r=dict(job=j)
 try:r.update(experiment(j));r['status']='ok'
 except Exception as e:r.update(status='error',error=repr(e))
 r['seconds']=time.monotonic()-start;save('case-'+str(j['id'])+'.json',r);return r
if __name__=='__main__':
 jobs=json.loads(Path('jobs.json').read_text());start=time.monotonic();rows=[];r=work(jobs[0]);rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print('pilot',r['status'],r['seconds'],r.get('error',''),flush=True)
 if r['status']!='ok' or r['seconds']>60:raise SystemExit('pilot failed or oversized')
 with ProcessPoolExecutor(max_workers=14) as ex:
  for f in as_completed([ex.submit(work,j) for j in jobs[1:]]):
   r=f.result();rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print(r['job']['id'],r['status'],r.get('relative_nonscalar_norm'),r.get('error',''),flush=True)
