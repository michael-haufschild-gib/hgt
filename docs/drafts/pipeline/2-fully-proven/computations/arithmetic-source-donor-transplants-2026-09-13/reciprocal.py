from experiment import *

def node_work(start):
    mp.mp.dps=60;r=dict(start=start);z=mp.mpc(*start)
    try:
        for it in range(55):
            v,n,e,N=raw_jets('D',z,2,True);step=v[0]/v[1]
            if abs(v[0])/n<mp.mpf('1e-42') and abs(step)<mp.mpf('1e-30'):break
            if abs(step)>.12:step*=mp.mpf('.12')/abs(step)
            z-=step
            if abs(mp.re(z))>2.5 or abs(mp.im(z))>=mp.mpf('.7849'):raise ArithmeticError('node domain escape')
        else:raise ArithmeticError('node iteration limit')
        z=mp.mpc(abs(mp.re(z)),abs(mp.im(z)));v,n,e,N=raw_jets('D',z,2,False);r.update(status='ok',root=enc(z),normalized_residual=str(abs(v[0])/n),correction=str(abs(v[0]/v[1])))
    except Exception as e:r.update(status='error',error=repr(e))
    return r
if __name__=='__main__':
    start=time.monotonic();cs=[controls(h) for h in ['R','D']];save('carrier-controls.json',cs)
    starts=[[str(x/10),str(y)] for x in range(0,19,2) for y in [.25,.45,.62,.72,.77,.783]];rr=[]
    with ProcessPoolExecutor(max_workers=14) as ex:
        for r in ex.map(node_work,starts):rr.append(r);save('node-search.json',dict(starts=starts,rows=rr))
    nodes=[]
    for r in rr:
        if r['status']=='ok' and not any(abs(dec(r['root'])-dec(q))<mp.mpf('1e-12') for q in nodes):nodes.append(r['root'])
    nodes.sort(key=lambda z:abs(dec(z)));save('dh-nodes.json',nodes)
    chosen=[z for z in nodes if abs(mp.re(dec(z)))>mp.mpf('1e-8')][:4]
    if not chosen:save('summary.json',dict(planned=0,rows=[],status='no qualifying source nodes; no transplant performed',preparation_seconds=time.monotonic()-start));raise RuntimeError('no qualifying source nodes')
    zz=json.loads(Path('nodes.json').read_text());m={a['host']:mp.mpf(a['second_moment']) for a in cs};jobs=[]
    for k,z in enumerate(chosen):
        jobs.append(dict(label='D-erase-'+str(k),host='D',remove=[z],insert=[],dh_node=z))
        for i in [0,4,7,8]:
            for mode in ['native','variance']:
                scale=mp.sqrt(m['D']/m['R']) if mode=='variance' else mp.mpf(1)
                jobs.append(dict(label=f'D-exchange-{k}-R{i}-{mode}',host='D',remove=[z],insert=[enc(dec(zz[i])*scale)],dh_node=z,donor_index=i,mode=mode))
        for i in [0,4]:jobs.append(dict(label=f'R-exchange-{i}-D{k}',host='R',remove=[zz[i]],insert=[z],dh_node=z,removed_index=i,mode='native'))
    run_jobs(jobs,dict(seconds=time.monotonic()-start,node_starts=len(starts),distinct_nodes=len(nodes),selected_nodes=chosen,controls='passed'))
