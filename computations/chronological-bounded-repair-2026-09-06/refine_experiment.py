"""Conditioning audit: compare BVLS and singular-mode prefix repair via linear programming.
Every returned vector is clipped to its box and scored on the original design.
Known feasible vectors survive increases in N/C. None of this is a Lean proof.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='4'
os.environ['OMP_NUM_THREADS']='4'
import json, pathlib, concurrent.futures, time
import numpy as np
from scipy.optimize import lsq_linear, linprog
from scipy.sparse import eye, hstack, vstack, csr_matrix
import experiment as ex


def candidates(n):
    A,e,t,_=ex.design(n,20)
    V,v,tv,_=ex.design(n,36,True)
    pool={1:[],2:[]}
    diagnostics=[]
    for C in [1,2]:
        previous=np.loadtxt(ex.OUT/('coeff_box%d_%d.csv'%(C,n)),delimiter=',',skiprows=1)[:,2]
        pool[C].append(('screening',previous))
        for scale in [1.,1e5]:
            fit=lsq_linear(scale*A,-scale*e,bounds=(-C,C),method='bvls',
                           tol=1e-14,max_iter=1000)
            a=np.clip(fit.x,-C,C)
            pool[C].append(('bvls_scale_%g'%scale,a))
            r=A@a+e
            diagnostics.append({'C':C,'scale':scale,'method':'bvls','status':int(fit.status),
                                'iterations':int(fit.nit),'energy':float(r@r)})
    u,s,vh=np.linalg.svd(A,full_matrices=False)
    projection=u.T@e
    # LP minimizes coefficient infinity norm after cancelling the first r orthogonal modes.
    B=vstack([hstack([eye(n),-np.ones((n,1))]),
              hstack([-eye(n),-np.ones((n,1))])],format='csr')
    costs=[]
    rank_limit=min(n,45,int(np.sum(s>1e-13*s[0])))
    for rank in range(1,rank_limit+1):
        target=-projection[:rank]/s[:rank]
        eq=np.column_stack([vh[:rank],np.zeros(rank)])
        fit=linprog(np.r_[np.zeros(n),1.],A_ub=B,b_ub=np.zeros(2*n),A_eq=eq,b_eq=target,
                    bounds=[(None,None)]*n+[(0,None)],method='highs',
                    options={'primal_feasibility_tolerance':1e-10,
                             'dual_feasibility_tolerance':1e-10})
        if not fit.success:
            costs.append({'rank':rank,'status':int(fit.status),'message':fit.message})
            break
        a=fit.x[:n]
        # Orthogonal correction removes solver feasibility tolerance before checking the box.
        a=a+vh[:rank].T@(target-vh[:rank]@a)
        actual_cost=float(np.max(np.abs(a)))
        costs.append({'rank':rank,'lp_minimum_box':float(fit.x[-1]),'corrected_box':actual_cost,
                      'singular_value':float(s[rank-1]),
                      'constraint_residual':float(np.max(np.abs(vh[:rank]@a-target)))})
        for C in [1,2]:
            if actual_cost<=C*(1+1e-10):
                pool[C].append(('singular_prefix_rank_%d'%rank,np.clip(a,-C,C)))
        if fit.x[-1]>2.0001: break
    best={}
    for C in [1,2]:
        if C==2: pool[C]+=pool[1]
        label,a=min(pool[C],key=lambda z:float(np.linalg.norm(A@z[1]+e)))
        best[C]=(label,a)
    np.savez_compressed(ex.OUT/('candidate_pool_%d.npz'%n),
                        box1=best[1][1],box2=best[2][1])
    return {'N':n,'best_labels':{str(C):best[C][0] for C in [1,2]},
            'solver_diagnostics':diagnostics,'singular_prefix_costs':costs,
            'design_condition_ratio':float(s[-1]/s[0]),'rank_limit':rank_limit}


def assess(n,C,a,origin):
    A,e,t,delta=ex.design(n,20)
    V,v,tv,_=ex.design(n,36,True)
    r=A@a+e
    vr=V@a+v
    g=A.T@r
    energy=float(vr@vr)
    regions=[tv<1/n,(tv>=1/n)&(tv<1),tv>=1]
    mu=ex.mobius(n)[1:]
    return {'l2_norm':float(np.sqrt(energy)),'energy':energy,'training_energy':float(r@r),
            'mesh_energy_difference':float(abs(energy-r@r)),
            'max_abs_coefficient':float(np.max(np.abs(a))),'coefficient_bound':C,'origin':origin,
            'quadrature_primal_dual_gap':2*float(a@g)+2*C*float(np.abs(g).sum()),
            'quadrature_dual_lower_bound':float(r@r)-2*float(a@g)-2*C*float(np.abs(g).sum()),
            'energy_regions_t_lt_1_over_n__middle__t_ge_1':[float(vr[z]@vr[z]) for z in regions],
            'first_quarter_mean_abs_deviation_from_mu':float(np.mean(np.abs(a[:max(1,n//4)]-mu[:max(1,n//4)]))),
            'first_eight_coefficients':a[:8].tolist(),
            'first_eight_mobius_deviations':(a[:8]-mu[:8]).tolist(),
            'harmonic_coefficient_sum':float(np.sum(a/np.arange(1,n+1))),
            'bound_active_count':int(np.sum(np.abs(a)>C-1e-6)),
            'left_tail_energy_bound':delta*(1+2*n)**2}


if __name__=='__main__':
    started=time.time()
    screening=json.loads((ex.OUT/'results.json').read_text())
    (ex.OUT/'screening_results.json').write_text(json.dumps(screening,indent=2))
    with concurrent.futures.ProcessPoolExecutor(max_workers=4) as pool:
        diagnostics=list(pool.map(candidates,ex.SIZES))
    previous={1:None,2:None}
    rows=[]
    for base,diag in zip(screening['results'],diagnostics):
        n=base['N']
        data=np.load(ex.OUT/('candidate_pool_%d.npz'%n))
        A,e,t,_=ex.design(n,20)
        selected={}
        for C in [1,2]:
            options=[(diag['best_labels'][str(C)],data['box%d'%C])]
            if previous[C] is not None:
                options.append(('padded_previous_N',np.pad(previous[C],(0,n-len(previous[C])))))
            if C==2: options.append(('included_box1_solution',selected[1][1]))
            label,a=min(options,key=lambda z:float(np.linalg.norm(A@z[1]+e)))
            selected[C]=(label,np.clip(a,-C,C))
            previous[C]=selected[C][1]
            base['models']['box%d'%C]=assess(n,C,selected[C][1],label)
            np.savetxt(ex.OUT/('coeff_box%d_%d.csv'%(C,n)),
                       np.column_stack([np.arange(1,n+1),ex.mobius(n)[1:],selected[C][1]]),
                       delimiter=',',header='k,mu_k,a_k',comments='',fmt=['%d','%d','%.17g'])
        k=np.arange(1,n+1)
        profile_t=np.geomspace(1e-6/n,20,1200)
        H=ex.bose_h(profile_t[:,None]*k)
        np.savez_compressed(ex.OUT/('profile_%d.npz'%n),t=profile_t,
                            raw=np.exp(-profile_t)+H@ex.mobius(n)[1:],
                            box2=np.exp(-profile_t)+H@selected[2][1])
        base['refinement']=diag
        (ex.OUT/('result_%d.json'%n)).write_text(json.dumps(base,indent=2))
        rows.append(base)
        print(json.dumps({'N':n,'box1':base['models']['box1']['l2_norm'],
                          'box2':base['models']['box2']['l2_norm'],
                          'origins':{str(C):selected[C][0] for C in [1,2]},
                          'last_rank_cost':diag['singular_prefix_costs'][-1]}),flush=True)
    screening['results']=rows
    screening['refinement_seconds']=time.time()-started
    screening['interpretation']='Validated feasible upper bounds; optimality is not certified.'
    (ex.OUT/'results.json').write_text(json.dumps(screening,indent=2))
    ex.make_plot(rows)
    print(json.dumps({'event':'refinement_complete','seconds':time.time()-started}),flush=True)
