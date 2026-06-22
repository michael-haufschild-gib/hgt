"""comp7 / rt#35: high-degree K_d spectral law (EXACT zeta moments).
margin(d)=lambda_min(H^0,M_triv)=1-lambda_max(K_d). Track exponent e_d in
margin(d)/margin(d-1) ~ gamma_d^{-e_d}, lambda_max, and (selected d) dangerous-eigvec
overlap with pole u=(-4)^i and K_d corner concentration K_dd/K_00.
Open question: does e_d drift to the density value 4 past d=20; does eigvec stay ~0.97u?"""
import sys, time, mpmath as mp
import importlib.util
spec=importlib.util.spec_from_file_location("hgtlib","hgtlib.py"); H=importlib.util.module_from_spec(spec); spec.loader.exec_module(H)

dmin=int(sys.argv[1]); dmax=int(sys.argv[2])
VEC_AT=set(int(x) for x in sys.argv[3].split(',')) if len(sys.argv)>3 else set()

def dps_for(d):
    lg=float(mp.log10(mp.factorial(d)))
    return max(60, int(4.5*lg)+120)

gammas=H.load_zeros('zeros.txt', dmax+2)
prev=None
print(f"# d  dps   log10(margin)  e_d    lambda_max(K_d)         t(s)  [overlap_u  K_dd/K_00]")
for d in range(dmin,dmax+1):
    DPS=dps_for(d); mp.mp.dps=DPS
    t=time.time()
    T=H.T_moments_exact(2*d+1)
    A=H.H0_matrix(d,T); B=H.Mtriv_matrix(d)
    L=mp.cholesky(B); Linv=mp.inverse(L); C=Linv*A*Linv.T; C=(C+C.T)/2
    if d in VEC_AT:
        E,Q=mp.eigsy(C); idx=min(range(len(E)),key=lambda i:E[i]); margin=E[idx]
        q=mp.matrix([Q[r,idx] for r in range(d+1)]); c=Linv.T*q
        ov=H.overlap_with_pole(c); K=mp.eye(d+1)-C; corner=abs(K[d,d]/K[0,0])
        extra=f"  {mp.nstr(ov,6)}  {mp.nstr(corner,4)}"
    else:
        E=mp.eigsy(C, eigvals_only=True); margin=min(E); extra=""
    lmax=1-margin; dt=time.time()-t
    lg_m=float(mp.log10(margin)) if margin>0 else float('nan')
    if prev is not None and margin>0 and prev>0:
        e_d=float(-mp.log(margin/prev)/mp.log(gammas[d-1])); es=f"{e_d:6.3f}"
    else: es="  --  "
    print(f"{d:3d} {DPS:4d}  {lg_m:13.5f}  {es}  {mp.nstr(lmax,12):16s}  {dt:4.1f}{extra}", flush=True)
    prev=margin
