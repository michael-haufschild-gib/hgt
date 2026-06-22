"""comp7b: push K_d margin law to high d with honest, self-checked precision.
Fixed chunk dps; moments+matrices built ONCE (degree-d matrices are leading submatrices).
Self-check: recompute top-d margin at dps and dps+80; must agree to be trusted."""
import sys, time, mpmath as mp
import importlib.util
spec=importlib.util.spec_from_file_location("hgtlib","hgtlib.py"); H=importlib.util.module_from_spec(spec); spec.loader.exec_module(H)
dmin=int(sys.argv[1]); dmax=int(sys.argv[2]); DPS=int(sys.argv[3])
VEC_AT=set(int(x) for x in sys.argv[4].split(',')) if len(sys.argv)>4 else set()
gammas=H.load_zeros('zeros.txt', dmax+2)

def build(dps):
    mp.mp.dps=dps
    T=H.T_moments_exact(2*dmax+1)
    A=H.H0_matrix(dmax,T); B=H.Mtriv_matrix(dmax)
    return A,B
def margin_at(A,B,d,want_vec=False):
    sub=lambda Mx:mp.matrix([[Mx[i,j] for j in range(d+1)] for i in range(d+1)])
    Ad,Bd=sub(A),sub(B)
    L=mp.cholesky(Bd); Linv=mp.inverse(L); C=Linv*Ad*Linv.T; C=(C+C.T)/2
    if want_vec:
        E,Q=mp.eigsy(C); idx=min(range(len(E)),key=lambda i:E[i])
        q=mp.matrix([Q[r,idx] for r in range(d+1)]); c=Linv.T*q
        K=mp.eye(d+1)-C
        return E[idx], H.overlap_with_pole(c), abs(K[d,d]/K[0,0])
    E=mp.eigsy(C,eigvals_only=True); return min(E),None,None

t0=time.time(); A,B=build(DPS); print(f"# built moments+matrices at dps={DPS} in {time.time()-t0:.1f}s",flush=True)
print(f"# d   log10(margin)  e_d    t(s)  [overlap_u  K_dd/K_00]")
prev=None
for d in range(dmin,dmax+1):
    t=time.time(); m,ov,corner=margin_at(A,B,d,want_vec=(d in VEC_AT)); dt=time.time()-t
    if m<=0 or m<mp.mpf(10)**(-(DPS-40)):
        print(f"{d:3d}   PRECISION-LIMITED (margin~{mp.nstr(m,3)}, dps={DPS})"); prev=None; continue
    lg=float(mp.log10(m))
    es=f"{float(-mp.log(m/prev)/mp.log(gammas[d-1])):6.3f}" if prev else "  --  "
    extra=f"  {mp.nstr(ov,6)}  {mp.nstr(corner,4)}" if ov is not None else ""
    print(f"{d:3d}  {lg:13.4f}  {es}  {dt:4.1f}{extra}",flush=True); prev=m
# self-check at dmax with +80 digits
A2,B2=build(DPS+80); m1,_,_=margin_at(A,B,dmax); m2,_,_=margin_at(A2,B2,dmax)
agree=float(-mp.log10(abs(m1-m2)/abs(m2))) if m2>0 else float('nan')
print(f"# self-check d={dmax}: dps={DPS} vs {DPS+80} agree to ~{agree:.0f} digits (margin {mp.nstr(m2,6)})")
