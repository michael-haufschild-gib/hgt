"""comp11 / rt#39: detection law d*(gamma,delta). Inject FE quartet {1/2+-delta+-i*gamma0}
into exact zeta moments; d* = first d with lambda_min(H^0_inj, M_triv)<0 (M_triv always PD,
so this is genuine off-line detection, no Cholesky-fail). Print signed lambda_min through the
flip so the transition is verifiable (not precision noise). Grid: one gamma0 per run, deltas."""
import sys, mpmath as mp, importlib.util
def imp(n,f):
    s=importlib.util.spec_from_file_location(n,f); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
H=imp("hgtlib","hgtlib.py")
g0=mp.mpf(sys.argv[1]); deltas=[mp.mpf(x) for x in sys.argv[2].split(',')]
DMAX=int(sys.argv[3]); DPS=int(sys.argv[4])
mp.mp.dps=DPS
Tbase=H.T_moments_exact(2*DMAX+1)
Bfull=H.Mtriv_matrix(DMAX)
subB=lambda d: mp.matrix([[Bfull[i,j] for j in range(d+1)] for i in range(d+1)])
Lcache={d:mp.inverse(mp.cholesky(subB(d))) for d in range(2,DMAX+1)}
def lammin(Tinj,d):
    A=H.H0_matrix(d,Tinj); Li=Lcache[d]; C=Li*A*Li.T; C=(C+C.T)/2
    return min(mp.eigsy(C,eigvals_only=True))
print(f"# gamma0={mp.nstr(g0,6)}  dps={DPS}  dmax={DMAX}")
for de in deltas:
    Tinj=H.add_quartet_moments(Tbase, mp.mpf('0.5')+de, g0)
    dstar=None; trail=[]
    for d in range(2,DMAX+1):
        m=lammin(Tinj,d); trail.append((d,m))
        if m<0 and dstar is None:
            dstar=d
            # verify: also check d+1 stays negative (clean flip, not noise)
            mnext=lammin(Tinj,d+1) if d<DMAX else m
            stable = (mnext<0)
            break
    if dstar:
        around=" ".join(f"d{d}:{('+' if v>0 else '-')}{float(mp.log10(abs(v))):.0f}" for d,v in trail[-4:])
        print(f"  delta={mp.nstr(de,4)}: d*={dstar} (flip {'clean' if stable else 'NOISY?'})  [..{around}]",flush=True)
    else:
        last=trail[-1]
        print(f"  delta={mp.nstr(de,4)}: d*>{DMAX} (lambda_min still +, log10={float(mp.log10(abs(last[1]))):.0f} at d={DMAX})",flush=True)
