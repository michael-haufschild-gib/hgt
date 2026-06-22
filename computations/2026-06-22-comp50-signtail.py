"""comp50 / rt#50 / gpt38-c6: sign-tail audit. R^P rank-1 in norm (comp16). Spectrally
truncate R^P to its top-r modes (largest |eig|); test the SIGN/value of the true margin
margin_r = lambda_min(M_triv + R^P_r, M_triv). Find smallest r recovering the tiny-positive
true margin. Also: removing the dominant NEGATIVE mode -> does positivity survive but with
wrong magnitude? Question is NOT 'is the remainder small' but 'can a rank-r approx flip/miss
the sign'. If r ~ d (need ALL modes) => low-rank routes formally dead."""
import sys, mpmath as mp, importlib.util
def imp(n,f):
    s=importlib.util.spec_from_file_location(n,f); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
H=imp("hgtlib","hgtlib.py")
def genmin(A,B):
    Li=mp.inverse(mp.cholesky(B)); C=Li*A*Li.T; return min(mp.eigsy((C+C.T)/2,eigvals_only=True))
for d in [8,12]:
    mp.mp.dps=int(6.5*d)+110
    T=H.T_moments_exact(2*d+1); A=H.H0_matrix(d,T); B=H.Mtriv_matrix(d); RP=(A-B)
    RP=(RP+RP.T)/2
    Evals,Q=mp.eigsy(RP)                    # RP = Q diag(Evals) Q^T
    order=sorted(range(d+1), key=lambda i:-abs(Evals[i]))   # by |eig| desc
    margin_true=genmin(A,B)
    print(f"d={d}: true margin = {mp.nstr(margin_true,5)} (log10={float(mp.log10(margin_true)):.1f})")
    print(f"     keep top-r modes of R^P, recompute margin:")
    rec=None
    for r in range(1,d+2):
        RPr=mp.zeros(d+1,d+1)
        for t in range(r):
            k=order[t]; qk=mp.matrix([Q[i,k] for i in range(d+1)])
            RPr+=Evals[k]*(qk*qk.T)
        Ar=B+RPr
        try: mr=genmin(Ar,B)
        except: mr=mp.mpf('nan')
        tag=""
        if mr<0: tag=" <-- WRONG SIGN (negative)"
        elif rec is None and abs(mr-margin_true)/abs(margin_true)<mp.mpf('0.5'): rec=r; tag=" <-- recovers true margin"
        if r<=4 or mr<0 or r==rec or r>=d:
            print(f"       r={r:2d}: margin={mp.nstr(mr,4)} (log10={float(mp.log10(abs(mr))):.1f}){tag}",flush=True)
    print(f"     => smallest r recovering true margin: {rec} (of {d+1})  -> {'LOW-RANK DEAD (needs ~all modes)' if rec and rec>=d else 'low-rank ok'}")
