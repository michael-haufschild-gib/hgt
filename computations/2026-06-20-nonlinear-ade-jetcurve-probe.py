#!/usr/bin/env python3
# NONLINEAR algebraic-differential (ADE) probe = discrete shadow of HÖLDER (Popper id=660).
# Revisualise (rng move): jet-curve J_R(x)=(x,f,f',...,f^(R)); "f satisfies an order-R degree-D ADE"
# <=> J_R lies on a degree-D algebraic hypersurface in jet-space. HT (Hölder) = lies on NONE at any
# finite (R,D). DISCRETE observable (S67-compliant, NOT a metric slope): does an exact relation EXIST,
# validated OUT-OF-SAMPLE (rank/yes-no), and the minimal (R,D). Evaluates f,f',f'' at POINTS via
# mpmath -> NO coefficient precision-wall.
#
# PRE-REGISTERED PREDICTION (DeWitt, seed 3792956044253267381):
#  DROP (differentially-algebraic): exp@(R1,D1) conf.95 ; tan@(R1,D2) [Riccati y'=1+y^2] conf.9 ;
#   sn(.,m=.37)@(R1,D4) [(y')^2=(1-y^2)(1-m y^2)] conf.85 ; besselJ0@(R2,D1) [linear] conf.85.
#  RESIST (HT, Hölder): Gamma, zeta -> NO out-of-sample-valid relation up to (R2,D4) conf.8.
#  SIGNATURE = diff-alg controls DROP at finite (R,D) while Gamma/zeta RESIST everywhere -> separates
#   HT from merely-diff-algebraic = the mission test. conf 0.7 it comes out clean.
#  REDUCE? expect: the BINARY (Gamma resists / tan drops) = Hölder = KNOWN; any GRADED "rate of
#   resistance" = metric -> S67 conformal-confound. So probably reduces; running to TEST that & report.
import numpy as np, mpmath as mp, itertools
mp.mp.dps=35
TOL=mp.mpf(10)**-18           # relation EXISTS if sigma_min/sigma_max < TOL (HIGH-PRECISION svd now)
NTR=40; NTE=24                # high-prec: fewer points suffice (rows > ncols, two intervals=globality)
# ANALYTIC jets (exact to full precision; mp.diff was the precision floor that masked true relations)
def jet_exp(x,R):  e=mp.e**x; return [e]*(R+1)
def jet_tan(x,R):  t=mp.tan(x); f1=1+t*t; f2=2*t*f1; return [t,f1,f2][:R+1]
def jet_sn(x,R,m=mp.mpf('0.37')):
    s=mp.ellipfun('sn',x,m); c=mp.ellipfun('cn',x,m); d=mp.ellipfun('dn',x,m)
    return [s, c*d, -s*(d*d+m*c*c)][:R+1]
def jet_bes(x,R): j0=mp.besselj(0,x); j1=mp.besselj(1,x); return [j0,-j1,-j0+j1/x][:R+1]
def jet_gam(x,R): g=mp.gamma(x); p0=mp.digamma(x); p1=mp.polygamma(1,x); return [g,g*p0,g*(p0*p0+p1)][:R+1]
def jet_zet(x,R): return [mp.zeta(x),mp.zeta(x,derivative=1),mp.zeta(x,derivative=2)][:R+1]
def monos(nv, D):             # exponent tuples over nv vars, total degree<=D
    out=[]
    for tot in range(D+1):
        for c in itertools.combinations_with_replacement(range(nv), tot):
            e=[0]*nv
            for i in c: e[i]+=1
            out.append(tuple(e))
    return out
def cluster_rows(jet, lo, hi, R, D, npts):
    xs=[mp.mpf(lo)+(mp.mpf(hi)-mp.mpf(lo))*mp.mpf(i+1)/mp.mpf(npts+1) for i in range(npts)]
    ms=monos(R+2,D); rows=[]
    for x in xs:
        v=[x]+jet(x,R)
        rows.append([mp.fprod([v[k]**e[k] for k in range(R+2)]) for e in ms])
    return rows, len(ms)
def test(jet, A, B, R, D):
    # GLOBALITY + HIGH PRECISION: stack two FAR-disjoint intervals; mpmath SVD (no float64 floor).
    rA,nm=cluster_rows(jet,A[0],A[1],R,D,NTR); rB,_=cluster_rows(jet,B[0],B[1],R,D,NTE)
    rows=rA+rB
    M=mp.matrix(rows)
    # column-equilibrate
    for j in range(nm):
        cs=mp.sqrt(mp.fsum(M[i,j]**2 for i in range(M.rows)))
        if cs!=0:
            for i in range(M.rows): M[i,j]=M[i,j]/cs
    S=mp.svd_r(M, compute_uv=False)   # singular values, high precision
    smax=max(S); smin=min(S)
    return smin/smax, nm
funcs={  # (jet, intervalA, intervalB-FAR)
 'exp':     (jet_exp,(0.4,1.2),(2.0,2.8)),
 'tan':     (jet_tan,(0.1,0.6),(0.9,1.4)),
 'sn_m.37': (jet_sn, (0.2,0.8),(2.5,3.1)),
 'besselJ0':(jet_bes,(0.5,1.5),(3.0,4.0)),
 'Gamma':   (jet_gam,(1.2,2.0),(3.5,4.5)),
 'zeta':    (jet_zet,(2.2,3.0),(4.0,5.0)),
}
grid=[(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)]
print(f"dps={mp.mp.dps} TOL={float(TOL):.0e}  HIGH-PREC sigma_min/sigma_max over FAR-disjoint A,B; [E]=GLOBAL relation EXISTS")
hdr="func       "+"".join(f"({R},{D})  " for (R,D) in grid); print(hdr)
res={}
for name,(jet,A,B) in funcs.items():
    row=[]; res[name]={}
    for (R,D) in grid:
        try: o,nm=test(jet,A,B,R,D); fo=float(o); ex=(o<TOL)
        except Exception as e: fo=float('nan'); ex=False
        res[name][(R,D)]=(fo,ex); row.append((fo,ex))
    print(f"{name:10s} "+"".join((f"{fo:.0e}{'E' if ex else ' '} " if fo==fo else " nan   ") for (fo,ex) in row))
print("\n-- MINIMAL (R,D) with a GLOBAL algebraic relation (else 'RESISTS') --")
for name in funcs:
    hit=[(R,D) for (R,D) in grid if res[name][(R,D)][1]]
    if hit:
        mn=min(hit, key=lambda rd:(rd[0],rd[1])); print(f"{name:10s} relation at (R,D)={mn}")
    else: print(f"{name:10s} RESISTS up to {grid[-1]}  <-- HT signature if Gamma/zeta")
