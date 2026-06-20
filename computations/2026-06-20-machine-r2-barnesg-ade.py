#!/usr/bin/env python3
# THE MACHINE — Round 2. Object: BARNES G-function (multiple-gamma cell) — maximally far from
# R1 partial-theta / prior Lambert / theta q-series rounds. In the pool "multiple-Gamma / Barnes-G".
# WHY status informative: Barnes G obeys a DIFFERENCE relation G(z+1)=Gamma(z)G(z) (a 2nd native axis)
# while its DIFFERENTIAL status should mirror logGamma (HT, no ADE). Instruments the multiple-gamma
# cell on the differential axis + records the 2-axis (difference-caught / differential-resist) datum.
#
# PRE-REGISTER (Wheeler, seed 2599920945872091226, move=attack-false):
#   BarnesG RESISTS the differential nonlinear-ADE probe at all accessible (R,D)<=(2,2), dps-stable
#   (sits at the HT/logGamma control floor, NOT at a genuine 0 like exp). Confidence 0.8.
#   attack-false on this: could G be secretly low-order DA? No native ADE known; G is built from
#   logGamma-type transcendence (Hoelder-class). If it CATCHES at low order that would be the surprise.
#   Controls: exp CATCHES (1,1) [genuine 0]; logGamma RESISTS (HT floor). Same jet method (mp.diff)
#   for all, so the control floor calibrates BarnesG's verdict. dps 80 vs 120 must agree.
import mpmath as mp, itertools

GRID=[(1,1),(1,2),(2,1),(2,2)]
NTR=22; NTE=14                       # rows = 36 > max cols (R=2,D=2: vars4 -> C(6,2)=15)

def monos(nv,D):
    out=[]
    for tot in range(D+1):
        for c in itertools.combinations_with_replacement(range(nv),tot):
            e=[0]*nv
            for i in c: e[i]+=1
            out.append(tuple(e))
    return out

def jet(f,x,R):                      # numerical jet via mp.diff (same method for all funcs)
    return [mp.diff(f,x,k) for k in range(R+1)]

def rows_for(f,lo,hi,R,D,npts):
    xs=[mp.mpf(lo)+(mp.mpf(hi)-mp.mpf(lo))*mp.mpf(i+1)/mp.mpf(npts+1) for i in range(npts)]
    ms=monos(R+2,D); rows=[]
    for x in xs:
        v=[mp.mpf(x)]+jet(f,x,R)
        rows.append([mp.fprod([v[k]**e[k] for k in range(R+2)]) for e in ms])
    return rows,len(ms)

def test(f,A,B,R,D):
    rA,nm=rows_for(f,A[0],A[1],R,D,NTR); rB,_=rows_for(f,B[0],B[1],R,D,NTE)
    M=mp.matrix(rA+rB)
    for j in range(nm):
        cs=mp.sqrt(mp.fsum(M[i,j]**2 for i in range(M.rows)))
        if cs!=0:
            for i in range(M.rows): M[i,j]=M[i,j]/cs
    S=mp.svd_r(M,compute_uv=False)
    return float(min(S)/max(S)),nm

# functions: (callable, intervalA, intervalB-far)
def f_exp(t):   return mp.e**t
def f_gam(t):   return mp.loggamma(t)      # logGamma = HT control (differential)
def f_bg(t):    return mp.log(mp.barnesg(t))  # log Barnes G (differential axis)
FUN={
 'exp':     (f_exp,(0.4,1.2),(2.0,2.8)),
 'logGamma':(f_gam,(1.3,2.1),(3.4,4.2)),
 'logBarnesG':(f_bg,(1.6,2.4),(3.6,4.4)),
}

for dps in (80,120):
    mp.mp.dps=dps
    print(f"\n==== dps={dps}  (smin/smax; small => GLOBAL algebraic relation EXISTS at that (R,D)) ====")
    hdr="func          "+"".join(f"({R},{D})    " for (R,D) in GRID); print(hdr)
    for name,(f,A,B) in FUN.items():
        row=[]
        for (R,D) in GRID:
            try: o,_=test(f,A,B,R,D)
            except Exception as e: o=float('nan')
            row.append(o)
        print(f"{name:13s} "+"".join((f"{o:.1e}  " if o==o else "  nan     ") for o in row))
print("\nREAD: exp -> ~0 at (1,1) [catch]. logGamma -> conditioning floor [resist].")
print("      logBarnesG: CATCH if << logGamma floor & drops at dps120; RESIST if ~= logGamma floor & dps-stable.")
