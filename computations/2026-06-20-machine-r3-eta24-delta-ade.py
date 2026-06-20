#!/usr/bin/env python3
# THE MACHINE — Round 3. Object: Delta = eta^24 (modular discriminant; ETA-QUOTIENT cell).
# rng-picked (seed pick), move=extreme-cases. Maximally far from R2 Barnes-G.
# WHY status informative: Delta lives in the quasimodular ring C[E2,E4,E6] (trdeg 3) -> it satisfies an
# ORDER-3 ADE in delta=q d/dq (4 jets in a trdeg-3 field are dependent) BUT of HIGH DEGREE (Delta=
# (E4^3-E6^2)/1728 -> the closing relation is ~degree 6 in the jets). EXTREME-CASES prediction: order is
# low (3) yet degree is the binding constraint -> the cheap grid (degree<=3) RESISTS at the HT/logGamma
# floor, a DIFFERENT failure mode from HT (high-degree-DA vs no-ADE), both at the same numeric floor.
#
# PRE-REGISTER (Wheeler): Delta RESISTS (3,3) at the logGamma floor, dps80==dps120 (degree-blind, NOT a
#   genuine 0 like exp, NOT an HT-claim). conf 0.75. exp CATCHES (1,1). logGamma RESISTS (HT floor).
import mpmath as mp, itertools

GRID=[(1,1),(2,2),(3,2),(3,3)]
NTR=24; NTE=16

def monos(nv,D):
    out=[]
    for tot in range(D+1):
        for c in itertools.combinations_with_replacement(range(nv),tot):
            e=[0]*nv
            for i in c: e[i]+=1
            out.append(tuple(e))
    return out

def jet_exp(x,R):
    e=mp.e**mp.mpf(x); return [e]*(R+1)
def jet_gam(x,R):
    return [mp.loggamma(x), mp.digamma(x), mp.polygamma(1,x), mp.polygamma(2,x)][:R+1]

def make_delta(K):
    sig=[0]*(K+1)
    for d in range(1,K+1):
        for m in range(d,K+1,d): sig[m]+=d
    def jet_delta(x,R):              # delta=q d/dq jets of Delta=eta^24, autonomous in (j0..j3)
        q=mp.mpf(x); qp=[q**k for k in range(K+1)]
        logD = mp.log(q) - 24*mp.fsum(mp.mpf(sig[k])/k*qp[k] for k in range(1,K+1))
        D   = mp.e**logD
        L1  = 1 - 24*mp.fsum(mp.mpf(sig[k])*qp[k]      for k in range(1,K+1))   # E2 = delta logD
        dL1 =   - 24*mp.fsum(mp.mpf(sig[k])*k*qp[k]    for k in range(1,K+1))   # delta E2
        d2L1=   - 24*mp.fsum(mp.mpf(sig[k])*k*k*qp[k]  for k in range(1,K+1))
        j0=D; j1=D*L1; j2=D*(L1*L1+dL1); j3=D*(L1**3+3*L1*dL1+d2L1)
        return [j0,j1,j2,j3][:R+1]
    return jet_delta

def rows_for(jet,lo,hi,R,D,npts):
    xs=[mp.mpf(lo)+(mp.mpf(hi)-mp.mpf(lo))*mp.mpf(i+1)/mp.mpf(npts+1) for i in range(npts)]
    ms=monos(R+2,D); rows=[]
    for x in xs:
        v=[mp.mpf(x)]+jet(x,R)
        rows.append([mp.fprod([v[k]**e[k] for k in range(R+2)]) for e in ms])
    return rows,len(ms)

def test(jet,A,B,R,D):
    rA,nm=rows_for(jet,A[0],A[1],R,D,NTR); rB,_=rows_for(jet,B[0],B[1],R,D,NTE)
    M=mp.matrix(rA+rB)
    for j in range(nm):
        cs=mp.sqrt(mp.fsum(M[i,j]**2 for i in range(M.rows)))
        if cs!=0:
            for i in range(M.rows): M[i,j]=M[i,j]/cs
    S=mp.svd_r(M,compute_uv=False)
    return float(min(S)/max(S))

for dps in (80,120):
    mp.mp.dps=dps
    jet_delta=make_delta(140)
    FUN={'exp':(jet_exp,(0.4,1.2),(2.0,2.8)),
         'logGamma':(jet_gam,(1.3,2.1),(3.4,4.2)),
         'Delta=eta^24':(jet_delta,(0.05,0.12),(0.20,0.27))}
    print(f"\n==== dps={dps}  smin/smax (small => algebraic relation EXISTS at (R,D)) ====")
    print("func            "+"".join(f"({R},{D})    " for (R,D) in GRID))
    for name,(jet,A,B) in FUN.items():
        row=[]
        for (R,D) in GRID:
            try: o=test(jet,A,B,R,D)
            except Exception: o=float('nan')
            row.append(o)
        print(f"{name:14s} "+"".join((f"{o:.1e}  " if o==o else "  nan     ") for o in row))
print("\nREAD: exp ~0 @(1,1) catch. logGamma = HT floor. Delta: RESIST if ~= logGamma floor & dps-stable")
print("      (=> degree-blind high-degree-DA, NOT HT, NOT a genuine 0); CATCH if << floor & drops w/ dps.")
