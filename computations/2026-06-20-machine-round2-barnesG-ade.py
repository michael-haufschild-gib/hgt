#!/usr/bin/env python3
# THE MACHINE — Round 2. Object: BARNES G-function G(z) (max-far from partial-theta/Lambert-sigma_k).
# Why status plausibly open here: G is a multiple-gamma object; its LOW-ORDER nonlinear-ADE catch-status
# vs Gamma has not been put through this validated instrument. PRE-REGISTERED (seed 3089404714896536260):
#   predict RESIST up to (2,2), conf ~0.7 (G built from the logGamma integral, Hoelder-type) -> if so it is
#   a BOUNDARY-MARKER (one-sidedness S78: resist != HT-claim), and Barnes-G hypertranscendence is catalogued
#   -> catalogued-adjacent boundary-marker. A low-order CATCH would REFUTE the prediction = a real surprise.
# Instrument = the validated nonlinear-ADE catch-probe (jet-curve on a degree-D algebraic hypersurface),
# ANALYTIC jets (no mp.diff precision floor). Barnes-G analytic derivatives are VERIFIED vs mp.diff first.
import mpmath as mp, itertools, sys

def L1(z):  # candidate d/dz log G(z) = 1/2 ln(2pi) + 1/2 - z + (z-1) psi(z)   [VERIFY before trust]
    return mp.mpf(1)/2*mp.log(2*mp.pi) + mp.mpf(1)/2 - z + (z-1)*mp.digamma(z)
def L2(z):  # d/dz of L1 = -1 + psi(z) + (z-1) psi'(z)
    return -1 + mp.digamma(z) + (z-1)*mp.polygamma(1, z)

def verify_barnesg_jet(dps=60):
    mp.mp.dps = dps
    ok = True
    for z in [mp.mpf('1.37'), mp.mpf('2.6'), mp.mpf('3.9')]:
        G   = mp.barnesg(z)
        l1  = L1(z); l2 = L2(z)
        Gp  = G*l1
        Gpp = G*(l1*l1 + l2)
        Gp_num  = mp.diff(mp.barnesg, z, 1)
        Gpp_num = mp.diff(mp.barnesg, z, 2)
        e1 = abs(Gp-Gp_num)/abs(Gp_num);  e2 = abs(Gpp-Gpp_num)/abs(Gpp_num)
        good = (e1 < mp.mpf(10)**-(dps-15)) and (e2 < mp.mpf(10)**-(dps-15))
        ok = ok and good
        print(f"  z={float(z):.2f}  relerr G'={float(e1):.1e}  G''={float(e2):.1e}  {'OK' if good else 'MISMATCH'}")
    return ok

def jet_barnesg(x, R):
    G = mp.barnesg(x); l1 = L1(x); l2 = L2(x)
    return [G, G*l1, G*(l1*l1+l2)][:R+1]
def jet_exp(x, R):  e = mp.e**x; return [e]*(R+1)
def jet_gam(x, R):
    g = mp.gamma(x); p0 = mp.digamma(x); p1 = mp.polygamma(1, x)
    return [g, g*p0, g*(p0*p0+p1)][:R+1]

def monos(nv, D):
    out=[]
    for tot in range(D+1):
        for c in itertools.combinations_with_replacement(range(nv), tot):
            e=[0]*nv
            for i in c: e[i]+=1
            out.append(tuple(e))
    return out
def cluster_rows(jet, lo, hi, R, D, npts):
    xs=[mp.mpf(lo)+(mp.mpf(hi)-mp.mpf(lo))*mp.mpf(i+1)/mp.mpf(npts+1) for i in range(npts)]
    ms=monos(R+2, D); rows=[]
    for x in xs:
        v=[x]+jet(x, R)
        rows.append([mp.fprod([v[k]**e[k] for k in range(R+2)]) for e in ms])
    return rows, len(ms)
def sigratio(jet, A, B, R, D, NTR=40, NTE=24):
    rA,nm=cluster_rows(jet, A[0],A[1], R,D, NTR); rB,_=cluster_rows(jet, B[0],B[1], R,D, NTE)
    M=mp.matrix(rA+rB)
    for j in range(nm):
        cs=mp.sqrt(mp.fsum(M[i,j]**2 for i in range(M.rows)))
        if cs!=0:
            for i in range(M.rows): M[i,j]=M[i,j]/cs
    S=mp.svd_r(M, compute_uv=False)
    return mp.fdiv(min(S), max(S)), nm

funcs={
 'exp[CTRL catch]':   (jet_exp,    (0.4,1.2),(2.0,2.8)),
 'Gamma[CTRL resist]':(jet_gam,    (1.2,2.0),(3.5,4.5)),
 'BarnesG[TARGET]':   (jet_barnesg,(1.3,2.1),(3.4,4.4)),
}
grid=[(1,1),(1,2),(1,3),(2,1),(2,2)]
TOL=mp.mpf(10)**-18

def run(dps):
    mp.mp.dps=dps
    print(f"\n=== dps={dps}  TOL={float(TOL):.0e}  sigma_min/sigma_max ; [E]=relation EXISTS (catch) ===")
    print("func               "+"".join(f"({R},{D})    " for (R,D) in grid))
    res={}
    for name,(jet,A,B) in funcs.items():
        row=[]; res[name]={}
        for (R,D) in grid:
            try: o,nm=sigratio(jet,A,B,R,D); fo=float(o); ex=(o<TOL)
            except Exception as e: fo=float('nan'); ex=False
            res[name][(R,D)]=(fo,ex); row.append((fo,ex))
        print(f"{name:18s} "+"".join((f"{fo:.0e}{'E' if ex else ' '} " if fo==fo else " nan    ") for (fo,ex) in row))
    return res

print("VERIFY Barnes-G analytic jet vs mp.diff:")
if not verify_barnesg_jet(60):
    print("ABORT: analytic Barnes-G jet does not match mp.diff -> formula wrong, refusing to trust probe.")
    sys.exit(1)
r80 =run(80)
r120=run(120)
print("\n-- dps-STABILITY (80 vs 120) for BarnesG[TARGET] --")
for (R,D) in grid:
    a=r80['BarnesG[TARGET]'][(R,D)][0]; b=r120['BarnesG[TARGET]'][(R,D)][0]
    same = (a==a and b==b and abs(a-b) < 1e-3*max(abs(a),abs(b),1e-99))
    print(f"  ({R},{D}): dps80={a:.2e}  dps120={b:.2e}  {'STABLE' if same else 'DRIFTS->underflow/catch'}")
print("\n-- MINIMAL (R,D) with a relation (catch) else RESISTS (boundary-marker) @dps120 --")
for name in funcs:
    hit=[(R,D) for (R,D) in grid if r120[name][(R,D)][1]]
    if hit:
        mn=min(hit,key=lambda rd:(rd[0],rd[1])); print(f"{name:18s} CATCH at (R,D)={mn}")
    else: print(f"{name:18s} RESISTS up to {grid[-1]}")
