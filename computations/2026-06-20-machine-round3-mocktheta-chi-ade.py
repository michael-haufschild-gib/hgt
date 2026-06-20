#!/usr/bin/env python3
# THE MACHINE — Round 3. Object: RAMANUJAN 3rd-ORDER MOCK THETA chi(q) = sum_{n>=0} q^{n^2}/prod_{k=1}^n(1-q^k+q^{2k}).
# Max-far from R1 partial-theta / R2 Barnes-G (multiple-gamma). Why status plausibly OPEN: mock modular forms
# have NO modular-ODE (quasimodular ring) closure, so their differential-algebraic status in q is genuinely
# uncatalogued territory (unlike eta/E_k which are DA via Ramanujan). seed 772999101109405545.
# PRE-REGISTERED: predict RESIST up to (2,2), conf 0.55 (mock => no modular closure suggests not-low-order-DA;
#   genuinely uncertain = that's why it's open). A low-order CATCH would REFUTE "mock theta is HT-like" = surprise.
# Instruments: (i) validated nonlinear-ADE catch-probe (sigma_min/sigma_max, analytic jet, dps80 vs dps120);
#   (ii) discrete-height integer-rationalization cross-check on the target. One-sidedness S78: resist != HT-claim.
import mpmath as mp, itertools, sys
from math import gcd

NMAX = 60
def _terms(q):
    # returns lists t,A,Ap over n=0..NMAX where t_n=q^{n^2}/D_n, A_n=(log t_n)', A_n'=A_n'
    q = mp.mpf(q) if not isinstance(q, mp.mpf) else q
    ts=[]; As=[]; Aps=[]
    D = mp.mpf(1)              # D_n product
    S1 = mp.mpf(0)            # sum_{k<=n} d_k'/d_k
    S2 = mp.mpf(0)            # sum_{k<=n} (d_k'' d_k - d_k'^2)/d_k^2
    for n in range(0, NMAX+1):
        if n >= 1:
            k = n
            dk  = 1 - q**k + q**(2*k)
            dkp = k*q**(k-1)*(2*q**k - 1)
            dkpp= -k*(k-1)*q**(k-2) + 2*k*(2*k-1)*q**(2*k-2) if k>=2 else (2*k*(2*k-1)*q**(2*k-2))
            # k=1: -k(k-1)q^{k-2}=0 term vanishes; q**(k-2)=q**-1 avoided since coeff 0
            D = D*dk
            S1 = S1 + dkp/dk
            S2 = S2 + (dkpp*dk - dkp*dkp)/(dk*dk)
        t = q**(n*n)/D
        if n == 0:
            A = mp.mpf(0); Ap = mp.mpf(0)
        else:
            A  = mp.mpf(n*n)/q - S1
            Ap = -mp.mpf(n*n)/q**2 - S2
        ts.append(t); As.append(A); Aps.append(Ap)
    return ts, As, Aps

def chi_jet(q, R):
    ts, As, Aps = _terms(q)
    f=mp.mpf(0); f1=mp.mpf(0); f2=mp.mpf(0)
    for n in range(len(ts)):
        t=ts[n]; A=As[n]; Ap=Aps[n]
        f  += t
        f1 += t*A
        f2 += t*(A*A + Ap)
    return [f, f1, f2][:R+1]
def chi_val(q): return chi_jet(q,0)[0]

def jet_exp(x,R): e=mp.e**x; return [e]*(R+1)
def jet_gam(x,R):
    g=mp.gamma(x); p0=mp.digamma(x); p1=mp.polygamma(1,x); return [g,g*p0,g*(p0*p0+p1)][:R+1]

def verify_chi_jet(dps=50):
    mp.mp.dps=dps; ok=True
    for q in [mp.mpf('0.17'), mp.mpf('0.33'), mp.mpf('0.55')]:
        j=chi_jet(q,2)
        f1n=mp.diff(chi_val,q,1); f2n=mp.diff(chi_val,q,2)
        e1=abs(j[1]-f1n)/abs(f1n); e2=abs(j[2]-f2n)/abs(f2n)
        good=(e1<mp.mpf(10)**-(dps-18)) and (e2<mp.mpf(10)**-(dps-18))
        ok=ok and good
        print(f"  q={float(q):.2f} chi={float(j[0]):.6f} relerr f'={float(e1):.1e} f''={float(e2):.1e} {'OK' if good else 'MISMATCH'}")
    return ok

def monos(nv,D):
    out=[]
    for tot in range(D+1):
        for c in itertools.combinations_with_replacement(range(nv),tot):
            e=[0]*nv
            for i in c: e[i]+=1
            out.append(tuple(e))
    return out
def cluster_rows(jet,lo,hi,R,D,npts):
    xs=[mp.mpf(lo)+(mp.mpf(hi)-mp.mpf(lo))*mp.mpf(i+1)/mp.mpf(npts+1) for i in range(npts)]
    ms=monos(R+2,D); rows=[]
    for x in xs:
        v=[x]+jet(x,R)
        rows.append([mp.fprod([v[k]**e[k] for k in range(R+2)]) for e in ms])
    return rows,len(ms),ms
def build_M(jet,A,B,R,D,NTR=40,NTE=24):
    rA,nm,ms=cluster_rows(jet,A[0],A[1],R,D,NTR); rB,_,_=cluster_rows(jet,B[0],B[1],R,D,NTE)
    M=mp.matrix(rA+rB)
    for j in range(nm):
        cs=mp.sqrt(mp.fsum(M[i,j]**2 for i in range(M.rows)))
        if cs!=0:
            for i in range(M.rows): M[i,j]=M[i,j]/cs
    return M,nm,ms
def sigratio(jet,A,B,R,D):
    M,nm,_=build_M(jet,A,B,R,D); S=mp.svd_r(M,compute_uv=False)
    return mp.fdiv(min(S),max(S)),nm

# --- discrete-height cross-check (rationalize smallest right singular vector to integer height) ---
HMAX=10**6; TOLV=mp.mpf(10)**-40
def disc_height(jet,A,B,R,D):
    M,nm,ms=build_M(jet,A,B,R,D)
    U,S,V=mp.svd_r(M,compute_uv=True); v=[V[V.rows-1,j] for j in range(V.cols)]
    k=max(range(len(v)),key=lambda i:abs(v[i])); vn=[vi/v[k] for vi in v]
    nums=[]; dens=[]
    for vi in vn:
        if abs(vi)<mp.mpf(10)**-30: nums.append(0); dens.append(1); continue
        r=mp.pslq([vi,mp.mpf(1)],maxcoeff=HMAX,maxsteps=6000)
        if r is None or r[0]==0: return ('resist',None)
        a,b=r; nums.append(-b); dens.append(a)
    L=1
    for d in dens: L=L*d//gcd(L,d) if d!=0 else L
    c=[nums[i]*(L//dens[i]) for i in range(len(v))]; g=0
    for ci in c: g=gcd(g,ci)
    if g>1: c=[ci//g for ci in c]
    h=max(abs(ci) for ci in c)
    res=M*mp.matrix(c); rn=mp.sqrt(mp.fsum(res[i]**2 for i in range(M.rows)))
    cn=mp.sqrt(mp.fsum(ci**2 for ci in c)); rownorm=max(mp.sqrt(mp.fsum(M[i,j]**2 for j in range(M.cols))) for i in range(M.rows))
    return ('GLOBAL' if rn/(cn*rownorm+mp.mpf(10)**-50)<TOLV else 'spurious', h)

funcs={
 'exp[CTRL catch]':   (jet_exp,(0.4,1.2),(2.0,2.8)),
 'Gamma[CTRL resist]':(jet_gam,(1.2,2.0),(3.5,4.5)),
 'chi3[TARGET]':      (chi_jet,(0.10,0.30),(0.45,0.62)),
}
grid=[(1,1),(1,2),(1,3),(2,1),(2,2)]
TOL=mp.mpf(10)**-18
def run(dps):
    mp.mp.dps=dps
    print(f"\n=== dps={dps} TOL={float(TOL):.0e} sigma_min/sigma_max ; [E]=catch ===")
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

print("VERIFY chi3 analytic jet vs mp.diff:")
if not verify_chi_jet(50):
    print("ABORT: analytic chi jet != mp.diff -> formula wrong, refusing to trust probe."); sys.exit(1)
r80=run(80); r120=run(120)
print("\n-- dps-STABILITY (80 vs 120) chi3[TARGET] --")
for (R,D) in grid:
    a=r80['chi3[TARGET]'][(R,D)][0]; b=r120['chi3[TARGET]'][(R,D)][0]
    same=(a==a and b==b and abs(a-b)<1e-3*max(abs(a),abs(b),1e-99))
    print(f"  ({R},{D}): dps80={a:.2e} dps120={b:.2e} {'STABLE' if same else 'DRIFTS'}")
print("\n-- DISCRETE-HEIGHT cross-check on chi3[TARGET] @dps120 (integer ADE? else resist) --")
mp.mp.dps=120
for (R,D) in [(1,1),(1,2),(1,3)]:
    st,h=disc_height(chi_jet,(0.10,0.30),(0.45,0.62),R,D)
    print(f"  ({R},{D}): {st}"+(f" height={h}" if h is not None else ""))
print("\n-- MINIMAL (R,D) catch else RESISTS @dps120 --")
for name in funcs:
    hit=[(R,D) for (R,D) in grid if r120[name][(R,D)][1]]
    if hit:
        mn=min(hit,key=lambda rd:(rd[0],rd[1])); print(f"{name:18s} CATCH at {mn}")
    else: print(f"{name:18s} RESISTS up to {grid[-1]}")
