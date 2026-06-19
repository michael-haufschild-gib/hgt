#!/usr/bin/env python3
"""
Decoupling test (Wheeler, 2026-06-19): is the prime large-values regime (argmax ||S_d||) DIFFERENT
from the RH-bearing collision regime (argmin lambda_min(I+S_d))?  And is dH_d PSD at the ||S||-max t?

Prediction (if the decoupling holds): t_rhomax != t_lammin, and dH_d(t_rhomax) >= 0 (PSD, all eig>=0),
i.e. the norm-maximizing resonance spreads roots (positive direction), harmless to lambda_min.

Reuses the relative-rho construction: A_d = mean_t H_d(t), S_d = A_d^{-1/2}(H_d-A_d)A_d^{-1/2}.
Reports per d: t at max ||S||, t at min lambda_min(I+S), |zeta(1/2+it)| at each (proxy for near/far-zero),
and the eigenvalue signs of dH_d at t_rhomax.
"""
import mpmath as mp
mp.mp.dps = 30
DMAX = 6
T0, T1, NT = 0.5, 80.0, 161
CD_GUARD = mp.mpf('1e-18')

def xi(s): return mp.mpf('0.5')*s*(s-1)*mp.power(mp.pi,-s/2)*mp.gamma(s/2)*mp.zeta(s)
def Xi(z): return xi(mp.mpf('0.5')+1j*z)
def tcoef(t,n): return [mp.re(c) for c in mp.taylor(Xi,mp.mpf(t),n)]
def jcoef(t,d):
    c=tcoef(t,d); return [mp.binomial(d,j)*c[j] for j in range(d+1)]
def psums(c,d):
    cd=c[d]; a=[c[j]/cd for j in range(d+1)]
    e=[(-1)**k*a[d-k] for k in range(d+1)]; p=[mp.mpf(d)]
    for k in range(1,2*d-1):
        s=mp.mpf(0); kk=min(k,d)
        for i in range(1,kk): s+=(-1)**(i-1)*e[i]*p[k-i]
        if k<=d: s+=(-1)**(k-1)*k*e[k]
        else: s+=(-1)**(d-1)*e[d]*p[k-d]
        p.append(s)
    return p
def hank(p,d): return mp.matrix([[p[i+j] for j in range(d)] for i in range(d)])
def sym(M,d): return mp.matrix([[(M[i,j]+M[j,i])/2 for j in range(d)] for i in range(d)])
def eigs(M,d): return sorted([mp.re(x) for x in mp.eigsy(sym(M,d),eigvals_only=True)])
def invsqrt(A,d):
    E,Q=mp.eigsy(sym(A,d)); D=mp.matrix(d,d)
    for i in range(d): D[i,i]=1/mp.sqrt(E[i])
    return Q*D*Q.T

tg=[T0+(T1-T0)*k/(NT-1) for k in range(NT)]
print(f"# decoupling probe dps={mp.mp.dps} DMAX={DMAX} t in [{T0},{T1}] NT={NT}")
for d in range(2,DMAX+1):
    Hs=[];tu=[]
    for t in tg:
        c=jcoef(t,d)
        if abs(c[d])<CD_GUARD*(abs(c[0])+1): continue
        Hs.append(hank(psums(c,d),d)); tu.append(t)
    A=mp.matrix(d,d)
    for H in Hs: A+=H
    A=A/len(Hs)
    try: Aih=invsqrt(A,d)
    except Exception as ex: print(f"d={d}: A not PD {ex}"); continue
    best_rho=-1; t_rho=None; H_at_rho=None
    best_lam=mp.mpf('1e9'); t_lam=None
    for t,H in zip(tu,Hs):
        S=Aih*(H-A)*Aih
        es=eigs(S,d); rho=max(abs(es[0]),abs(es[-1]))
        lam=eigs(Aih*H*Aih,d)[0]
        if rho>best_rho: best_rho=rho;t_rho=t;H_at_rho=H
        if lam<best_lam: best_lam=lam;t_lam=t
    # signature of dH_d at t_rho (= H_at_rho - A)
    dH_eigs=eigs(H_at_rho-A,d)
    npos=sum(1 for x in dH_eigs if x>0); nneg=sum(1 for x in dH_eigs if x<0)
    zr=abs(mp.zeta(mp.mpf('0.5')+1j*t_rho)); zl=abs(mp.zeta(mp.mpf('0.5')+1j*t_lam))
    print(f"d={d}: argmax||S|| t={mp.nstr(t_rho,5)} (|zeta|={mp.nstr(zr,4)}) | "
          f"argmin lam_min t={mp.nstr(t_lam,5)} (|zeta|={mp.nstr(zl,4)}) | "
          f"SAME_t={'Y' if t_rho==t_lam else 'N'} | dH(t_rho) eig signs: +{npos}/-{nneg} "
          f"{'PSD' if nneg==0 else 'NOT-PSD'}")
print("# done")
