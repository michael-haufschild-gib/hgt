"""
Push the chi_4 / character-decomposition lead analytically, with numerical guards.

The arch budget is the quarter-integer Hurwitz tower; its character split (mod 4) is
  ZETA_k = -2^{2k-1}(1-2^{-2k})zeta(2k)   [principal char: ALL odd integers]   (= -1/2 (2^{2k}-1)zeta(2k))
  BETA_k = -2^{2k-1} beta(2k)             [chi_4: odd character]
Question: is the principal (all-odd) sector PD and the chi_4 sector indefinite? If so, character
decomposition breaks the manifestly-positive residue-class (1 mod 4) budget into a PD principal part
plus an INDEFINITE chi_4 part -- i.e. it is the WRONG representation for a positivity proof.

Tests (pure arch, no zeros):
 (1) inertia(H^zeta), inertia(H^beta), inertia(H^{zeta+beta})  for several d;
 (2) verify the Hurwitz character identity zeta(2k,1/4)+/-zeta(2k,3/4) at a few k;
 (3) verify ZETA_k = -2^{2k-1} * sum_{m odd} m^{-2k}  (principal = all-odd-integer tower).
args: d dps
"""
import sys, mpmath as mp
d=int(sys.argv[1]) if len(sys.argv)>1 else 8
mp.mp.dps=int(sys.argv[2]) if len(sys.argv)>2 else 60
KMAX=2*d+1
q1=mp.mpf(1)/4; q3=mp.mpf(3)/4
def beta(s): return mp.mpf(4)**(-s)*(mp.zeta(s,q1)-mp.zeta(s,q3))
ZETA={k:-(mp.mpf(1)/2)*(2**(2*k)-1)*mp.zeta(2*k) for k in range(1,KMAX+1)}
BETA={k:-mp.mpf(2)**(2*k-1)*beta(2*k) for k in range(1,KMAX+1)}
def Hk(S):
    H=mp.matrix(d+1,d+1)
    for i in range(d+1):
        for j in range(d+1):
            k=i+j+1; H[i,j]=(-1)**k*S[k]
    return H
def inertia(S):
    E=mp.eigsy(Hk(S),eigvals_only=True); return sum(1 for e in E if e>0),sum(1 for e in E if e<0),min(E),max(E)
pZ,nZ,mnZ,mxZ=inertia(ZETA)
pB,nB,mnB,mxB=inertia(BETA)
ZB={k:ZETA[k]+BETA[k] for k in range(1,KMAX+1)}
pZB,nZB,mnZB,_=inertia(ZB)
print(f"# character sectors, d={d}, dps={mp.mp.dps}")
print(f"inertia(H^zeta principal) = ({pZ},{nZ})  min={mp.nstr(mnZ,3)} max={mp.nstr(mxZ,3)}")
print(f"inertia(H^beta  chi_4)    = ({pB},{nB})  min={mp.nstr(mnB,3)} max={mp.nstr(mxB,3)}")
print(f"inertia(H^{{zeta+beta}})    = ({pZB},{nZB})  min={mp.nstr(mnZB,3)}")
# (2) Hurwitz identity check at k=1,2
for k in (1,2,KMAX):
    lhs_sum=mp.zeta(2*k,q1)+mp.zeta(2*k,q3); rhs_sum=mp.mpf(4)**(2*k)*(1-mp.mpf(2)**(-2*k))*mp.zeta(2*k)
    lhs_dif=mp.zeta(2*k,q1)-mp.zeta(2*k,q3); rhs_dif=mp.mpf(4)**(2*k)*beta(2*k)
    print(f"k={k}: Hurwitz sum relerr={mp.nstr(abs(lhs_sum-rhs_sum)/abs(rhs_sum),3)}  diff relerr={mp.nstr(abs(lhs_dif-rhs_dif)/abs(rhs_dif),3)}")
# (3) ZETA_k = -2^{2k-1} sum_{m odd} m^{-2k}
for k in (1,2,KMAX):
    oddsum=mp.nsum(lambda m:(2*m+1)**(-2*k),[0,mp.inf])  # sum over odd m=2m+1
    pred=-mp.mpf(2)**(2*k-1)*oddsum
    print(f"k={k}: ZETA_k vs -2^(2k-1)*sum_odd relerr={mp.nstr(abs(ZETA[k]-pred)/abs(ZETA[k]),3)}")
