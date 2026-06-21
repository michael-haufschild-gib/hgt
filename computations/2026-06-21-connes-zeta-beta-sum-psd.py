"""
Settle gpt/31 questions A/B: is Q_zeta + Q_beta a positive form, or does it have negative modes
(the claimed "battlefield")? Claim (from the proved trivial-zero decomposition):
  Q_zeta+Q_beta = 4 p(-4)^2 + R_d^A[p],  R_d^A[p]=sum_{j>=1}(2j+1/2)^{-2} p(-(2j+1/2)^{-2})^2,
which is positive-DEFINITE (4p(-4)^2>=0 plus the PD trivial-zero budget). So the zeta-vs-beta
opposition is a residue-class (chi_0 vs chi_4 mod 4) artifact of splitting one positive object;
the SUM has no negative modes.
Tests: (1) inertia of H^{zb}=[(-1)^k(ZETA+BETA)_{i+j+1}]  -- expect (d+1,0), PD;
       (2) cross-check Q^{zb}[p] = 4 p(-4)^2 + R_d^A[p] on a random p (R_d^A via Hurwitz, exact).
args: d dps
"""
import sys, mpmath as mp
d=int(sys.argv[1]) if len(sys.argv)>1 else 8
mp.mp.dps=int(sys.argv[2]) if len(sys.argv)>2 else 80
KMAX=2*d+1
q1=mp.mpf(1)/4; q3=mp.mpf(3)/4
def beta(s): return mp.mpf(4)**(-s)*(mp.zeta(s,q1)-mp.zeta(s,q3))
ZETA={k:-(mp.mpf(1)/2)*(2**(2*k)-1)*mp.zeta(2*k) for k in range(1,KMAX+1)}
BETA={k:-mp.mpf(2)**(2*k-1)*beta(2*k) for k in range(1,KMAX+1)}
ZB={k:ZETA[k]+BETA[k] for k in range(1,KMAX+1)}
H=mp.matrix(d+1,d+1)
for i in range(d+1):
    for j in range(d+1):
        k=i+j+1; H[i,j]=(-1)**k*ZB[k]
E=mp.eigsy(H,eigvals_only=True)
npos=sum(1 for e in E if e>0); nneg=sum(1 for e in E if e<0)
# cross-check on a random-ish real polynomial
c=[mp.mpf(((5*i+2)%9)-4)+mp.mpf(1)/(i+3) for i in range(d+1)]
def p(y): return mp.fsum(c[i]*y**i for i in range(d+1))
Qzb=mp.fsum(c[i]*c[j]*H[i,j] for i in range(d+1) for j in range(d+1))
# 4 p(-4)^2 + R_d^A   (R_d^A = sum_{j>=1}(2j+1/2)^{-2} p(y_j)^2; exact via Hurwitz on p^2 coeffs)
b=[mp.fsum(c[i]*c[l-i] for i in range(max(0,l-d),min(l,d)+1)) for l in range(2*d+1)]
RA=mp.fsum(b[l]*(-1)**l*mp.mpf(2)**(-2*(l+1))*(mp.zeta(2*(l+1),q1)-mp.mpf(4)**(2*(l+1))) for l in range(2*d+1))
pred=4*p(-4)**2+RA
print(f"# Q_zeta+Q_beta PSD test, d={d}, dps={mp.mp.dps}")
print(f"inertia(H^zb) = ({npos},{nneg})   min eig = {mp.nstr(min(E),4)}   (expect (d+1,0)=PD)")
print(f"Q^zb[p]            = {mp.nstr(Qzb,22)}")
print(f"4 p(-4)^2 + R_d^A  = {mp.nstr(pred,22)}")
print(f"   (4p(-4)^2={mp.nstr(4*p(-4)**2,8)}, R_d^A={mp.nstr(RA,8)})")
print(f"rel diff = {mp.nstr(abs(Qzb-pred)/abs(Qzb),5)}")
