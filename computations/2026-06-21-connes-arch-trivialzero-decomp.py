"""
Cross-check the DERIVED closed-form archimedean decomposition (guards the residue/sign algebra):
  Q_arch[p] = -4 p(-4)^2 + sum_{j>=1} (2j+1/2)^{-2} p(-(2j+1/2)^{-2})^2
against the Hankel built from the verified polygamma S_k^A. Pure archimedean -- no zeros needed.
Trivial sum done EXACTLY via Hurwitz zeta (no truncation): with p^2=sum_l b_l y^l,
  sum_{j>=1}(2j+1/2)^{-2}p(y_j)^2 = sum_l b_l (-1)^l 2^{-2(l+1)} ( zeta(2(l+1),1/4) - 4^{2(l+1)} ).
args: d
"""
import sys, mpmath as mp
mp.mp.dps=60
d=int(sys.argv[1]) if len(sys.argv)>1 else 6
def SA(k): return 2**(2*k+1)-mp.polygamma(2*k-1,mp.mpf(1)/4)/(2**(2*k)*mp.factorial(2*k-1))
# a deterministic non-trivial real polynomial
c=[mp.mpf(((3*i+1)%7)-3)+mp.mpf(1)/(i+2) for i in range(d+1)]
def p(y): return mp.fsum(c[i]*y**i for i in range(d+1))
# (a) Hankel: T^A_k=(-1)^k SA(k)
QaH=mp.fsum(c[i]*c[j]*(-1)**(i+j+1)*SA(i+j+1) for i in range(d+1) for j in range(d+1))
# (b) derived decomposition; b_l = (c*c)_l
b=[mp.fsum(c[i]*c[l-i] for i in range(max(0,l-d),min(l,d)+1)) for l in range(2*d+1)]
pole=-4*p(-4)**2
triv=mp.fsum(b[l]*(-1)**l*mp.mpf(2)**(-2*(l+1))*(mp.zeta(2*(l+1),mp.mpf(1)/4)-mp.mpf(4)**(2*(l+1))) for l in range(2*d+1))
QaD=pole+triv
print(f"# arch trivial-zero decomposition cross-check, d={d}, dps={mp.mp.dps}")
print(f"Qa via Hankel(polygamma) = {mp.nstr(QaH,24)}")
print(f"Qa via -4p(-4)^2 + trivial-zero squares = {mp.nstr(QaD,24)}")
print(f"   pole term = {mp.nstr(pole,10)}   trivial-zero sum = {mp.nstr(triv,10)}")
print(f"rel diff = {mp.nstr(abs(QaH-QaD)/abs(QaH),5)}")
