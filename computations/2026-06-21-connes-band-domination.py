"""
gpt/36 #7: is the domination -R^P <= M_triv scale-local or only global?
On the dangerous mode p_d (lambda_min eigvec of (Q_0,M_triv)), decompose by atom-scale:
  protector M_triv[p_d] = sum_j (2j+1/2)^{-2} p_d(y_j)^2   (trivial zeros, y_j<0)  -> per-band mass
  on-line   Q_0[p_d]    = sum_n 2 y_n p_d(y_n)^2           (zeros, y_n>0)          -> per-band mass
  -R^P[p_d] = M_triv[p_d] - Q_0[p_d].
Report where (which dyadic |y|-band) the protector mass and the Q_0 mass sit. If they live in DIFFERENT
bands, domination is global (cross-scale); if same band, it could localize.
args: N d dps
"""
import sys, mpmath as mp
N=int(sys.argv[1]) if len(sys.argv)>1 else 250
d=int(sys.argv[2]) if len(sys.argv)>2 else 10
mp.mp.dps=int(sys.argv[3]) if len(sys.argv)>3 else 130
KMAX=2*d+1; q1=mp.mpf(1)/4
with open("/root/gam_cache.txt") as f:
    hdr=f.readline().split(); gam=[mp.mpf(f.readline().strip()) for _ in range(N)]
TN=gam[-1]
def tail(k):
    pp=2*k-1; return (1/mp.pi)*TN**(-pp)/pp*(mp.log(TN/(2*mp.pi))+mp.mpf(1)/pp)
T={k:2*mp.fsum(g**(-2*k) for g in gam)+tail(k) for k in range(1,KMAX+1)}
def maMM(m): return (-1)**m*mp.mpf(2)**(-2*(m+1))*(mp.zeta(2*(m+1),q1)-mp.mpf(4)**(2*(m+1)))
H0=mp.matrix(d+1,d+1); MA=mp.matrix(d+1,d+1)
for i in range(d+1):
    for j in range(d+1): H0[i,j]=T[i+j+1]; MA[i,j]=maMM(i+j)
L=mp.cholesky(MA); Li=mp.inverse(L); G=Li*H0*Li.T; G=(G+G.T)/2
E,V=mp.eigsy(G); x=[V[i,0] for i in range(d+1)]
v=[mp.fsum(Li.T[i,j]*x[j] for j in range(d+1)) for i in range(d+1)]
def pd(y): return mp.fsum(v[i]*y**i for i in range(d+1))
# trivial-zero (protector) contributions
Jt=400
ctri=[((2*j+mp.mpf(1)/2)**(-2))*pd(-(2*j+mp.mpf(1)/2)**(-2))**2 for j in range(1,Jt+1)]
Mtot=mp.fsum(ctri)
# on-line zero (Q_0) contributions
con=[2*(gam[n]**(-2))*pd(gam[n]**(-2))**2 for n in range(N)]
Qtot=mp.fsum(con)
print(f"# band domination, N={N}, d={d}, dps={mp.mp.dps} (cache {hdr[0]}@{hdr[1]})")
print(f"# M_triv[p_d]={mp.nstr(Mtot,6)}  Q_0[p_d]={mp.nstr(Qtot,6)}  -R^P[p_d]=M-Q={mp.nstr(Mtot-Qtot,6)}")
# protector mass by trivial-zero index band
def frac_band(c,tot,lo,hi): return mp.fsum(c[k] for k in range(lo,min(hi,len(c))))/tot
print(f"# protector M_triv mass by trivial-zero j:  j1-3={mp.nstr(frac_band(ctri,Mtot,0,3),4)}  j4-20={mp.nstr(frac_band(ctri,Mtot,3,20),4)}  j21+={mp.nstr(frac_band(ctri,Mtot,20,Jt),4)}")
print(f"#   peak trivial-zero j*={max(range(Jt),key=lambda k:ctri[k])+1}")
print(f"# on-line Q_0 mass by zero n:  n1-3={mp.nstr(frac_band(con,Qtot,0,3),4)}  n4-20={mp.nstr(frac_band(con,Qtot,3,20),4)}  n21+={mp.nstr(frac_band(con,Qtot,20,N),4)}")
print(f"#   peak zero n*={max(range(N),key=lambda k:con[k])+1} (gamma={mp.nstr(gam[max(range(N),key=lambda k:con[k])],5)})")
# scale comparison: trivial-zero atoms |y_j| vs zero atoms y_n where mass peaks
jp=max(range(Jt),key=lambda k:ctri[k]); npk=max(range(N),key=lambda k:con[k])
print(f"# protector peak |y|={mp.nstr((2*jp+2.5)**(-2),4)}   Q_0 peak y={mp.nstr(gam[npk]**(-2),4)}  (ratio {mp.nstr((2*jp+2.5)**(-2)/gam[npk]**(-2),3)})")
