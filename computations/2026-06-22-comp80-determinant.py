"""comp80 / gpt/43 #10 — determinantal / tau-function identity for s_d; Jacobi-Krein <-> Jensen.

H^0_d = (T_{i+j+1}) is the HANKEL (Jensen/Turan) determinant matrix of the shifted seam-moment
sequence; RH <=> H^0_d >=0 forall d <=> all its leading Hankel determinants >0 (the Polya-Jensen
positivity).  The scalar gap is the Christoffel/Uvarov determinant ratio:
  s_d = 1/K_{H^0}(y_*,y_*),  K = v_*^T (H^0)^{-1} v_*,  v_*=(y_*^i).
Cramer/border:  v_*^T (H^0)^{-1} v_* = -det(B_d)/det(H^0_d),  B_d=[[H^0, v_*],[v_*^T, 0]]
  =>  s_d = -det(H^0_d)/det(B_d).
Matrix-determinant lemma:  det(H^0)=det(H^-)(1+a_* m_d),  H^-=H^0-a_* v_* v_*^T.
Verify both; exhibit the tau-function form; check the orthogonal-polynomial-norm (Jensen) link."""
import mpmath as mp, sys
sys.path.insert(0,'.')
from hgtlib import T_moments_exact, H0_matrix
A_STAR=mp.mpf('0.16'); Y_STAR=-A_STAR
def vy(y,d): return mp.matrix([[y**i] for i in range(d+1)])

def bordered(H0,vs,d):
    B=mp.zeros(d+2)
    for i in range(d+1):
        for j in range(d+1): B[i,j]=H0[i,j]
        B[i,d+1]=vs[i]; B[d+1,i]=vs[i]
    return B

print(f"{'d':>4} {'s_d (a+1/m)':>16} {'-detH0/detB':>16} {'rel.diff':>10} {'det-lemma rel':>14} {'detH0>0?':>9}")
Dprev=None
for d in (6,8,10,12,14):
    mp.mp.dps=int(6.5*d)+150
    T=T_moments_exact(2*d+2)
    H0=H0_matrix(d,T); vs=vy(Y_STAR,d); vv=vs*vs.T
    Hm=H0-A_STAR*vv
    H0inv=mp.inverse(H0); Hminv=mp.inverse(Hm)
    m_d=(vs.T*Hminv*vs)[0]; s_d=A_STAR+1/m_d
    K00=(vs.T*H0inv*vs)[0]
    # determinant forms
    dH0=mp.det(H0); dHm=mp.det(Hm); dB=mp.det(bordered(H0,vs,d))
    s_det = -dH0/dB
    reldiff = abs(s_d-s_det)/abs(s_d)
    # matrix-determinant lemma
    lemma = dHm*(1+A_STAR*m_d)
    lemma_rel = abs(dH0-lemma)/abs(dH0)
    print(f"{d:>4} {mp.nstr(s_d,8):>16} {mp.nstr(s_det,8):>16} {mp.nstr(reldiff,2):>10} {mp.nstr(lemma_rel,2):>14} {str(dH0>0):>9}")

print("\n=== tau-function / Hankel(Jensen)-determinant structure ===")
print(f"{'d':>4} {'detH0 (Hankel/Jensen)':>24} {'detH^-':>16} {'sign detH^-':>12} {'1+a*m_d=detH0/detH-':>20}")
for d in (6,8,10,12,14):
    mp.mp.dps=int(6.5*d)+150
    T=T_moments_exact(2*d+2)
    H0=H0_matrix(d,T); vs=vy(Y_STAR,d)
    Hm=H0-A_STAR*(vs*vs.T)
    dH0=mp.det(H0); dHm=mp.det(Hm)
    print(f"{d:>4} {mp.nstr(dH0,6):>24} {mp.nstr(dHm,6):>16} {('+' if dHm>0 else '-'):>12} {mp.nstr(dH0/dHm,8):>20}")

print("""
Reading: s_d = -det(H^0_d)/det(B_d) is the Christoffel/Uvarov determinant RATIO of the SAME Hankel
(Jensen/Turan) determinants that govern Polya-Jensen positivity. det(H^0)>0 forall d is the Hankel-
determinant positivity (= Q_0>=0 = H^0 PSD). det(H^-)<0 (inertia (d,1), one negative eigenvalue) so
1+a_*m_d = det(H^0)/det(H^-) < 0, i.e. a_*m_d<-1 is the Krein-threshold crossing in determinant form.
=> Jacobi-Krein (s_d, inertia) and Jensen/Hankel (det H^0 positivity) are the SAME object, linked by
the matrix-determinant lemma + the Cramer/Uvarov border.""")
print("DONE")
