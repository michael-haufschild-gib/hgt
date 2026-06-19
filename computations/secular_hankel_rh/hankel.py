import numpy as np
from mpmath import mp, zetazero
mp.dps = 30
N = 20
gammas = [complex(zetazero(n)) for n in range(1, N+1)]  # ρ = 1/2 + iγ; we work in z-coord with zeros ±γ
gam = [g.imag for g in gammas]   # heights γ_n (real if RH)

def secular_moments(zeros_z, kmax):
    # P_k = Σ over Ξ-zeros {±γ} of γ^{-k}+(-γ)^{-k}; zeros_z = list of z-coord zeros (could be complex)
    P=[]
    for k in range(kmax+1):
        s=sum((g**(-k) if k>0 else 1.0) + ((-g)**(-k) if k>0 else 1.0) for g in zeros_z)
        P.append(s)
    return P

def hankel_signature(zeros_z, m, tol=1e-9):
    P = secular_moments(zeros_z, 2*m)
    H = np.array([[P[i+j] for j in range(m+1)] for i in range(m+1)], dtype=complex)
    H = 0.5*(H+H.conj().T)
    w = np.linalg.eigvalsh(H)
    return int((w>tol).sum()), int((w<-tol).sum()), np.round(w,4)

m=5
print("=== RH-true: real Ξ-zeros ±γ_n (first %d) — secular-moment Hankel [P_{i+j}] ===" % N)
npos,nneg,w = hankel_signature(gam, m)
print(f"  Hankel size {m+1}: (n+, n-) = ({npos}, {nneg})   κ₋ expect 0 (PSD = Hamburger moment matrix)")

print("\n=== off-line: move k zeros γ→γ+iδ (δ=2.0); Hankel should lose positivity ===")
for kp in [1,2,3]:
    zz = [ (gam[i]+2.0j if i<kp else gam[i]) for i in range(N) ]
    npos,nneg,w = hankel_signature(zz, m)
    print(f"  k={kp} off-line: (n+, n-) = ({npos}, {nneg})  -> n- = {nneg}  (RH-broken ⟹ expect n- > 0)")
