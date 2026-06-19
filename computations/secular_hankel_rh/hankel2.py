import numpy as np
from mpmath import mp, zetazero
mp.dps = 30
N = 20
gam = [float(zetazero(n).imag) for n in range(1, N+1)]

def moments_from_zeros(zeros, kmax):   # P_k = Σ_z z^{-k}; zeros = full z-coord zero list
    return [sum(z**(-k) for z in zeros) if k>0 else float(len(zeros)) for k in range(kmax+1)]

def hankel_sig(zeros, m, tol=1e-8):
    P = moments_from_zeros(zeros, 2*m)
    H = np.array([[P[i+j] for j in range(m+1)] for i in range(m+1)], dtype=complex)
    H = 0.5*(H+H.conj().T)
    w = np.linalg.eigvalsh(H.real if np.allclose(H.imag,0) else H)
    return int((w>tol).sum()), int((w<-tol).sum()), float(np.max(np.abs(H.imag)))

m=6
online = [g for g in gam] + [-g for g in gam]   # ±γ_n, all real
npos,nneg,imerr = hankel_sig(online, m)
print(f"=== RH-true (±γ_n real): Hankel size {m+1} (n+,n-)=({npos},{nneg}) maxImag={imerr:.1e}  expect n-=0 ===")

print("\n=== off-line via FE QUADRUPLE {γ±iδ,-γ±iδ} (δ=1.0); moments stay real; expect n- > 0 ===")
delta=1.0
for kp in [1,2,3]:
    zeros=[]
    for i,g in enumerate(gam):
        if i<kp: zeros += [g+1j*delta, g-1j*delta, -g+1j*delta, -g-1j*delta]
        else:    zeros += [g, -g]
    npos,nneg,imerr = hankel_sig(zeros, m)
    print(f"  k={kp}: (n+,n-)=({npos},{nneg})  n-={nneg}  maxImag(Hankel)={imerr:.1e}  (RH-broken ⟹ n->0 expected)")
