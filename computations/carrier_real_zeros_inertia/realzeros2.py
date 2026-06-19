import numpy as np
from mpmath import mp, zetazero
mp.dps = 30
N = 8
gammas = [float(zetazero(n).imag) for n in range(1, N+1)]

def carrier(z, poles): return sum(1.0/(p - z) for p in poles)
def pick_sig(poles, nodes, tol=1e-7):
    M=len(nodes); P=np.zeros((M,M),dtype=complex)
    for j in range(M):
        for k in range(M):
            P[j,k]=(carrier(nodes[j],poles)-np.conj(carrier(nodes[k],poles)))/(nodes[j]-np.conj(nodes[k]))
    P=0.5*(P+P.conj().T); w=np.linalg.eigvalsh(P)
    return int((w>tol).sum()), int((w<-tol).sum())

rng=np.random.default_rng(0)
nodes=list(rng.uniform(-30,30,16)+1j*rng.uniform(0.5,5,16))

print("=== RH-true: poles {±γ_n} all real ===")
poles=[g for g in gammas]+[-g for g in gammas]
print("  (n+,n-) =", pick_sig(poles,nodes), " κ₋ expect 0")

print("\n=== k off-line zeros, FE-correct QUADRUPLE {γ±iδ, -γ±iδ} per zero; predict κ₋ = 2k ===")
delta=0.7
for kp in [1,2,3]:
    poles=[]
    for i,g in enumerate(gammas):
        if i<kp:
            poles += [g+1j*delta, g-1j*delta, -g+1j*delta, -g-1j*delta]  # full FE quadruple
        else:
            poles += [g, -g]
    npos,nneg=pick_sig(poles,nodes)
    print(f"  k={kp} off-line: (n+,n-) = ({npos},{nneg})  -> κ₋ = {nneg}  (expect 2k = {2*kp})")
