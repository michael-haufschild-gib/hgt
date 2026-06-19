import numpy as np
from mpmath import mp, zetazero
mp.dps = 30
N = 8
gammas = [float(zetazero(n).imag) for n in range(1, N+1)]

def carrier(z, poles): return sum(1.0/(p - z) for p in poles)
def pick_sig(poles, nodes, tol=1e-9):
    M=len(nodes); P=np.zeros((M,M),dtype=complex)
    for j in range(M):
        for k in range(M):
            P[j,k]=(carrier(nodes[j],poles)-np.conj(carrier(nodes[k],poles)))/(nodes[j]-np.conj(nodes[k]))
    P=0.5*(P+P.conj().T); w=np.linalg.eigvalsh(P)
    return int((w>tol).sum()), int((w<-tol).sum()), np.sort(w)[:6]

delta=0.7
print("=== k off-line zeros, FE quadruple; nodes placed NEAR pole heights ±γ_i + small i·η ===")
for kp in [1,2,3,4]:
    poles=[]
    offheights=[]
    for i,g in enumerate(gammas):
        if i<kp:
            poles += [g+1j*delta, g-1j*delta, -g+1j*delta, -g-1j*delta]
            offheights += [g, -g]
        else:
            poles += [g, -g]
    # nodes: near each off-line pole height (resolve the negative squares) + some spread
    nodes=[]
    for h in offheights:
        nodes += [h+0.4j, h+1.0j]   # two nodes near each off-line height
    rng=np.random.default_rng(1)
    nodes += list(rng.uniform(-45,45,8)+1j*rng.uniform(0.5,4,8))
    npos,nneg,small=pick_sig(poles,nodes)
    print(f"  k={kp}: #nodes={len(nodes)} (n+,n-)=({npos},{nneg}) κ₋={nneg} expect 2k={2*kp}; smallest eigs={np.round(small,4)}")
