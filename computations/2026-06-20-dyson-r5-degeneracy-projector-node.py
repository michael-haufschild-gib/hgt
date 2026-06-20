# THE MACHINE R5 (dyson). NODE = eigenvalue (near-)multiplicity -> eigenvector basis UNSTABLE,
# but spectral PROJECTOR + heat kernel well-defined (basis-independence constraint).
import numpy as np
# symmetric family M(s) with an eigenvalue crossing at s=0: M = [[s, g],[g, -s]] (eigs +/-sqrt(s^2+g^2))
def M(s,g): return np.array([[s, g],[g,-s]],float)
def topvec(s,g):
    w,v=np.linalg.eigh(M(s,g)); return v[:,np.argmax(w)]
def proj_top(s,g):
    w,v=np.linalg.eigh(M(s,g)); k=np.argmax(w); p=v[:,k:k+1]; return p@p.T
def heat_trace(s,g,t=1.0):
    w=np.linalg.eigvalsh(M(s,g)); return np.sum(np.exp(-t*w))

for g in [0.2, 0.01, 0.0]:   # gap=2g; g=0 is exact degeneracy
    ss=np.linspace(-0.3,0.3,7)
    # eigenvector instability: max jump in top eigenvector across the sweep
    vjump=max(np.linalg.norm(np.abs(topvec(ss[i+1],g))-np.abs(topvec(ss[i],g))) for i in range(len(ss)-1))
    pjump=max(np.linalg.norm(proj_top(ss[i+1],g)-proj_top(ss[i],g)) for i in range(len(ss)-1))
    hjump=max(abs(heat_trace(ss[i+1],g)-heat_trace(ss[i],g)) for i in range(len(ss)-1))
    print(f"gap=2g={2*g:.3f}: eigvec max-jump={vjump:.3f}  PROJECTOR max-jump={pjump:.3f}  heat-trace max-jump={hjump:.4f}")
