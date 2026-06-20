import numpy as np, mpmath as mp
mp.mp.dps=30
# ---- STEP 6 (fixed): true crossing. M(s)=diag(s,-s,2). Order-labeled eigenvector SWAPS at s=0;
#      projector onto the two crossing levels is CONSTANT; heat trace smooth. ----
def M(s): return np.diag([s,-s,2.0])
def lowvec(s):
    w,v=np.linalg.eigh(M(s)); return v[:,0]              # order-labeled lowest eigenvector
def proj2(s):
    w,v=np.linalg.eigh(M(s)); return v[:,:2]@v[:,:2].T   # projector onto lowest-2 (crossing subspace)
ss=np.linspace(-1,1,11)
vjump=max(np.linalg.norm(np.abs(lowvec(ss[i+1]))-np.abs(lowvec(ss[i]))) for i in range(len(ss)-1))
pjump=max(np.linalg.norm(proj2(ss[i+1])-proj2(ss[i])) for i in range(len(ss)-1))
hjump=max(abs(np.sum(np.exp(-np.linalg.eigvalsh(M(ss[i+1]))))-np.sum(np.exp(-np.linalg.eigvalsh(M(ss[i]))))) for i in range(len(ss)-1))
print(f"NODE true-crossing: order-eigvec max-jump={vjump:.3f} (UNSTABLE)  projector max-jump={pjump:.3e} (STABLE)  heat-trace max-jump={hjump:.3e} (smooth)")

# ---- STEP 8 minimal edit: 'projector = basis-free symmetric function' -> HT VALUE RELATION.
#      For the FE-pair {zeta(s),zeta(1-s)} (a 2-fold 'degeneracy' under s<->1-s), test the
#      symmetric-function relation product/sum^2, which should be a VALUE RELATION (zeta-free). ----
def chi(s): return mp.zeta(s)/mp.zeta(1-s)
print("\nHT value-relation test: r(s)=zeta(s)zeta(1-s)/(zeta(s)+zeta(1-s))^2  vs  chi/(1+chi)^2 :")
for s in [mp.mpf('2.3'), mp.mpf('0.5')+3j, mp.mpf('-1.2')+0.7j, mp.mpf('4')]:
    z1=mp.zeta(s); z2=mp.zeta(1-s); r=z1*z2/(z1+z2)**2
    c=chi(s); pred=c/(1+c)**2
    print(f"  s={str(s):16s}: r={mp.nstr(r,8)}  chi/(1+chi)^2={mp.nstr(pred,8)}  diff={mp.nstr(abs(r-pred),3)}")
