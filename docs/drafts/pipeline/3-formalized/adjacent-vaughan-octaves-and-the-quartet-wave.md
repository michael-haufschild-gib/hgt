# Recovering the ordinary prime error from adjacent Vaughan octaves

**Stage** 3-formalized. **Type** Theorem (Lean).

Let $C_{V,W}(M)=\sum_{d\le\min(M,W)}b_V(d)[\psi(\lfloor M/d\rfloor)-\lfloor M/d\rfloor]$ and $A_t(M)=C_{t,2t}(M)$. For arbitrarily large $t$, the ordinary prime $p=2t+1$ isolates the entire Chebyshev error:
$$A_{t+1}(pN)-A_t(pN)=N-\psi(N)\qquad(N\ge0).$$

**Proof.** The first-octave cofactor equals $\mu(d)$ for $t<d\le 2t$ and vanishes elsewhere. Increasing $t$ by one removes $t+1$ and adds $2t+1$ and $2t+2$. Choose $p\equiv7\pmod8$ by Dirichlet's theorem. Both even endpoints are then divisible by four, and $\mu(p)=-1$. The difference of the two coefficient functions is exactly $-\mathbf1_{d=p}$. The finite hyperbola identity gives the displayed formula. [Pointwise identity and count theorem](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/AdjacentVaughanOctavesRecoverTheOrdinaryPrimeCount.lean)
