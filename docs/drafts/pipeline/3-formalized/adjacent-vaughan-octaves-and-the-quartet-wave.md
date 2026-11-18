# Recovering the ordinary prime error from adjacent Vaughan octaves

**Stage** 3-formalized. **Type** Theorem (Lean).

Let $C_{V,W}(M)=\sum_{d\le\min(M,W)}b_V(d)[\psi(\lfloor M/d\rfloor)-\lfloor M/d\rfloor]$ and $A_t(M)=C_{t,2t}(M)$. For arbitrarily large $t$, the ordinary prime $p=2t+1$ isolates the entire Chebyshev error:
$$A_{t+1}(pN)-A_t(pN)=N-\psi(N)\qquad(N\ge0).$$

**Proof.** The first-octave cofactor equals $\mu(d)$ for $t<d\le 2t$ and vanishes elsewhere. Increasing $t$ by one removes $t+1$ and adds $2t+1$ and $2t+2$. Choose $p\equiv7\pmod8$ by Dirichlet's theorem. Both even endpoints are then divisible by four, and $\mu(p)=-1$. The difference of the two coefficient functions is exactly $-\mathbf1_{d=p}$. The finite hyperbola identity gives the displayed formula. [Pointwise identity and count theorem](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/AdjacentVaughanOctavesRecoverTheOrdinaryPrimeCount.lean)

## Both confined rungs

Define $P_t(x)=A_{t+1}(p\lfloor x\rfloor)-A_t(p\lfloor x\rfloor)+x-\lfloor x\rfloor=x-\psi(x)$. Write $\rho=\beta+i\gamma$ for a right-hand strip zero and $m$ for its multiplicity. The unique-quartet condition is equivalent to
$$P_t(x)=2m\Re(x^\rho/\rho)+O(\sqrt{x}\log^2 x),\qquad x\ge16.$$

For every confined null vector $F$ under this quartet there are $a>0$ and $|\tau|\le\pi/|\gamma|$ such that
$$e^{17s/2}\operatorname{averagedState}(F,s)=aP_t(e^{s+\tau})+O_{F,\rho}\!\left(e^{s/2}(1+(s+\tau)^2)\right).$$
The estimate holds for $s>0$ with $e^{s+\tau}\ge16$. The cutoff $t$ is common to all states, including both rungs.

**Proof.** The confined-state expansion gives $2m\Re(A e^{(\rho-17/2)s})+O(e^{-8s})$ with $A\ne0$. Choose $\tau=\arg(\rho A)/\gamma$ and $a=|\rho A|e^{-\beta\tau}$. Then $ae^{\rho\tau}=\rho A$. Multiplying the state expansion by $e^{17s/2}$ makes its leading term exactly the leading term of $aP_t(e^{s+\tau})$. The two remainders give the displayed bound. [Formal characterization and state recovery](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheSingleQuartetWaveInAdjacentPrimeCounts.lean)
