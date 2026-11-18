# Two Vaughan cutoffs detect every right-hand zero

**Stage** 3-formalized. **Type** Theorem (Lean).

Put $b_V=\delta-\mathbf1*\mu_{\le V}$ and $D_{V,W}(s)=\sum_{n\le W} b_V(n)n^{-s}$. For every zero $\rho$ with $1/2<\beta=\Re\rho<1$, every sufficiently large $V$, and every $W\ge V^2$, at least one of $D_{V,W}(\rho),D_{V,2W}(\rho)$ is nonzero. The associated restricted ordinary Mangoldt convolution has a pole at $\rho$ for any finite choice of prime head.

**Proof.** Sum the truncated divisor convolution first over the divisor $d$. Euler summation for $\sum_{k\le W/d} k^{-s}$ gives the integral $(W/d)^{1-s}/(1-s)$, the constant $\zeta(s)$ and error at most $C(s)(W/d)^{-\Re s}$. Multiplying the error by $|\mu(d)d^{-s}|$ and summing costs at most $C(s)VW^{-\Re s}$. At $s=\rho$ the constant term vanishes. Writing $H_V=\sum_{d\le V}\mu(d)/d$, the result is
$$D_{V,W}(\rho)=1-H_V W^{1-\rho}/(1-\rho)+O_\rho(VW^{-\beta}).$$

Put $r=2^{1-\rho}$. The difference $D_{V,2W}(\rho)-rD_{V,W}(\rho)$ equals $1-r+O_\rho(V^{1-2\beta})$. Since $|r|=2^{1-\beta}>1$, the difference stays away from zero. For ordinary primes, deleting the head through $U$ changes $-\zeta'/\zeta$ by a finite Dirichlet polynomial. Multiplication by $D_{V,W}$ gives residue $-mD_{V,W}(\rho)$, where $m$ is the zero multiplicity. The proof applies separately to every strip zero without a common height or separation bound.

**Lean** `norm_dyadic_shortCofactor_sub_le`, `restrictedPrimeSeries_residue_at_zero`, `eventually_dyadic_shortCofactor_detects_zero`, and `riemannHypothesis_iff_cofinal_restrictedPrimeResidues`. [Cofactor estimate](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheShortVaughanCofactorAtAZetaZero.lean) · [Ordinary prime residues](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheRestrictedPrimeConvolutionsDetectEveryRightZero.lean)

## Equivalent condition on integer counts

Let $E(N)=\psi(N)-N$ and $C_{V,W}(N)=\sum_{d\le\min(N,W)}b_V(d)E(\lfloor N/d\rfloor)$. RH holds exactly when for each $1/2<b<1$, arbitrarily large $V$ have $C_{V,W}(N)=O_{b,V,W}(N^b)$ at both $W=V^2$ and $W=2V^2$.

The finite hyperbola identity gives $C$ as the partial sum of $(\Lambda-\mathbf1)*(b_V\mathbf1_{[1,W]})$. Its Dirichlet series on $\Re s>1$ equals $(-\zeta'/\zeta-\zeta)D_{V,W}$. The count bound supplies a holomorphic continuation on $\Re s>b$ by partial summation. The meromorphic identity theorem identifies the two continuations there. At a right zero $\rho$ their residues must agree, forcing $D_{V,W}(\rho)=0$. Applying this at both cutoffs with $b<\Re\rho$ contradicts the dyadic estimate. Conversely RH bounds $E(N)$ by $O_b(N^b)$ at each such $b$, and the cofactor sum is finite. [Formal count equivalence](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/PairedCofactorBoundsForOrdinaryPrimeCounts.lean)

Deleting the actual long-prime head through $U$ changes $C_{V,W}(N)$ by the prefix of $\Lambda_{\le U}*(b_V\mathbf1_{[1,W]})$. This prefix is constant for $N\ge UW$ and bounded for all $N$. Thus the same equivalence holds for the literal long-prime convolution, for any function $U=U(V)$. [Restricted count theorem](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/PairedCofactorBoundsForOrdinaryPrimeCounts.lean#L280)
