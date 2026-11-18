# Sifting the integer density in the large-prime cells

**Route** PVC. **Stage** 3-formalized.

For $R=\lfloor X^\alpha\rfloor$, $\alpha=10^{-5}$, let $v_R$ be the [centered factorial weight](pvc-reciprocal-phases-near-the-square-root.md) on $X^{1/2+\alpha}<m\le X/R$. There is a square-root approximation to $\psi(X)-X$ on this interval by
$$
\sum_m v_R(\lfloor X/m\rfloor)
\left(\mathbf1_{m\text{ prime}}\log m-
\frac{P}{\varphi(P)}\mathbf1_{(m,P)=1}\right),
\qquad P=\prod_{p\le c\log X}p
$$
with $c=1/400000$. Both terms are supported on integers free of every prime factor up to $\lfloor c\log X\rfloor$.

**Truncated divisor count.** Let $Z=1+\lfloor X^{1/2+\alpha}\rfloor$, and let $a$ be any real sequence whose sum on every integer interval differs from its length by at most $B$. For a divisor $k$, reverse the inequalities $Z\le m$, $kjm\le X$. With $T=X/(kZ)$ and $n=\lfloor T\rfloor$, the weighted floor count is
$$
\sum_{Z\le m\le X}a(m)\lfloor X/(km)\rfloor
=Z(TH_n-n)+O((B+1)T).
$$
The corpus half-reciprocal harmonic bounds give $TH_n-n=T(\log T+\gamma-1)+1/2+O(1/T)$. Indeed for $n\ge1$, $0\le T\log(T/n)-(T-n)\le1/n$ by the two elementary log inequalities, and $|T(H_n-\log n-\gamma)-1/2|\le1/(2n)$. For $0<T<1$, $|T\log T|\le1$ suffices.

**Cancellation of the density.** Write $v_R(j)=1+\sum_k c_k\lfloor j/k\rfloor$. The harmonic, factorial, and centering identities give $\sum c_k/k=0$, $\sum c_k(\log k)/k=1$, and $\sum c_k=2$. The three main terms of the truncated count therefore cancel the constant weight's $X-Z$. The surviving error is
$$
O\!\left((1+B)\left[1+(X/Z)\sum_k|c_k|/k\right]+(Z^2/X)\sum_k k|c_k|\right).
$$
Here $\sum k|c_k|\ll R^3$ since $k\ll R^2$ and the coefficient mass is $O(R)$. Also $\sum |c_k|/k\ll1+\log R$: the Möbius coefficients have at most harmonic mass and all exterior coefficients of size $O(R)$ occur at $k\ge R$. If $B\ll X^{\alpha/2}$ this gives $O(\sqrt X)$, using $1+\log R\ll X^{\alpha/2}$. The weight vanishes beyond $X/R$. Choose $P$ as the primorial of $\lfloor (\alpha/4)\log X\rfloor$; $P\le4^{(\alpha/4)\log X}\le X^{\alpha/2}$. The normalized coprime indicator has period $P$ and mass $P$. Two incomplete end periods give $B\le 2P$. Subtract its weighted count from the established ordinary-prime row and sum the errors against the absolute cofactor coefficients.

**Prime fluctuations inside each block.** Partition the integers into adjacent blocks of $H=\lfloor X^{\alpha/4}\rfloor$ consecutive integers. Replace the prime measure in each block by its mean log-prime mass, truncating the measure at $X$. The two measures agree on complete blocks. Their difference has interval discrepancy at most $2H\log X$, which is $O(X^{\alpha/2})$. Adding the unit density to this difference and applying the same truncated-floor bound shows that the signed prime excess of each block, divided by $H$, carries the entire row up to $O(\sqrt X)$. This removes all pointwise variation of primality inside polynomial-length blocks at the individual horizon.

**Lean.** [`high_density_bound`](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/DensityCancellationInTheLargeQuotientCells.lean) gives the discrepancy estimate for signed weights. [`roughPrimeExcess_support`, `rough_prime_excess_cofactors`, and `block_prime_excess_cofactors`](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/PrimeExcessInGrowingBlocks.lean) give the common sifted support and both uniform cofactor estimates. The three declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
