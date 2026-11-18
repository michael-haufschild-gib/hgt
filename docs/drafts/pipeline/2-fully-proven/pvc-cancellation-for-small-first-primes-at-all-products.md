# Cancellation for small first primes at all products

**PVC · Paper theorem.** For $T\ge1$, $D,R\ge1$ and every $L$, the complementary-factor slice satisfies
$$
\left|\sum_{L<v\le T}g_D(v)w_R(\lfloor T/v\rfloor)\right|
\ll (D+1)^2R^3(1+\log T)T^{0.49}.
$$
Consequently all $p\le X^{1/200}$ can be removed from the coprime ordinary-prime row at square-root precision up to logarithms, uniformly in the lower product endpoint.

**Proof.** For $v\le T^{0.49}$ use $|g_D|\ll D+1$ and $|w_R|\ll R$. For $v>T^{0.51}$ there are at most $T^{0.49}$ quotients. Each quotient fibre remains an interval after truncation, and every interval sum of $g_D$ is $O(D+1)$.

For $T^{0.49}<v\le T^{0.51}$, the signed divisor expansion of $g_D(v)$ tests $e\mid v$ for $e\le 2(D+1)$ and costs $O(D+1)$ in coefficient mass. Expansion of $w_R$ costs $O(R)$ and gives centered fractional parts $\{T/(dv)\}-1/2$ with $d\le128(128R^2+1)$. Write $v=et$ and subdivide the resulting integer interval dyadically. Each nonempty block $[P,B)$ has $T^{0.49}\le eP$ and $P\le T^{0.51}$. Set $Z=T/(de)$ and $\lambda=Z/(4P^3)$. Then $P\sqrt\lambda\le T^{0.255}$ and $1/\sqrt\lambda\le 2de\,T^{0.265}$. The [integer reciprocal-block estimate](pvc-centered-fractional-parts-on-integer-blocks.md) with $\Delta=T^{-0.04}$ bounds the block by $O(de\,T^{0.47})$. The number of blocks is $O(1+\log T)$. Multiplication by the two stencil masses proves the slice estimate.

Put $T=\lfloor X/p\rfloor$, $L=\lfloor Y/p\rfloor$ and sum over $p\le X^{1/200}$. Chebyshev bounds their total logarithmic mass by $7X^{1/200}$, giving $O((D+1)^2R^3(1+\log X)X^{0.495})$. Enforcing coprimality costs $O((D+1)R\sqrt X(1+\log X))$ by the [prime-multiple slice bound](../3-formalized/pvc-cancellation-on-repeated-prime-factors.md) and Mertens. For logarithmic cutoffs the two estimates hold at every divided horizon and hence at both Vaughan widths.
