# Coprime ordinary primes at both Vaughan widths

**Route** PVC. **Stage** 3-formalized.

At each divided horizon $X$, put $Y=\min(X,(D+1)\lfloor\sqrt X\rfloor)$. Let $Q(D,R,X)$ be
$$
\sum_{\substack{p>2(D+1)\\p\ \mathrm{prime}}}\log p
\sum_{\substack{Y<pv\le X\\(p,v)=1}}
g_D(v)w_R(\lfloor X/(pv)\rfloor).
$$
For $1\le D,R\le H$, $1\le X$ and $\log X\le H$, with $H\ge1$,
$$
|\psi(X)-X-Q(D,R,X)|\ll H^5\sqrt X.
$$
The summands vanish for $v\le D$ and for $pv>X/R$. Differencing $w_R$ therefore introduces a third argument $k\ge R$ with $pvk\le X$.

**Transfer to the product.** The centered factorial identity replaces $\psi(X)-X$ by the full Mangoldt pairing at cost $O(H^3)$. Below $Y$ this pairing is $O(RY)=O(H^2\sqrt X)$ by Chebyshev. Write $B_D(n)=\sum_{uv=n,\,u,v>D}\Lambda(u)g_D(v)$. The factorial middle-interval estimate bounds every prefix of $\Lambda-B_D-1$ through $X$ by $O(H^2)$. The [quotient-interval estimate](pvc-cancellation-on-repeated-prime-factors.md) costs $O(H^3\sqrt X)$ on $Y<n\le X$.

**Unit density.** Write $Z=Y+1$. Then $\sqrt X\le Z\le3H\sqrt X$. The [truncated unit-density estimate](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/DensityCancellationInTheLargeQuotientCells.lean) bounds its high pairing by $1+O(R^3 Z^2/X+(1+\log R)X/Z)$, hence $O(H^5\sqrt X)$. This accounts for the whole density before filtering the product.

**Removing factors.** Reindex the high pairing of $B_D$ by $u,v$. Each $u$ costs $O((D+1)R\sqrt{X/u})$ before its Mangoldt weight. Chebyshev bounds the total for $D<u\le2(D+1)$ by $O(H^3\sqrt X)$. Above $2(D+1)$ the [repeated-prime estimate](pvc-cancellation-on-repeated-prime-factors.md) removes every proper prime-power $u$ and every prime $u$ dividing $v$, at cost $O(H^3\sqrt X)$.

**One row for all exponents.** Taking $D=R=\lfloor1+\log X\rfloor$ yields a single coprime row with error $O(\sqrt N(1+\log N)^5\sum_{d\le W}|b_V(d)|)$ at every width.

**Polynomial cutoffs.** Fix $1/2<b<1$. Set $\delta=(b-1/2)/10$ and $D=R=\lfloor X^\delta\rfloor$. Take $H=(1+1/\delta)X^\delta$, using $\log X\le X^\delta/\delta$. The error is $O_b(X^{1/2+5\delta})$, with $1/2+5\delta<b$. At $X=\lfloor N/d\rfloor$, summing costs $O_b(N^{1/2+5\delta}\sum_{d\le W}|b_V(d)|)$ at both widths. The remaining signed correlation is entirely over ordinary primes coprime to their long complementary factor.

**Lean.** [Adjustable product interval](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/PrimeCountsOnAdjustableProductIntervals.lean), `adjustable_product_bound`. [Coprime prime rows](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/CoprimeOrdinaryPrimeFactorsAtBothWidths.lean), `coprime_prime_support`, `coprime_prime_row_bound`, `logarithmic_coprime_cofactors`, and `coprime_prime_cofactors`. All four declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.
