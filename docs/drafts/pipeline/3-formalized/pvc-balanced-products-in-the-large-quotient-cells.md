# Balanced products in the large quotient cells

**Route** PVC. **Stage** 3-formalized.

Put $D=\lfloor X^{1/400000}\rfloor$, $R=\lfloor X^{1/100000}\rfloor$ and $Y=\lfloor X^{50001/100000}\rfloor$. Let $F_{D+1}$ be the [corrected divisor-floor prefix](pvc-log-factorial-middle-primes.md). Set $G_D(0)=0$, $G_D(t)=1-F_{D+1}(t)$ for $t>0$, and $g_D(v)=G_D(v)-G_D(v-1)$. With the outer centered factorial weight $w_R$,
$$
\psi(X)-X =
\sum_{\substack{u,v>D\\Y<uv\le X/R}}
\Lambda(u)g_D(v)w_R(\lfloor X/(uv)\rfloor)+O(\sqrt X).
$$
Every product is composite. The complementary coefficient has $|\sum_{v\le t}g_D(v)|\ll D+1$ uniformly in $t$.

**Inner count.** The corrected prefix equals one through $D$. Hence $g_D$ vanishes there. Define $B_D(n)=\sum_{uv=n,\ u,v>D}\Lambda(u)g_D(v)$. Summing over $n\le T$ telescopes the $v$-sum to $G_D(\lfloor T/u\rfloor)$. This is the factorial middle interval at cutoffs $D+1,D$. The zero reciprocal moment and unit log slope give
$$
\left|\sum_{n\le T}(\Lambda(n)-B_D(n))-T\right|
\ll (D+1)(1+\log(2D+2)+\log T)+(D+1)D.
$$
For $1\le T\le X$ the bound is $O(X^{1/200000})$ since $\log X\le400000X^{1/400000}$. Extend $\Lambda-B_D$ by one beyond $X$. Subtracting two prefix errors gives the same order for every interval. The [large-cell density estimate](pvc-sifting-the-large-complementary-prime-cells.md) therefore bounds its entire outer pairing by $O(\sqrt X)$.

**Mangoldt row.** The ordinary-prime pairing above $Y$ already carries $\psi(X)-X$. On the full range the outer square-root moment bounds the signed proper-power sum by $O(\sqrt X)$. The absolute cost below $Y$ is $O(R\sqrt Y)$ by the positive proper-power mass bound, hence $O(\sqrt X)$. This gives the same approximation for the high Mangoldt row. Subtract the inner density estimate. For the original cofactor sum at $X=\lfloor N/d\rfloor$, the combined error is $O(\sqrt N\sum_{d\le W}|b_V(d)|)$.

**Third factor.** Extend $w_R$ by zero at index zero. Since $w_R(j)=0$ for $1\le j<R$, the outer weight is the sum of its successive differences $h_R(k)$ over $R\le k\le X/(uv)$. Both $g_D$ and $h_R$ have bounded partial sums, respectively $O(D+1)$ and $O(R)$. Thus the signed sum is trilinear on $uvk\le X$ with all three factors growing.

**Lean.** [Interval discrepancy](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/IntervalDiscrepancyOfTwoGrowingFactors.lean), `balancedDensity_discrepancy`. [Trilinear identity and cofactor bound](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/BalancedProductsInTheLargePrimeCells.lean), `balancedProductRow_trilinear` and `balanced_product_cofactors`. Both use only `propext`, `Classical.choice`, and `Quot.sound`.
