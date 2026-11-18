# Short factors in the dual prime window

**PVC · Formalized.** Let $X\ge1$, $1\le e\le X^{10^{-5}}$, and $Q=\lfloor X^{10^{-6}}\rfloor$. For $L+1\ge\sqrt X$, $U\le X^{1/2+10^{-9}}$, and any first-prime threshold $F$, one has
$$
\left|\sum_{1\le j\le Q}\beta_j\sum_{\substack{p>F\ \mathrm{prime}\\L<pj\le U}}\log(p)\left(\{X/(ejp)\}-\tfrac12\right)\right|
\ll \|\beta\|_\infty (1+\log X)\sqrt X .
$$

**Proof.** On each nonempty truncated dyadic prime block $[P,P')$, $X^{0.4999}\le P\le X^{0.5001}$. For the lower bound use $jX^{0.4999}\le\sqrt X\le L+1\le j(\lfloor L/j\rfloor+1)$. With $Z=X/(ej)$, the bounds on $e,j$ give $X^{0.9999}\le Z\le X$. Hence $P^{1.998}\le Z\le P^{2.002}$, and the [prime fractional-part estimate](../../../../formal/GaloisForLFunctions/PrimeExponentialSums/FractionalPartsOfReciprocalPrimes.lean) bounds the block by $O(P^{0.999})=O(X^{0.4997})$. The block count is $O(1+\log X)$. Summing over $j$ costs at most $X^{0.000001}$ and the claimed bound follows.

**Lean.** [`short_factor_prime_divisor_window`](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/ShortFactorsInTheDualPrimeWindow.lean).
