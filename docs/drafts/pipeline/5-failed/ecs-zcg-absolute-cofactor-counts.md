# Absolute values in the two Vaughan counts

**Obstruction.** For every $c<2\log 2$, all sufficiently large $V$, every fixed $W\ge V^2$, and all sufficiently large $N$ (depending on $V,W,c$),
$$
\sum_{n\le N}|(b_{V,\le W}*(\Lambda-\mathbf1))(n)|>cN.
$$
Both widths in the signed RH criterion satisfy this lower bound. Taking absolute values before summing over the product cannot give the required sublinear estimate.

**Positive theorem.** Every individual coefficient of any finite real cofactor can be recovered from a signed average on ordinary prime multiples. For $f$ supported through $W$, $1\le d\le W$, $p>W$ prime, and $h=f*(\Lambda-\mathbf1)$,
$$
h(dp)=f(d)\log p-\sum_{e\mid d}f(e),\qquad
\lim_{N\to\infty}\frac1N\sum_{W<p\le N/d}h(dp)=\frac{f(d)}d.
$$
Only the divisor $d$ leaves a prime power in the complementary factor. All other divisors in the support divide $d$ and leave $p$ times a nonunit smaller than $p$. The limit follows from the prime number theorem and $\pi(X)=o(X)$. Products belonging to different $d$ are disjoint, so any subset of cofactors forces at least its absolute harmonic mass in the limiting lower bound for variation.

For $V<p\le V^2$ the Vaughan coefficient at $p$ is $-1$. These disjoint prime multiples alone have signed density $-\sum_{V<p\le V^2}1/p$, tending to $-\log 2$ as $V\to\infty$. The full signed density is zero by the prime number theorem for each of the finitely many dilations. The complement must therefore carry the opposite mass, giving the factor two.

**Lean** `centered_cofactor_at_prime_mul`, `tendsto_primeMultipleSum_div_product`, `eventually_cofactor_variation_gt`, and `vaughan_cofactor_linear_variation`. [Formal proof](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/PrimeMultiplesRecoverEachFiniteCofactor.lean)
