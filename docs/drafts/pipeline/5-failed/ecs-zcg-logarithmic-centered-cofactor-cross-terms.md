# Centered correlations of ordinary prime weights

**Obstruction.** At the nested cofactor ratio six, the correlation through $X$ is exactly $X-\psi(X)$. Indeed $6k$ always has two different prime divisors, so $\Lambda(6k)=0$. For each $0\le b<\Theta$, the correlation falls below $-X^b$ at arbitrarily large integers. A logarithmic bound for every centered off-diagonal is therefore false.

**Positive theorem.** For distinct $d,e\in(V,2V]$, put $g=\gcd(d,e)$, $a=e/g$, $b=d/g$ and $L=\operatorname{lcm}(d,e)$. On common products $Lk$, $2\le k\le X$, the centered correlation is exactly
$$X-1-R_a(X)-R_b(X).$$
Here $R_a(X)=\lfloor\log_p X\rfloor\log p$ if $a$ is a power of the prime $p$, and zero otherwise. Each deficit lies in $[0,\log X]$. Since $a,b$ are coprime nonunits, $ak,bk$ cannot both be prime powers when $k>1$. Expanding the centered product leaves the two individual deficits. For a nested pair with any non-prime-power ratio, the same argument gives the exact ordinary prime error above.

For $n>4V^2$ all uncentered prime columns of the octave have disjoint support at $n$. Thus their weighted sum has a pointwise diagonal square, and taking absolute values adds exactly the absolute contributions of its terms. Signed cancellation beyond this threshold must involve distinct integers.

**Lean** `centered_first_octave_overlap_bounds`, `first_octave_prime_sum_sq`, `first_octave_abs_prime_sum`, `centered_nested_dilation_eq_prime_error`, and `sixfold_centered_overlap_has_prime_excursions`. [Formal proof](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/CenteringDistinguishesNestedAndIncomparableCofactors.lean)
