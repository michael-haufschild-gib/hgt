# A logarithmic floor for integer-norm count distance

- **ID:** SPL-count-distance-floor
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Target:** Every nonclassical positive integer-norm Beurling system has
  count discrepancy `Ω(log x)` along an unbounded sequence.

## Exact alternatives

Write `a(n)` for the finite number of generalized integers of norm `n`, and
`D(N)=Σ_{n≤N}a(n)−N`.

1. **Norm collision.** If distinct factorizations have common integer norm
   `m`, then `a(m^k)≥k+1`. Hence
   `k≤|D(m^k)|+|D(m^k−1)|`. A collision has `m≥2`, so this gives the
   logarithmic floor on a geometric sequence.
2. **Injective norm, missing integer.** If the norm is injective and `m≥2`
   is not represented, then at least `R/4` integers below `m(R+1)` are missing.
   In particular `D(m(4k+1))≤−k`, a linear deficit on this progression.
3. **Injective and surjective norm.** The existing exact-factorization theorem
   identifies the labels, with multiplicities, with rational primes.

All three production modules pass direct Lean checks:
`NormCollisionAmplification`, `CountDistanceRigidity`, and `LogarithmicCountFloor`,
under `GaloisForLFunctions/SumProductArithmeticOfTheLogarithm/`.
Capstone axiom audits return only `{propext, Classical.choice, Quot.sound}`.

## Argument for the missing-integer bound

If `r,r+1,mr,m(r+1)` are all represented, write their factorizations as
`u,v,w,z`. Injectivity gives `w+v=u+z`. The multisets `u,v` share no label:
an integer norm at least two cannot divide both `r` and `r+1`.
Consequently `u≤w`, and the remaining factorization `w−u` has norm `m`.

Thus each `1≤r≤R` has a missing member among those four integers. Each
missing integer occurs in at most four quadruples, because each of the four
maps of `r` is injective. All four entries are at most `m(R+1)`. Counting
incidences proves the deficit bound.

## From finite bounds to the logarithmic floor

In the collision case, choose `k≥N+1`. Since `m≥2`, both `m^k` and
`m^k−1` are at least `N`, and one discrepancy has magnitude at least `k/2`.
Both logarithms are at most `k log m`, so take `c=1/(2 log m)`.

In the missing-integer case, take `k=N+1` and `n=m(4k+1)`. The deficit
has magnitude at least `k`, while `log n≤n≤5mk`. Thus `c=1/(5m)` works.
An `o(log n)` bound with coefficient `c/2` contradicts either alternative
at a sufficiently large threshold `n≥2`.

## Scope and audit

This implies rigidity for integer-norm count error `o(log x)` and extends
the [bounded-error theorem](logarithm-bounded-count-rigidity.md). The integer
support restriction is essential. It does not settle Beurling's corresponding
real-norm conjecture recorded by [Erdős, 1977, pp. 68–69](https://www.renyi.hu/~p_erdos/1977-27.pdf).

No claim of a sharp upper construction, a constant uniform over all systems,
or the smallest distance supporting one exceptional zero is made. No claim
of external novelty is made.

## Lean declarations

Namespace `GaloisForLFunctions.SumProductArithmeticOfTheLogarithm`:

* `intCount_pow_ge_of_collision`: amplified norm multiplicities.
* `represent_of_cross`: consecutive-integer cancellation.
* `linear_deficit_of_missing`: the arithmetic-progression deficit.
* `count_distance_trichotomy`: classical labels or one of the two quantitative bounds.
* `primes_or_logarithmic_count_distance`: the unconditional logarithmic floor alternative.
* `primes_of_sublogarithmic_count_error`: `o(log n)` rigidity.
