# Bounded count distance for positive integer-norm systems

- **ID:** SPL-bounded-count
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Target:** A locally finite Beurling system with integer generator norms
  and `N(x)=⌊x⌋+O(1)` is the rational-prime system, including multiplicities.

## Proof

Bounded count error bounds every jump, hence every norm-fibre cardinality.
If distinct generalized integers `u,v` share norm `m`, the `k+1` multisets
`j u+(k−j)v`, `0≤j≤k`, are distinct and share norm `m^k`. A label whose
multiplicities differ in `u,v` distinguishes them. Thus the norm map is injective.

Every positive integer then has multiplicity zero or one. Bounded count error
bounds the number of omitted integers, so only finitely many are omitted.
The existing theorem that eventual exact factorization forces rational primes
finishes the argument.

## Significance and boundary

This extends the corpus's vanishing-error isolation gap to every bounded
error at slope one: the bounded sup-count-distance component of the rational
primes contains only that system. The free commutative monoid of positive generators is
essential: arbitrary nonnegative integral multiplicative coefficients admit
bounded-error counterexamples. The distance needed for one exceptional zero
remains open.

## Lean evidence

`SumProductArithmeticOfTheLogarithm/NormCollisionAmplification.lean` and
`CountDistanceRigidity.lean` pass direct Lean checks. Their namespace is
`GaloisForLFunctions.SumProductArithmeticOfTheLogarithm`.

* `bounded_intCount_iff_norm_injective`: bounded multiplicities force unique factorization.
* `count_distance_trichotomy`: the exact collision/missing-integer alternatives.
* `primes_of_bounded_count_error`: bounded error for actual finite balls forces
  a norm-preserving equivalence of labels with rational primes.

The capstones have axiom set `{propext, Classical.choice, Quot.sound}`.

All norm-fibre `ncard` comparisons explicitly establish finiteness. No external
novelty claim is made.

## Stronger result

The [count-distance floor](logarithm-count-distance-floor.md) gives every
nonclassical integer-norm system discrepancy `Ω(log x)` along an unbounded
sequence. A collision at norm `m` gives a
jump of at least `k+1` at `m^k`, forcing this scale. With injective
norms, a stronger linear deficit holds whenever any integer is missing.
Indeed, if `r,r+1,mr,m(r+1)` are all represented, injectivity identifies the
two factorizations of `mr(r+1)`. The representations of `r` and `r+1` have
disjoint label support, since each label has integer norm at least two.
Cancellation then represents `m`. Thus a missing `m` forces at least one
missing element in each such quadruple, yielding a positive density of
omissions. The linked card records the exact bounds and Lean status.

Erdős records Beurling's `N(x)=x+o(log x)` rigidity conjecture for real
generator norms in [1977, pp. 68–69](https://www.renyi.hu/~p_erdos/1977-27.pdf).
Integer support is a genuine restriction; proving the integer case
must not be reported as settling that general conjecture.
