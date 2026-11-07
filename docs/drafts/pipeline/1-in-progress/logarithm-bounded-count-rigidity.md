# Bounded count distance for positive integer-norm systems

- **ID:** SPL-bounded-count
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Target:** A locally finite Beurling system with integer generator norms
  and `N(x)=⌊x⌋+O(1)` is the rational-prime system, including multiplicities.

## Proposed proof

Bounded count error bounds every jump, hence every norm-fibre cardinality.
If distinct generalized integers `u,v` share norm `m`, the `k+1` multisets
`j u+(k−j)v`, `0≤j≤k`, are distinct and share norm `m^k`. A label whose
multiplicities differ in `u,v` distinguishes them. Thus the norm map is injective.

Every positive integer then has multiplicity zero or one. Bounded count error
bounds the number of omitted integers, so only finitely many are omitted.
The existing theorem that eventual exact factorization forces rational primes
finishes the argument.

## Significance and boundary

This would extend the corpus's vanishing-error isolation gap to every bounded
error at slope one. The free commutative monoid of positive generators is
essential: arbitrary nonnegative integral multiplicative coefficients admit
bounded-error counterexamples. The result would not classify unbounded
subpower errors or determine the distance needed for one exceptional zero.

## Audit required

Formalize collision amplification, derive the fibre bound from actual finite
counts, and prove eventual exact factorization. Do not use `Set.ncard` without
finiteness: infinite fibres have `ncard=0`. Check prior literature before any
novelty claim. Lean proof not yet established.

## Stronger question exposed

Does every nonclassical integer-norm system have count discrepancy
`Ω(log x)` along some unbounded sequence? A collision at norm `m` gives a
jump of at least `k+1` at `m^k`, already forcing this scale. With injective
norms, a stronger linear deficit may hold whenever any integer is missing.
Indeed, if `r,r+1,mr,m(r+1)` are all represented, injectivity identifies the
two factorizations of `mr(r+1)`. The representations of `r` and `r+1` have
disjoint label support, since each label has integer norm at least two.
Cancellation then represents `m`. Thus a missing `m` forces at least one
missing element in each such quadruple, yielding a positive density of
omissions. This stronger claim requires a separate proof and audit.

Erdős records Beurling's `N(x)=x+o(log x)` rigidity conjecture for real
generator norms in [1977, pp. 68–69](https://www.renyi.hu/~p_erdos/1977-27.pdf).
Integer support is a genuine restriction; proving the proposed integer case
must not be reported as settling that general conjecture.
