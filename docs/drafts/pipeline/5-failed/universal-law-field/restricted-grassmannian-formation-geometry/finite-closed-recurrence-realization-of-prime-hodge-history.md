# Finite closed recurrence realization of prime--Hodge history

- **ID:** ULF-FCRI-001
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Conjecture:** the exact exit law of the pre-divisor defect `T` is the averaged first-return law
  of a finite-dimensional monitored unitary colligation.
- **Status:** `[FALSIFIED ON PAPER] [UNCONDITIONAL] [NOT LEAN CERTIFIED]`

## Why it looked viable

`T` has total exit mass one and finite mean `7/4`.  Finite-dimensional quantum subspace recurrence
quantizes averaged return time as determinant winding divided by absorbing dimension.  The ratio
`7/4` matches the independently forced four-leg positive Hodge completion.

## No-go closure

- **Exact killing mechanism:** finite expected return for a finite absorbing subspace forces its
  matrix Schur/first-return function to be rational inner.  Its Taylor coefficient energies then
  decay exponentially.  The exact source law satisfies
  `w_(n-1)>=2/(3n^4)`, so it cannot be such a coefficient-energy sequence.  Full proof is
  `ULF-PHRD-001`, Theorem PHRD-C.
- **Strongest positive survivor:** the first moment alone forces absorbing dimension divisible by
  four; the minimal coarse system has dimension four, determinant degree seven, and first-return
  function `diag(z,z^2,z^2,z^2)`.
- **New insight:** four-leg completion is a finite closed observer of the history, not the history
  carrier.  Exact completion must retain noncompact memory or use a relative/open determinant;
  replacing the weighted-shift observability isometry by a finite unitary recurrence changes the
  object and discards the polynomial tail.
- **Status:** paper dependency is Bourgain--Grünbaum--Velázquez--Wilkening, Theorem 3.2,
  [arXiv:1302.7286](https://arxiv.org/abs/1302.7286).  Formalization is outside current no-Lean
  research phase.

## Falsified shortcuts

1. An isometric exit record does not imply rational-inner recurrence.
2. Finite mean does not imply finite memory.
3. Agreement of one rational moment with four-leg Hodge rank does not identify the two carriers.
4. Any RH argument retaining only the `7/4` moment admits the explicit coarse countermodel above.

