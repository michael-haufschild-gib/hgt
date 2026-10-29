# Absolute unfolding of families over the unit-log lattice

- **ID:** number-field-log-periodizations-have-absolute-unfolding
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Dual theta unfolding](../1-in-progress/hecke-dual-theta-unfolding-over-fractional-ideal-classes.md)
- **Statement:** A continuous countable family on a number field's unit-log space, uniformly dominated on the unit fundamental domain by one summable family/lattice majorant, is integrable over the entire log space. Its absolute masses are summable, and integration of the paired periodization equals the sum of whole-space integrals.

## Proof

Compact closure of the actual unit domain gives integrability of every
translated summand. Its finite measure and the summable majorant bound
the sum of domain integral norms. Nonnegativity splits this paired sum
into summable lattice rows and a summable outer family.

Positive-translation nonnegative tile unfolding identifies each
whole-space norm integral with its lattice row. The resulting finite
integral proves whole-space integrability before complex unfolding is
used. The same identity proves summability of all whole-space masses.

Absolute integral/sum exchange on the unit domain, paired-sum Fubini,
and complex tile unfolding then give the exact identity

```
integral_D sum_(i,l) F_i(x+l) = sum_i integral_whole F_i(x).
```

The hypotheses are a general domination criterion. Its Hecke application
constructs the majorant from the actual trace-dual Gaussian series.

## Lean

Module: `GaloisForLFunctions.HTGeometry.NumberFieldLogPeriodizationsHaveAbsoluteUnfolding`.
Declaration: `GaloisForLFunctions.HTGeometry.numberFieldUnitDomain_unfold_family`.

The transitive axiom audit reports only `propext`, `Classical.choice`,
and `Quot.sound`. Final direct source audit passes without warnings:

```
lake --old env lean GaloisForLFunctions/HTGeometry/NumberFieldLogPeriodizationsHaveAbsoluteUnfolding.lean
```

Wired into `HTGeometry.lean`; the umbrella was not compiled.
