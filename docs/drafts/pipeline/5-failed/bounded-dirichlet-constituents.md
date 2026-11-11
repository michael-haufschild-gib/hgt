# Bounded Dirichlet constituents cannot carry a zero

- **Stage:** 5-failed
- **Type:** NO-GO
- **Parent:** [Closure tasks](../3-formalized/fable-route-closures.md).

## Obstruction

A nonzero bounded holomorphic Dirichlet series on `Re s>x`, absolutely
convergent sufficiently far right, cannot have a zero there if all its zeros
are zeros of `ξ`. The boundary `x` is arbitrary.

Lean: `ConstituentTheoryOfTheZeros.bounded_dirichlet_constituent_ne_zero`,
in `ABoundedConstituentHasNoZeros.lean`.

## Positive survivor

Every bounded pure Dirichlet series has a bounded finite-prime representative
of its zero set, with the same bound and any prescribed initial prime coordinates
retained. Two zero-free anchors and simultaneous prime contraction supply the
representative; finite winding alone is not the argument.

Paper proof and Lean formalization are complete:
[finite-prime zero sets](../3-formalized/bounded-pure-dirichlet-series-have-finite-prime-zero-sets.md).
The stronger finite exponential polynomial divisor conjecture remains open.
