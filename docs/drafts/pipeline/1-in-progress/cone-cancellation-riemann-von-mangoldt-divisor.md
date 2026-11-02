# Exact spline cone cancellation with the Riemann–von Mangoldt count

- **Stage:** 1-in-progress
- **Type:** Paper construction; Lean formalization incomplete
- **Parent:** SC2; distinguish arithmetic source data from zero geometry.

Conjecture: the exact sparse off-line quartet model can be completed by
simple critical-line pairs so that its positive-ordinate count satisfies

```text
N(T)=T/(2π) log(T/(2π))−T/(2π)+O(log T),
```

while exact coefficients `(sinh z/z)^8`, symmetry, unattained positive
width, and bounded natural two-prime cone coupling persist. The resulting
divisor is not asserted to be the zeta divisor or to admit its Euler product.

## Written construction to formalize

Write `F(T)` for the displayed main term. In each unit interval `[j,j+1)`, `j≥1`,
place `max(6, floor F(j+1)−floor F(j))` distinct critical ordinates.
The maximum changes only finitely many blocks because `F'` tends to infinity.
The reference count telescopes at integer heights, and partial blocks cost
`O(log T)`.

The existing sparse model has at most three core ordinates per unit
interval, hence at most six positive-ordinate quartet points. Delete that
many critical slots in each block and insert these off-line points.
Block counts remain unchanged, so the same counting law survives.
The remaining critical slots can use distinct rational heights
`j+(k+1)/(n_j+1)`, avoiding all nonzero integer multiples of `π`.
Their exact spline coefficients are consequently nonzero.
Critical coefficients equal `(sin γ/γ)^8`; their norms are summable under
this count. Their coupling is therefore bounded, and adding them preserves
the bounded coupling of the off-line model.

The paired Hadamard product may further realize this divisor by a real
even entire function of order one. This stronger conclusion needs its own
product and growth proof; it is not part of the established construction.

## Audit

The zero-exponent off-line model is formalized.
`exists_unit_block_rvm_count` in `ConeMoments/RVMCompletionCounts.lean`
proves the counting law for arbitrary finite blocks of the prescribed sizes;
its direct Lean and transitive axiom audits use only standard axioms.
`CriticalSplineSlots.lean` also proves nonzero exact rational-slot weights,
absolute summability, and bounded critical-pair coupling, with standard
axiom audits. Divisor geometry and full-series assembly remain unformalized.
The separate count audit found the actual Riemann–von Mangoldt count
and the theta-tail divisor-capacity theorem. The latter controls radial
density, without resolving bounded horizontal displacements. No block
completion preserving exact spline cone cancellation was found.
The optional entire-function realization still needs its own audit.
External priority is unchecked.
