# Rational Hecke orbits at ratio six

- **ID:** rational-hecke-orbits-at-ratio-six
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** review-0411 §2.1, A6.

## Statement

On rational `1≤q<6`, let `F(q)=2q` for `q<3`, and `F(q)=q/3` otherwise.
Every orbit stays in `[1,6)` and has infinite range. Consequently, no finite
template containing one is closed under all ratio-two and ratio-three
neighbours in `[1,6)`. Stages beyond this aperture cannot be treated by a
single finite closed graph.

## Positive survivor and proof

Every nonempty finite subset of `[1,6)` has a vertex whose `F`-neighbour lies
outside it. Maximize the two-adic valuation, then minimize the rational
vertex among maximizers. Below three, doubling increases the valuation.
At or above three, division by three preserves it and lowers the vertex.
Both alternatives contradict closure. A finite orbit range would be a
nonempty finite invariant set.

This supplies infinitely many vertices connected by allowed Hecke edges,
all in a fixed bounded interval. The finite-graph/window equivalence still
applies to every finite subset; a uniform bound on component size does not.

## Lean theorems

`WindowTowerOfSpecZ.exists_heckeSixStep_not_mem`, `heckeSixOrbit_infinite` and
`no_finite_hecke_template_at_six` in
`AnInfiniteRationalHeckeOrbitInABoundedWindow.lean` prove the escape law,
infinite range for every starting point in `[1,6)`, and the template obstruction.
The final direct source check and all three transitive axiom audits passed
(`propext`, `Classical.choice`, `Quot.sound`). The owning umbrella imports the module.
