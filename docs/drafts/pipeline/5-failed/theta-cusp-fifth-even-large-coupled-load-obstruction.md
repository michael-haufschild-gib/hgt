# Large first coupled theta loads fail at scale seven

- **Stage:** 5-failed; native and weighted matrix obstructions formalized.
- **Wall:** Σ6; smaller coupled loads and the integrated rank-nine sign remain open.
- **Claim:** Every `C≥10⁸`, `D≥0` fails positive semidefiniteness at `x₇=½log(7/π)`, including the literal weighted representative at each `0<a<1/2`.
- **Positive survivor:** Exact native and weighted sixth-degree capacity half-planes; `(10⁷,10¹²)` passes this direction. Paper proof and Lean formalization complete.

The coupled loads are `u₁=(0,0,1,420,0)`, `u₂=(0,0,0,1,1568)`.
They annihilate the eighth-degree scale-seven witness, but in the independent
direction `w=(-6272,336,-2,1/420,0)` their cost is `C+D/176400`.
The [complete-source capacity theorem](../3-formalized/theta-cusp-fifth-even-sixth-direction-capacity.md)
gives native threshold `B₆∈(16·10⁶,50·10⁶)` and weighted threshold
`B₆,a∈(B₆,70·10⁶)`. Both energies are strictly negative when
`C≥10⁸`, `D≥0`. Thus the explicit positive-origin pair `(10⁸,10¹²)`
cannot supply global pointwise positivity, despite its positive origin and tail.

The same theorem identifies the positive regions exactly:
`C+D/176400<B₆` and `C+D/176400<B₆,a`. The reduced pair
`(10⁷,10¹²)` lies strictly inside both. It also preserves the positive
eighth-degree witness. Its [origin-and-tail repair](../3-formalized/theta-cusp-fifth-even-reduced-coupled-repair.md)
is formalized. A further
[Schur direction](../5-failed/theta-cusp-fifth-even-reduced-coupled-schur-obstruction.md)
refutes this pair's full source sign at scale seven. These directional and
origin-and-tail results remain valid.

Lean: `EvenFiveCoherent.coupledRepair_not_posSemidef_of_large_first` and
`coupledWeightedRepair_not_posSemidef_of_large_first`, with the exact
capacity and reduced-pair positivity theorems in `ThetaCuspSections`.
Canonical checks pass; all dependencies use only standard Lean axioms.
