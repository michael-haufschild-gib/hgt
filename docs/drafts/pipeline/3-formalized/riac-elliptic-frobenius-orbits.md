# Closed-place fibres are actual Frobenius orbits

- **ID:** RIAC-elliptic-frobenius-orbits
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Curve orientation counts](../1-in-progress/riac-curve-orientation-square-root.md)
- **Statement:** Frobenius is transitive on finite residue-field embeddings; its orbits on actual elliptic points are precisely the closed-place fibres.

For finite fields `F,K,E` and embeddings `f,g:K→_F E`, there is `n≥0`
with `Frob_E^n∘f=g`. Normality restricts the second embedding to an
automorphism of `K` relative to the first. The cyclic finite-field Galois
group expresses that automorphism as a Frobenius power. Embeddings commute
with Frobenius.

On the actual curve `Y²Z=X³−XZ²` over `F₃`, an affine point is a map
from the coordinate algebra to `E`. Its prime kernel is unchanged by
Frobenius. Two maps with the same kernel descend to embeddings of the
same residue field, so the transitivity theorem joins them. The existing
projective-point equivalence adds infinity as a fixed singleton.

For every finite `E/F₃`, two actual projective points have the same
closed-place label exactly when a Frobenius power joins them. These
powers have identity at zero and satisfy the additive composition law.
Only places supported over `E` occur; the existing residue-degree
criterion identifies them by `deg(v) | [E:F₃]`, together with infinity.

[EllipticFrobeniusOrbits.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/EllipticFrobeniusOrbits.lean):
`finiteField_embeddings_frobenius_transitive`, `ellipticAffineFrobenius_pow`,
`ellipticAffineFrobenius_place`, `ellipticAffine_same_place_iff_frobenius`,
`ellipticPoint_same_place_iff_frobenius`, `ellipticPointFrobeniusPower_zero`,
`ellipticPointFrobeniusPower_add`.
Direct Lean check passed; all seven audits use only `propext`,
`Classical.choice`, `Quot.sound`.

This establishes the geometric fibre comparison needed to relate actual
orientation quotients to the [proved signed divisor counts](riac-elliptic-squarefree-divisor-cancellation.md).
The [stable-subset bijection and permutation-sign comparison](riac-elliptic-stable-orientation.md)
are now formalized, with a square-root bound on the actual geometric
orientation sum. The original orientation-quotient comparison and the
integer conductor-height transfer remain open.
