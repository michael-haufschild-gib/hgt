# Independent root-orientation cover count

- **ID:** RIAC-root-orientation-cover
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); classical finite-field calibration
- **Source:** [discriminant-cover construction](../1-in-progress/riac-discriminant-cover-signed-counts.md)
- **Statement:** Over an odd finite field with `q` elements, the actual root-orientation cover of monic degree-`n` polynomials has `q^n` points for `n≥2`, independently of any polynomial Möbius sum.

## Actual finite set

Take the constructed extension `E/F` of degree `n!`. For monic `f` of
degree `n`, let `x_f` order its roots in `E`, with multiplicities, and set
`V(x)=∏_(i<j)(x_j−x_i)`. The counted finite set is

`C_n(F)={(f,y): f monic of degree n, y∈F, (ιy)²=V(x_f)²}`,

where `ι:F→E` is the algebra map. Reordering roots changes `V` by a
permutation sign, so the equation is independent of the ordering.
It uses neither a Möbius coefficient nor an assumed cancellation law.

## Proof

Vieta identifies monic polynomials with the actual Frobenius-stable root
orbits. A collision makes `V=0`, and the fibre contains exactly `y=0`;
its orientation weight is zero.

For distinct roots, Frobenius multiplies `V` by its permutation sign.
With sign `+1`, the coordinate is Frobenius-fixed and descends to `F`;
its two square roots give two points. With sign `−1`, a base-field square
root would equal `V` or `−V` in `E`, contradicting Frobenius reversal in
odd characteristic. That fibre is empty.

Consequently every fibre has cardinality `1+w`, where `w` is the actual
signed transporter weight. Non-fixed orbits have weight zero. Independent
normal-basis counts cancel the total orientation weight for at least two
labels. Summing fibres and using Vieta gives `#C_n(F)=q^n`.

## Exact scope

The construction and count concern the displayed root equation. The
identification with Mathlib's `Polynomial.discr`, and a formal presentation
by one polynomial in coefficient coordinates, remain separate obligations.
The existing integral symmetric discriminant construction supplies a
candidate for the latter comparison.

No conductor-height estimate or identification with integer relative-homology
indices is supplied. In particular, this theorem does not bound
`Σ_p index_p(N)=1−M(N)` at the square-root scale.

## Formalization

[FiniteFieldRootCover.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/FiniteFieldRootCover.lean):

- `exists_base_of_frobenius_fixed`.
- `baseOrientationFibre_zero`, `baseOrientationFibre_card_of_fixed`, `baseOrientationFibre_empty_of_neg`.
- `vandermonde_square_eq_of_orbit`, `vandermonde_frobenius`, `baseOrientationFibre_card_eq_weight`.
- `sum_stableOrientationWeight_eq_zero`, `rootOrientationCover_card`.
- `arithmeticRootOrientationCover`, `arithmeticRootOrientationCover_card`.

Direct leaf check and eleven transitive axiom audits; only `propext`,
`Classical.choice`, `Quot.sound`.

## Literature boundary

The root-discriminant cover and Frobenius-sign mechanism are classical;
see [Gadish, §§1.1 and 3.2](https://arxiv.org/html/1703.01710v2) and
[Afshar, §§1–2](https://arxiv.org/html/2001.05641v1). The contribution is a
formal construction and independent count of the actual finite set,
including collisions. No new classical point-count theorem is claimed.
