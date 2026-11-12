# Descent of the global width square class

- **ID:** galois-zero-width-squareclass-descent
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Questions:** Complete-fibre ground field; location of the central width involution.

Let `K` be the complete-fibre source field, `F=K(all δ_q)` the signed-width
field, and `E=K(all δ_qδ_r)`. Both extensions are normal over `K`.

## Theorem

There is a canonical class `ω∈E×/(E×)²`, represented by `δ_q²` for every
nonzero width and defined as `1` if all widths vanish. Unconditionally:

- `Gal(E/K)` fixes `ω`.
- `ω=1 ⇔ F=E`.
- Restriction `Gal(F/K)→Gal(E/K)` has a continuous group section exactly
  when `ω` lies in the image of `K×/(K×)²`.

For a nonzero anchor, the last condition is exactly
`δ_q²=a u²` with `a∈K×` and `u∈E×`. These statements concern the full
infinite fields and their Krull topologies.

## Proof

Every width ratio lies in `E`, since `δ_q/δ_r=(δ_qδ_r)/δ_r²` for a nonzero
denominator. Thus changing anchors changes the square representative by a
square. If `δ_q²` is a square in `E`, equality of squares puts `δ_q` in `E`;
the established presentation `F=E(δ_q)` proves the triviality criterion.
Normality extends every `E/K` automorphism to `F/K`. Its image of a nonbase
anchor has square in `E` and lies on the `Eδ_q` line, proving invariance.

For descent `δ_q²=a u²`, put `b=δ_q/u`. Then `b²=a∈K` and `F=E(b)`.
When `F≠E`, the closed subgroup fixing `b` restricts bijectively onto
`Gal(E/K)`: extension gives a lift, and the quadratic kernel corrects its
sign on `b`. Agreement on `E` and `b` gives uniqueness. Compactness and
the Hausdorff Krull topology make this continuous bijection a homeomorphism,
whose inverse gives the section. When `F=E`, restriction itself is an
isomorphism.

Conversely, a continuous section has compact, hence closed, image `H`.
Its complement is the quadratic restriction kernel, so `[Gal(F/K):H]=2`.
Infinite Galois correspondence gives `[F^H:K]=2`. Moreover `F^H∩E=K`,
since section lifts act on `E` as all of `Gal(E/K)`. Completing the square
in a quadratic minimal polynomial supplies `b∈F^H` with `b²∈K×` and
`b∉E`. The square-root-line classification in `F=E(δ_q)` forces
`b=vδ_q`, `v∈E×`; hence `δ_q²=b²(v⁻¹)²`. No finite-dimensional assumption
on `F/K` enters this argument.

## Formalization

`GaloisTheoryOfZeros/TheDescentOfTheGlobalWidthSquareClass.lean`:
`widthSquareClass_anchor_independent`, `widthSquareClass_invariant`,
`widthEvenRestriction_kernel_card`, `widthRestrictionSplits_iff_descends`,
`globalWidthSquareClass_trivial_iff`, `globalWidthSquareClass_invariant`,
and `globalWidthSquareClass_descent_iff`.

Direct source audit and the main transitive axiom closures passed; only
`propext`, `Classical.choice`, and `Quot.sound` occur. Umbrella import wired.

## Open arithmetic problem

Determine whether the actual complete-fibre source coefficients force
`ω` into the source image. Invariance alone does not imply descent;
centrality alone does not split a quadratic group extension. Neither
triviality nor descent of this actual class has been decided.
