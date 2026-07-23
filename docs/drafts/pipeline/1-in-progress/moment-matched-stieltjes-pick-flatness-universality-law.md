# Moment-matched Stieltjes–Pick flatness universality law

Status: exact `lake env lean` audit passed; final module/lint/axiom audit pending.

## Lean sources

- `cauchy_transform_sub_of_moments_eq`
- `stieltjesTransform_im_pos`
- `stieltjesTransform_differentiableOn`
- `stieltjesTransform_conj`

## Survivor

Two nonzero finite positive measures with the same moments through order `N` generate holomorphic
strict Pick functions on the upper half-plane whose difference has an exact order-`N+1`
Stieltjes-kernel remainder and is real-symmetric under conjugation.

Moment flatness was stated for the opposite Cauchy-kernel orientation, while the Pick theory was
stated for the Stieltjes orientation.  The kernel sign conversion exposes one common transform and
makes finite moment agreement an exact analytic defect law inside the Pick class.

## Proof skeleton

Convert `(z - x)⁻¹` to `-((x - z)⁻¹)` in the Cauchy flatness theorem, including its weighted
remainder.  Apply upper-half-plane positivity and holomorphy separately to both measures, then use
Schwarz reflection on each transform to make their defect real-symmetric.

## Novelty audit

Pending post-formalization literature search.
