# Constraint Laplacian, uncertainty and capacity horizon — Lean certificate

- **ID:** `constraint-laplacian-uncertainty-and-capacity-horizon-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `constraint-laplacian-uncertainty-and-capacity-horizon.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Modules

| File | Contents |
|---|---|
| `HTGeometry/HilbertClosedRange.lean` | the closed-range theorem for a bounded operator on a Hilbert space, built from scratch |
| `HTGeometry/ConstraintLaplacian.lean` | §2 constraint defect, codefect, Laplacian and energy; §3 Thm 3.1 |
| `HTGeometry/FriedrichsAngle.lean` | §4 Thm 4.1, the sharp pairwise precision law |
| `HTGeometry/FriedrichsClosedSum.lean` | §4 Thm 4.1, closedness of the sum at Friedrichs cosine `< 1` |
| `HTGeometry/ExchangeCurvature.lean` | §5 Prop 5.1 and Prop 5.2 |
| `HTGeometry/NestedConvexCapacity.lean` | §7 Thm 7.1 and Example 7.2 |

Namespace `GaloisForLFunctions.HTGeometry`; the closed-range file extends
`ContinuousLinearMap`.

## Card statement to Lean name

| Card | Lean |
|---|---|
| infrastructure: coercive implies surjective | `ContinuousLinearMap.norm_le_of_reCoercive`, `ContinuousLinearMap.surjective_of_reCoercive` |
| infrastructure: transverse lower bound is closed range | `ContinuousLinearMap.HasTransverseLowerBound`, `ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range` |
| infrastructure: `range T* = (ker T)ᗮ` for closed range | `ContinuousLinearMap.range_adjoint_eq_ker_orthogonal_of_isClosed_range`, `ContinuousLinearMap.isClosed_range_adjoint_iff` |
| §2 joint sector, defect, codefect, Laplacian `Δ = Σ (1 − Pᵢ)` | `jointSector`, `constraintDefect`, `constraintCodefect`, `constraintLaplacian` |
| §2 energy as a sum of squared distances | `constraintEnergy`, `constraintEnergy_eq_sum_infDist_sq`, `constraintEnergy_eq_zero_iff` |
| §2 kernel of the Laplacian is the joint sector | `ker_constraintLaplacian`, `inner_constraintLaplacian_self` |
| §3 Thm 3.1 exact / uniform-uncertainty / mirage trichotomy | `HasUniformPrecisionGap`, `hasUniformPrecisionGap_iff_hasTransverseLowerBound`, `constraintLaplacian_tfae` |
| §3 mirage regime produces transverse almost-solutions | `exists_transverse_unit_sequence_of_not_hasUniformPrecisionGap` |
| §4 Friedrichs cosine and pairwise precision | `friedrichsCosine`, `pairPrecision`, `norm_inner_le_friedrichsCosine` |
| §4 Thm 4.1 (4.2)–(4.4) sharp pairwise precision law | `pair_precision_lower_bound`, `one_sharp_tradeoff`, `exists_transverse_unit_pairPrecision_le` |
| §4 Thm 4.1 (4.5) closed sum iff cosine `< 1` | `isClosed_genericSum_of_friedrichsCosine_lt_one`, `friedrichsCosine_lt_one_of_isClosed_genericSum`, `friedrichsCosine_lt_one_iff_isClosed_sup` |
| §5 Prop 5.1 exchange curvature and incidence are independent | `exchangeCurvature`, `exchangeCurvature_incidence_independent` |
| §5 Prop 5.2 equal curvature norm, unequal uncertainty | `norm_exchangeCurvature_planeLines`, `friedrichsCosine_planeLines` |
| §7 Thm 7.1 nested convex capacity criterion | `nonempty_iInter_iff_bddAbove_infDist` |
| §7 Example 7.2 harmonic profile with empty intersection | `harmonicConstraint`, `harmonicConstraint_iInter_eq_empty`, `tendsto_infDist_harmonicConstraint_atTop` |

## Verification

Foreground per-file elaboration and a cached foreground `lake build` of the six modules pass.
The axiom audit of `constraintLaplacian_tfae`, `one_sharp_tradeoff`,
`friedrichsCosine_lt_one_iff_isClosed_sup` and `harmonicConstraint_iInter_eq_empty` reports only
`propext`, `Classical.choice`, `Quot.sound`.

The capacity criterion is proved by the parallelogram law and the nearest-point projection, not by
weak compactness, so it needs no reflexivity argument.

## Boundary

The trichotomy and the pairwise law are statements about finitely many closed subspaces of one
Hilbert space.  They classify the obstruction; they do not produce a constraint family attached to
any arithmetic object.
