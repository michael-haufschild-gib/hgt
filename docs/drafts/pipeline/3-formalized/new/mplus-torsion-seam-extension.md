# M+ torsion seam extension

- **ID:** mplus-torsion-seam-extension
- **Stage:** 3-formalized
- **Type:** CONSTRUCTION + THEOREM (Lean), definition-layer extension
- **Source:** `docs/drafts/rh-monodromy-weight-mismatch/128-relative-torsor-collapse.md`; `docs/drafts/pipeline/3-formalized/new/sigma-divisor-jet-multiplicative-kill.md`; `formal/GaloisForLFunctions/RHTower/FittingSeamBoundary.lean`; `formal/GaloisForLFunctions/RHTower/MPlusTorsionSeam.lean`; `formal/GaloisForLFunctions/RHTower/CutoffCochain.lean`; `formal/GaloisForLFunctions/RHTower/CutoffTorsionSeam.lean`
- **Statement:** Bare `M+` has no torsion seam presentation layer, so the pinned `{sigma_p}` divisor-refinement route is killed there. The minimal extension is a constraint layer: a p-labelled presentation `R[X]^n --A--> R[X]^n` with `det A = X^m`, sigma defects `Delta_p`, and morphisms preserving both the presentation square and defects modulo `A End + (X^m)`. A coefficient below `m` in `tr(adj(A) Delta_p)` is a non-circular witness proving `Delta_p ∉ A End + (X^m)`.

## Goal

Doc 128 killed the free relative torsor: a globally rooted finite Euler reference is deck-invisible. The previous Fitting card identified the only algebraic survivor: an obstructed torsion seam presentation. This card makes that survivor into a Lean interface and proves the exact route from a local coefficient witness to the nonmembership theorem.

The extension is a constraint, not a flow. The formal object is parametric over the regular completed `(sigma_p, partial_s)` base; it does not construct a carrier.

## Formal Surface

Lean declarations in `MPlusTorsionSeam.lean`:

- `TorsionSeamPresentation`
- `MPlusTorsionSeamObject`
- `TorsionSeamPresentation.boundaryTrace`
- `TorsionSeamPresentation.boundaryClass`
- `TorsionSeamPresentation.DefectFactorsThrough`
- `TorsionSeamPresentation.DefectFactorsThroughLeft`
- `TorsionSeamPresentation.DefectNonmember`
- `TorsionSeamPresentation.DefectLeftNonmember`
- `TorsionSeamPresentation.BoundaryCoeffWitness`
- `TorsionSeamPresentation.BoundaryTraceDivisible`
- `TorsionSeamPresentation.HasBoundaryCoeffWitness`
- `TorsionSeamPresentation.HasDeterminantTransverseDefect`
- `TorsionSeamPresentation.Hom`
- `TorsionSeamPresentation.Hom.id`
- `TorsionSeamPresentation.Hom.comp`
- `jetClass_eq_zero_iff_coeff_lt_eq_zero`
- `jetClass_ne_zero_iff_exists_coeff_lt_ne_zero`
- `fittingBoundaryClass_eq_zero_iff_coeff_lt_eq_zero`
- `fittingBoundaryClass_ne_zero_iff_exists_coeff_lt_ne_zero`
- `fittingBoundaryClass_eq_zero_of_trace_X_pow_dvd`
- `no_nontrivialFittingBoundary_of_trace_X_pow_dvd`
- `coeff_eq_zero_of_X_pow_dvd`
- `jetClass_ne_zero_of_coeff_lt`
- `fittingBoundaryClass_ne_zero_of_coeff_lt`
- `coeff_obstructs_right_factor_mod_X_pow`
- `coeff_obstructs_left_factor_mod_X_pow`
- `TorsionSeamPresentation.boundaryClass_ne_zero_iff_coeffWitness`
- `TorsionSeamPresentation.boundaryClass_eq_zero_of_traceDivisible`
- `TorsionSeamPresentation.not_boundaryCoeffWitness_of_traceDivisible`
- `TorsionSeamPresentation.boundaryClass_ne_zero_of_coeffWitness`
- `TorsionSeamPresentation.boundaryCoeffWitness_iff_not_traceDivisible`
- `TorsionSeamPresentation.boundaryCoeffWitness_of_not_traceDivisible`
- `TorsionSeamPresentation.hasBoundaryCoeffWitness_iff_hasDeterminantTransverseDefect`
- `TorsionSeamPresentation.noBoundaryCoeffWitness_of_forall_traceDivisible`
- `TorsionSeamPresentation.hasNontrivialFittingBoundary_iff_hasDeterminantTransverseDefect`
- `TorsionSeamPresentation.defectNonmember_of_coeffWitness`
- `TorsionSeamPresentation.defectLeftNonmember_of_coeffWitness`
- `TorsionSeamPresentation.defectNonmember_of_not_traceDivisible`
- `TorsionSeamPresentation.defectLeftNonmember_of_not_traceDivisible`
- `TorsionSeamPresentation.exists_defectNonmember_of_hasDeterminantTransverseDefect`
- `TorsionSeamPresentation.exists_defectLeftNonmember_of_hasDeterminantTransverseDefect`
- `TorsionSeamPresentation.exists_defectNonmember_of_hasNontrivialFittingBoundary`
- `fittingBoundaryTrace_eq_sum_det_updateRow`
- `fittingBoundaryTrace_left_factor`
- `fittingBoundaryClass_add`
- `fittingBoundaryClass_add_right_factor_mod_X_pow`
- `fittingBoundaryClass_add_left_factor_mod_X_pow`
- `fittingBoundaryClass_eq_of_eq_add_right_factor_mod_X_pow`
- `fittingBoundaryClass_eq_of_eq_add_left_factor_mod_X_pow`
- `fittingBoundaryClass_eq_zero_of_left_factor_mod_X_pow`
- `nonzero_fittingBoundaryClass_obstructs_left_factor_mod_X_pow`
- `exists_crossBoundary_not_right_factor_mod_X_pow`
- `exists_nonfake_crossBoundary_not_commute`
- `exists_crossing_crossBoundary_not_right_factor_mod_X_pow`
- `exists_crossBoundary_not_left_factor_mod_X_pow`
- `exists_crossBoundary_not_trace_X_pow_dvd`
- `exists_crossing_cutoffTorsionSeam`
- `exists_crossing_cutoffMPlusTorsionSeamObject`

## Object And Morphism Definition

For fixed local multiplicity `m`, an added seam object is:

`A : Matrix n n R[X]`, `Delta : Sigma -> Matrix n n R[X]`, `det A = X^m`.

The extended object is:

`base : Base`, `seam : TorsionSeamPresentation Sigma n R m`.

Here `Base` is deliberately abstract: it is the regular finite-free `(sigma_p, partial_s)` object from the current paper category. The new data is only the torsion seam constraint.

A seam morphism `S -> T` consists of matrices `left`, `right` with:

`right * S.A = T.A * left`,

and for every `p`, defect compatibility modulo fake target defects:

`right * S.Delta p - T.Delta p * left = T.A * H + X^m K`.

Lean proves identity morphisms and composition, so this is category-shaped at the seam layer.

## Theorem

The theorem route is:

1. coefficient witness:

   `(tr(adj(A) Delta_p)).coeff j != 0` for some `j < m`;

2. nonzero Fitting boundary:

   `fittingBoundaryClass m A Delta_p != 0`;

3. nonmembership:

   `¬ ∃ H K, Delta_p = A * H + X^m K`.

This is the formal `Delta_p ∉ A End + (X^m)` statement. The theorem is not assumed as a field; it is derived from the coefficient witness.

The boundary trace also has a determinant form:

`tr(adj(A) Delta_p) = sum_i det(A with row i replaced by row_i(Delta_p))`.

This is formalized as `fittingBoundaryTrace_eq_sum_det_updateRow`. It turns the next arithmetic target into a concrete row-replacement determinant test. The same update also closes fake source-basis changes: defects `Delta = H A + X^m K` vanish just like right-factor defects `Delta = A H + X^m K`.

The coefficient witness is exact, not merely sufficient:

`fittingBoundaryClass m A Delta != 0`

iff

`exists j < m, coeff_j tr(adj(A) Delta) != 0`.

So determinant-compatible defects are killed: if `X^m | tr(adj(A) Delta_p)`, then the Fitting boundary class is zero and no coefficient witness exists. The remaining arithmetic obligation is therefore determinant transversality modulo `X^m`.

At the sigma-family level, Lean proves the exact gate:

`HasNontrivialFittingBoundary m A Delta`

iff

`exists p, not (X^m | tr(adj(A) Delta_p))`.

Thus extending `M+` by a torsion seam presentation is enough to state and prove `Delta_p ∉ A End + (X^m)` once a determinant-transverse sigma defect is supplied. It is not enough to produce that defect automatically; any construction whose trace remains divisible by `X^m` is formally dead.

The direct downstream theorem is also formalized:

`not (X^m | tr(adj(A) Delta_p)) -> Delta_p ∉ A End + (X^m)`,

and at family level:

`HasNontrivialFittingBoundary m A Delta -> exists p, Delta_p ∉ A End + (X^m)`.

The boundary class also descends through the fake-defect quotient: adding
`A H + X^m K` or `H A + X^m K` to a defect does not change the class. Thus the boundary witness is
well-defined on the presentation congruence, not merely a raw-matrix test.

`CutoffCochain.lean` supplies the current concrete algebraic survivor: for every `m > 0` there is
an idempotent cutoff `e`, a crossing action `sigma`, and a presentation `A` with `det A = X^m` such
that `sigma * e != e * sigma` and `Delta = (1-e) sigma e` is determinant-transverse and satisfies both
`Delta ∉ A End + (X^m)` and `Delta ∉ End A + (X^m)`.

`CutoffTorsionSeam.lean` packages that witness into the category layer itself: a one-label
`TorsionSeamPresentation Unit (Fin 2) ℚ m` has `Delta () = (1-e) sigma e`,
`HasDeterminantTransverseDefect`, `DefectNonmember ()`, and `DefectLeftNonmember ()`. Over any
inhabited regular base, this yields an `MPlusTorsionSeamObject` with the same live seam defect.

## Gates

- [x] 0 -> 1 in-progress: extension target isolated from the relative torsor collapse and the bare-`M+` no-go.
- [x] 1 -> 2 fully-proven: object, morphism, identity, composition, exact coefficient witness, determinant-compatible no-go, nonzero boundary, two-sided fake-defect vanishing, row-replacement determinant form, and nonmembership proof written as exact algebra.
- [x] 2 -> 3 formalized: `formal/GaloisForLFunctions/RHTower/MPlusTorsionSeam.lean`; imported by `RHTower.lean`; targeted checks passed.
- [ ] 3 -> 4 publication-ready: integrate this definition-layer amendment into the MWM charter and door index through the library ticket.

## Status

This does not prove such a determinant-transverse defect exists for the arithmetic Sonin seam. It proves the exact category extension, proves the boundary class is invariant under fake-defect congruence, proves an abstract cutoff-crossing cochain has the required nonmembership shape, and packages that cochain as an extended `M+` object. The free `{sigma_p}` reference remains killed; bare `M+` remains killed; pinned commutators remain killed; the only reopened route is a non-local cutoff-crossing torsion seam realized by the actual semilocal action.
