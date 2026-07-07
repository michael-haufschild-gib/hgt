# Cutoff cross-boundary seam nonmember

- **ID:** cutoff-cross-boundary-seam-nonmember
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), surviving candidate source
- **Source:** `docs/drafts/rh-monodromy-weight-mismatch/129-pinned-carrier-geometry-candidates.md`; `docs/drafts/rh-monodromy-weight-mismatch/130-sonin-seam-defect-commutator-nogo.md`; `formal/GaloisForLFunctions/RHTower/CutoffCochain.lean`; `formal/GaloisForLFunctions/RHTower/FittingSeamBoundary.lean`; `formal/GaloisForLFunctions/RHTower/CutoffTorsionSeam.lean`
- **Statement:** Pinned-germ scalar and commutator `{sigma_p}` defects are fake, but a cutoff-crossing cochain can be determinant-transverse to a torsion seam presentation. For every `m > 0`, Lean constructs an idempotent cutoff `e`, an action `sigma`, and a presentation `A` with `det A = X^m` such that `Delta = (1-e) sigma e` has nonzero Fitting boundary, is not a commutator, and satisfies `Delta ∉ A End + (X^m)` and `Delta ∉ End A + (X^m)`. The witness is packaged as a one-label `TorsionSeamPresentation`, and over any inhabited regular base it gives an `MPlusTorsionSeamObject`.

## Formal Surface

Lean declarations in `CutoffCochain.lean`:

- `crossBoundary`
- `upperBoundary`
- `compression`
- `crossBoundary_add`
- `crossBoundary_one`
- `compression_semicommutator`
- `compression_mul`
- `crossBoundary_eq_zero_of_commute`
- `upperBoundary_eq_zero_of_commute`
- `crossBoundary_smul_one`
- `exists_nonfake_crossBoundary`
- `exists_nonfake_crossBoundary_not_commute`
- `exists_nonfake_crossBoundary_not_commutator`
- `exists_crossBoundary_not_right_factor_mod_X_pow`
- `exists_crossing_crossBoundary_not_right_factor_mod_X_pow`
- `exists_crossBoundary_not_left_factor_mod_X_pow`
- `exists_crossBoundary_not_trace_X_pow_dvd`
- `crossBoundary_two_cutoff_asymmetry`

Supporting quotient-invariance declarations in `FittingSeamBoundary.lean`:

- `fittingBoundaryClass_add`
- `fittingBoundaryClass_add_right_factor_mod_X_pow`
- `fittingBoundaryClass_add_left_factor_mod_X_pow`
- `fittingBoundaryClass_eq_of_eq_add_right_factor_mod_X_pow`
- `fittingBoundaryClass_eq_of_eq_add_left_factor_mod_X_pow`

Packaging declarations in `CutoffTorsionSeam.lean`:

- `exists_crossing_cutoffTorsionSeam`
- `exists_crossing_cutoffMPlusTorsionSeamObject`

## Theorem Route

The cutoff defect is:

`Delta := (1 - e) * sigma * e`.

Pinned-germ actions collapse because commuting with the cutoff gives:

`crossBoundary e sigma = 0`.

The surviving algebraic witness is different: choose a boundary-crossing `sigma`. Lean now exports
the crossing condition itself:

`sigma * e != e * sigma`.

It then constructs a two-by-two polynomial model with `det A = X^m` and proves:

`fittingBoundaryClass m A Delta != 0`,

hence:

`not (X^m | tr(adj(A) Delta))`,

and therefore:

`Delta ∉ A End + (X^m)`.

The same witness is also outside the left fake class:

`Delta ∉ End A + (X^m)`.

Finally, the witness is packaged into the seam interface itself:

`S.Delta () = Delta`,

`S.HasDeterminantTransverseDefect`,

`S.DefectNonmember ()`,

`S.DefectLeftNonmember ()`.

For any inhabited regular base `Base`, this gives an extended object

`O : MPlusTorsionSeamObject Base Unit (Fin 2) ℚ m`

with the same live seam defect.

## Status

This is an abstract cutoff-crossing theorem, not yet the arithmetic Sonin operator. It changes the
backtracking point: the route is not killed by the category, not killed by fake presentation
congruence, not killed by the commutator collapse, and not blocked at the object layer of the
extended `M+` category. It is killed only if the actual semilocal Sonin `{sigma_p}` defect is shown
to be determinant-compatible modulo `X^m`, or if it cannot be realized as a cutoff-crossing torsion
seam defect.

## Gates

- [x] 0 -> 1 in-progress: Sonin/cutoff survivor isolated after free torsor, unit, and commutator collapses.
- [x] 1 -> 2 fully-proven: algebraic cutoff-crossing witness written with determinant-transverse Fitting boundary and two-sided fake-class nonmembership.
- [x] 2 -> 3 formalized: `formal/GaloisForLFunctions/RHTower/CutoffCochain.lean`; `formal/GaloisForLFunctions/RHTower/CutoffTorsionSeam.lean`; imported by `RHTower.lean`; targeted checks passed.
- [ ] 3 -> 4 publication-ready: integrate into the MWM charter/door through a library ticket.
