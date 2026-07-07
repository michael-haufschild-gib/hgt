# Library ticket: cutoff cross-boundary seam nonmember

- **Target docs:** `docs/drafts/door/00-index.md`; `docs/drafts/door/bucket-the-seam-archimedean-obstruction.md`; `docs/drafts/rh-monodromy-weight-mismatch/00-approach.md`; `docs/drafts/rh-monodromy-weight-mismatch/129-pinned-carrier-geometry-candidates.md`; `docs/drafts/rh-monodromy-weight-mismatch/130-sonin-seam-defect-commutator-nogo.md`.
- **Source card:** `docs/drafts/pipeline/3-formalized/new/cutoff-cross-boundary-seam-nonmember.md`
- **Formal files:** `formal/GaloisForLFunctions/RHTower/CutoffCochain.lean`; `formal/GaloisForLFunctions/RHTower/FittingSeamBoundary.lean`; `formal/GaloisForLFunctions/RHTower/CutoffTorsionSeam.lean`

## Update Needed

Record the sharpened state after the commutator collapse:

1. Pinned-germ scalar actions commute with every cutoff, so their cross-boundary cochain is zero.
2. The naive presentation commutator `sigma A - A sigma` has zero Fitting boundary for every `A` and `sigma`; it cannot be the live `{sigma_p}` seam defect.
3. The cutoff-crossing cochain `Delta = (1-e) sigma e` is the surviving shape.
4. `CutoffCochain.lean` proves abstract existence: for every `m > 0`, there is an idempotent cutoff `e`, an action `sigma`, and a torsion seam presentation `A` with `det A = X^m` such that `sigma * e != e * sigma` and this `Delta` has nonzero Fitting boundary.
5. The same witness is determinant-transverse: `not (X^m | tr(adj(A) Delta))`.
6. The same witness is not a commutator with `A`.
7. The same witness is outside both fake presentation classes: `Delta ∉ A End + (X^m)` and `Delta ∉ End A + (X^m)`.
8. `FittingSeamBoundary.lean` proves quotient invariance: adding `A H + X^m K` or `H A + X^m K` does not change the Fitting boundary class.
9. `CutoffTorsionSeam.lean` packages the witness as a one-label `TorsionSeamPresentation` and, over any inhabited regular base, as an `MPlusTorsionSeamObject`.
10. The remaining obligation is realization, not abstract algebra: identify the actual semilocal Sonin `{sigma_p}` boundary action with a determinant-transverse cutoff-crossing cochain.

## Suggested Grade

THEOREM (Lean), survivor narrowed. Door status: route remains open only through a non-local cutoff-crossing torsion seam; all pinned-germ and commutator presentations are killed.
