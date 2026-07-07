# Library ticket: M+ torsion seam extension

- **Target docs:** `docs/drafts/door/00-index.md`; `docs/drafts/door/bucket-the-seam-archimedean-obstruction.md`; `docs/drafts/rh-monodromy-weight-mismatch/00-approach.md`; possibly `docs/drafts/rh-monodromy-weight-mismatch/128-relative-torsor-collapse.md`.
- **Source card:** `docs/drafts/pipeline/3-formalized/new/mplus-torsion-seam-extension.md`
- **Formal files:** `formal/GaloisForLFunctions/RHTower/MPlusTorsionSeam.lean`; `formal/GaloisForLFunctions/RHTower/CutoffTorsionSeam.lean`

## Update Needed

Record the definition-layer amendment after the free relative torsor collapse:

1. The free finite `{sigma_p}` tower is deck-invisible as a reference torsor; dressing ξ by it returns ξ's own deck class.
2. Bare `M+` has regular finite-free `(sigma_p, partial_s)` lanes only, so it has no object/morphism slot for a supported torsion seam.
3. The minimal extension is a p-labelled torsion seam presentation `R[X]^n --A--> R[X]^n` with `det A = X^m` and defects `Delta_p`.
4. Morphisms preserve the presentation square and preserve sigma defects modulo fake target defects `A End + (X^m)`.
5. `MPlusTorsionSeam.lean` proves identities and composition for the seam morphisms.
6. The nonmembership theorem is now formal: a coefficient witness below `m` in `tr(adj(A) Delta_p)` proves `Delta_p ∉ A End + (X^m)`.
7. `FittingSeamBoundary.lean` now also proves the left-factor fake kill: defects `Delta_p = H_p A + X^m K_p` vanish, so source/target basis-change defects are both fake.
8. `fittingBoundaryTrace_eq_sum_det_updateRow` rewrites the boundary trace as a sum of row-replacement determinants.
9. The coefficient witness is exact: the Fitting boundary is nonzero iff some coefficient below `m` survives.
10. Determinant-compatible defects are dead: if `X^m | tr(adj(A) Delta_p)`, then the boundary class is zero and no coefficient witness exists.
11. At the sigma-family level, `HasNontrivialFittingBoundary m A Delta` is equivalent to existence of one determinant-transverse label `p`, i.e. `not (X^m | tr(adj(A) Delta_p))`.
12. The direct downstream theorem is formal: `not (X^m | tr(adj(A) Delta_p))` proves `Delta_p ∉ A End + (X^m)`, and `HasNontrivialFittingBoundary m A Delta` proves existence of such a nonmember label.
13. The boundary class descends through the fake-defect congruence: adding `A H + X^m K` or `H A + X^m K` preserves the Fitting boundary class.
14. `CutoffCochain.lean` proves the abstract cutoff-crossing survivor: for every `m > 0`, there is a cutoff `e`, a crossing action `sigma`, and a presentation `A` with `det A = X^m` such that `Delta = (1-e) sigma e` is determinant-transverse and satisfies both `Delta ∉ A End + (X^m)` and `Delta ∉ End A + (X^m)`.
15. `CutoffTorsionSeam.lean` packages that survivor as a one-label `TorsionSeamPresentation` with `HasDeterminantTransverseDefect`, `DefectNonmember ()`, and `DefectLeftNonmember ()`.
16. Over any inhabited regular base, the same seam gives an `MPlusTorsionSeamObject`; the route is therefore not blocked at the extended-object layer.
17. The remaining arithmetic obligation is no longer abstract existence; it is realization: identify the actual Sonin/semilocal `{sigma_p}` action with such a determinant-transverse cutoff-crossing cochain.

## Suggested Grade

CONSTRUCTION + THEOREM (Lean), definition-layer extension. Door status: reopened seam route only after changing `M+`; not an RH theorem.
