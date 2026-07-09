# Sonin Cutoff Transversality Realization

- **ID:** sonin-cutoff-transversality-realization
- **Stage:** 0-backlog
- **Type:** CANDIDATE / CONJECTURE
- **Source:** `../3-formalized/new/cutoff-cross-boundary-seam-nonmember.md`;
  `../3-formalized/new/mplus-torsion-seam-extension.md`;
  `../../rh-monodromy-weight-mismatch/lean_updates_codex.md`
- **Statement:** `[CONJECTURE]` The next non-remote handle on the RH-false route is the actual
  Sonin/prolate cutoff action, not a finite Hankel/Li visibility test. If the semilocal prime action
  has a cutoff-crossing cochain

  `Delta_{p,lambda} := (1 - Q_lambda) U_p Q_lambda`

  whose induced torsion seam presentation has

  `X^m ∤ tr(adj(A_lambda) Delta_{p,lambda})`,

  then the prime side supplies a nonfake, determinant-transverse seam defect in the extended
  `M+` category. If every actual Sonin cutoff presentation is determinant-compatible, this handle dies.

## Goal

Deconflict from the remote-defect / finite-probe route. The question here is not how far out an
off-line zero hides from finite degree. The question is whether the source action itself crosses a
nonlocal cutoff in a way that survives the Fitting boundary quotient before any zero-location,
Hankel, Markov, or Li positivity chart is evaluated.

Existing formal cards already prove the abstract algebra:

- pinned-germ scalar actions have zero cross-boundary cochain;
- commutator defects `sigma A - A sigma` have zero Fitting boundary;
- an abstract cutoff-crossing cochain can be determinant-transverse and nonfake;
- split diagonal torsion presentations are boundary-blind.

So the only possible new content is arithmetic realization: identify the actual semilocal
Sonin/prolate cutoff, the actual prime dilation action, and the actual local presentation, then compute
the low coefficient of `tr(adj(A) Delta)`.

## Gates

- [x] 0 -> 1 candidate shape: different from remote visibility; source-side cutoff action; attack listed
- [ ] 1 -> 2 fully-proven: construct the actual Sonin cutoff presentation and prove either determinant
  transversality or determinant compatibility
- [ ] 2 -> 3 formalized: Lean statement for the concrete `Q_lambda`, `U_p`, `A_lambda`, and the low
  coefficient witness
- [ ] 3 -> 4 publication-ready

## Attack

- This is not a proof of RH. It is an attempt to locate a source-side obstruction class.
- This cannot reuse the pinned-germ prime action: that action is central at the local germ and already
  collapses.
- This cannot use the commutator `sigma A - A sigma`: formal trace cyclicity kills it for every
  presentation.
- This cannot use a split torsion presentation: the split model is boundary-blind even for a crossing
  corner.
- This cannot grade success by detecting an off-line zero. The witness must be the low coefficient of
  `tr(adj(A) Delta)` in the actual source-built cutoff model.

## Approach

1. Define the concrete Sonin/prolate cutoff `Q_lambda` and prime action `U_p` in the semilocal model.
2. Extract the local torsion seam presentation `A_lambda` at a pinned seam divisor.
3. Compute the row-replacement determinant form

   `tr(adj(A_lambda) Delta_{p,lambda})
    = sum_i det(A_lambda with row i replaced by row_i(Delta_{p,lambda}))`.

4. Promote only one of two outcomes:

   - `[PROVED]` determinant-transverse: some coefficient below `m` is nonzero, giving a nonfake
     source-side seam class;
   - `[PROVED]` determinant-compatible: all such traces are divisible by `X^m`, killing this handle.

## Log

- 2026-07-09 - created from the route deconfliction request: avoid remote/finite-probe visibility and
  push the distinct Sonin cutoff-crossing torsion seam realization instead.
- 2026-07-09 - [BRIDGE] Extracted the existential non-split witness into named Lean API in
  `formal/GaloisForLFunctions/RHTower/CutoffCochain.lean`:
  `polynomialLowerCrossing`, `polynomialLowerCrossing_eq_crossBoundary`,
  `shearTorsionPresentation`, `shearTorsionPresentation_det`,
  `fittingBoundaryTrace_shearTorsion_lowerCrossing`,
  `fittingBoundaryClass_shearTorsion_lowerCrossing_ne_zero`,
  `lowerCrossing_not_right_factor_shearTorsion_mod_X_pow`, and
  `lowerCrossing_not_left_factor_shearTorsion_mod_X_pow`.  This does not solve the arithmetic
  Sonin realization; it gives the concrete sheared normal form that the actual `Q_lambda`, `U_p`,
  `A_lambda` calculation must hit or fail to hit.
- 2026-07-09 - [BRIDGE] The open arithmetic computation is now one coordinate residue in a sheared
  chart, not a full adjugate-trace calculation.  The Lean card
  `../3-formalized/new/sheared-seam-coordinate-criterion.md` proves that for
  `A_m = [[X^m,1],[0,1]]`, every defect satisfies
  `tr(adj(A_m) Delta) = Delta_00 - Delta_10 + X^m Delta_11`, so the Fitting class is exactly
  `jetClass(Delta_00 - Delta_10)`.  Thus actual Sonin/prolate data must prove either
  `X^m ∤ (Delta_{p,lambda,00} - Delta_{p,lambda,10})` in a source-built sheared chart, or prove that
  this entry difference is always divisible by `X^m`.
- 2026-07-09 - [BRIDGE] The residue criterion is now packaged as a concrete one-label
  `TorsionSeamPresentation`: `shearedTorsionSeam m Delta`.  For this object, Lean proves
  `HasDeterminantTransverseDefect` iff `X^m ∤ (Delta_00 - Delta_10)`, and residue nondivisibility
  gives both right and left nonfake defects.  The actual Sonin/prolate task can therefore target the
  single statement `X^m ∤ ((1-Q_lambda) U_p Q_lambda)_00 - ((1-Q_lambda) U_p Q_lambda)_10` after a
  source-built sheared chart is constructed.
