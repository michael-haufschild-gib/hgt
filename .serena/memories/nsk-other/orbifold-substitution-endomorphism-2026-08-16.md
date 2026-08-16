# Orbifold-tail card: the substitution endomorphism, its order descent, and the normalization

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/rational-coarse-graining-orbifold-tail-classification.md`
Dependent cards: `floquet-orbifold-tail-emergence`, `orbifold-tail-holographic-reconstruction`.

## Built (all unconditional, axiom-clean, umbrella-wired)

`HTGeometry/JetRationalSubstitution.lean` — `jetSubstitution R hR` (= `Phi_R`), `orbifoldTail`,
chain rule, `(T1)`, `(T3)`, `jetSubstitution_jet_one : Phi_R(y1) = y1·R'(y0)` (exact scaling at
order one), `IsInvariantDifferential`, `invariantCurrent`,
`differentialAdjoin_le_orbifoldTail_of_isInvariantDifferential`,
`isInvariantDifferential_pd_of_order_zero_eigen`.

`HTGeometry/TwistedScalingDescent.lean` — generic polynomial layer over any field:
`twistComp Phi T P = (P.map Phi).comp T`; degree/leadingCoeff laws for `natDegree T = 1`;
`exists_scalars_of_twisted_cross` (coprimality splits the cross identity);
`coeff_eigen_of_twistComp_scale` (pure scaling ⇒ every coefficient is an eigenvector);
`coeff_affine_pow`; **`twistComp_affine_cocycle`** (the two top coefficients of a split affine
relation solve `Phi(g) = rho·g - (a+1)L`).

`HTGeometry/JetSubstitutionDescent.lean` (~900 lines)
- prefix fields `jetPrefixField C M` = `C(y_0..y_(M-1))`, `mem_jetPrefixField_iff` (order below M),
  transcendence of `y_M`, `jetPrefixField_succ`, `jetPrefixField_zero`,
  `exists_algebraMap_of_forall_pd_eq_zero`, `jetSubstitutionPrefix` (restriction of `Phi_R`)
- affine normal form `substitutionShift R M`, `substitutionAffine R hM`,
  `jetSubstitution_aeval_of_act` (transport in ANY coordinate on which `Phi_R` acts polynomially)
- `SubstitutionEigen R hR M kappa w lam` := `w != 0 ∧ ord w ≤ M ∧ Phi_R(w)·R'^kappa = lam·w`;
  `IsInvariantDifferential = SubstitutionEigen … 0 …` (Iff.rfl)
- `exists_coprime_slicing_of_coordinate` / `exists_coprime_slicing`
- `substitutionEigen_leadingRatio` / `exists_substitutionEigen_pred` (order descends by one,
  exponent shifts by the degree difference)
- `exists_isInvariantDifferential_of_substitutionEigen`, `exists_isInvariantDifferential_of_eigen`
  — EVERY finite-order eigenvector carries an invariant differential with the same eigenvalue
- `exists_nonzero_isInvariantDifferential_or_eq_one` — the weight is nonzero unless `lam = 1`
- ORDER ONE CLOSED: `substitutionShift_one`, `substitutionAffine_eq_scale`,
  `substitutionEigen_coeffRatio`, `exists_nonzero_isInvariantDifferential_of_order_one`,
  `exists_nonzero_isInvariantDifferential_of_pd_one_ne_zero`,
  `exists_differentialAdjoin_invariantCurrent_le_orbifoldTail`
- **NORMALIZATION (2026-08-16 late)**: `exists_normalizing_shift`, `jetSubstitution_jet_add`
  (`Phi_R(y_M + t) = R'·(y_M + t)`), `lowerOrder_or_exists_scalingCoordinate`,
  `transcendental_add_algebraMap` (already existed in `RatFuncPositiveJetBranchSeparation` — reuse,
  do not redeclare), `intermediateField_adjoin_add_algebraMap`, and the capstone
  **`substitutionEigen_normalized_trichotomy`**:
      SubstitutionEigen M kappa w lam, M ≥ 1, lam ≠ 0 ⇒
        (i)  ord w ≤ M-1, or
        (ii) ∃ n ≠ 0, s : SubstitutionEigen (M-1) n s 1, or
        (iii) ∃ n ≠ 0, s : SubstitutionEigen (M-1) (kappa+n) s lam.

## The one remaining obligation — now pinned to order two

Following branch (iii) from `kappa = 0` writes `w = e·prod_j z_j^(n_j)` with `e` of order zero and
`sum n_j = 0`, `z_j = y_j + t_j` the normalized coordinates.  The shift `t_2` must solve

    alpha(R(z))·R'(z)^2 - R'(z)·alpha(z) = -R''(z),   alpha rational,

i.e. **`R` preserves a rational affine connection (Christoffel symbol) on P^1**.  Two facts checked
by hand:
- for `R = z^d` the solution is `alpha = -1/z`, and `Gamma' - Gamma^2/2 = 1/(2z^2)` is the invariant
  quadratic differential (weight 2, eigenvalue `d^2`);
- for `R = z^2+1` the equation forces a pole at `0`, hence at every point of the infinite backward
  orbit of `0` — impossible for a rational `alpha`.  This is the same orbit mechanism as the card's
  tensor argument.
General identity (verified by hand, not yet formalized): if `Gamma` is an invariant affine
connection then `P := Gamma' - Gamma^2/2` satisfies `P(R)·R'^2 = P - S_R` with `S_R` the Schwarzian
— an eigen-relation only when `S_R` is proportional to `P`.  So "invariant connection ⇒ invariant
tensor" is NOT automatic; the orbit/pole argument is the route.

To close: (a) Laurent normal form of the shift (slice `t` itself in the previous coordinate, where
the substitution is again a pure scaling, so `substitutionEigen_coeffRatio` applies and every
Laurent coefficient except the one at the exponent of `L` is an invariant differential);
(b) "no invariant rational affine connection for a non-exceptional map" by the orbit/pole argument.

## Lean process notes
- `set x := e with h` CLEARS AND RE-INTRODUCES every hypothesis whose type mentions `e`, making
  them inaccessible (`P✝`).  Put all `set`s BEFORE any `obtain`, or avoid `set` entirely.
- `not_imp` is ambiguous; use `Classical.not_imp`.
- `refine ⟨_, _, …, hres⟩` only infers the holes if the determining term comes last.
