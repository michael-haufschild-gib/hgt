# nsk/other stage-3 sweep — 2026-08-16 session

Standing goal: promote every card in `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other`
to stage 3 with unconditional Lean. Ledgers to tick on a promotion: this memory, the Serena memory
`nsk-other/stage3-sweep-ledger-2026-08-13`, and the on-disk card
`docs/drafts/pipeline/1-in-progress/other-stage3-closure-ledger.md`.

**Six `ccm-unit-riesz-*` / `ccm-four-unit-*` cards sitting in that folder belong to a concurrently
running CCM agent** (it writes its certificates into `3-formalized/new_scientific_knowledge/ccm/`).
Do not touch them; work the non-ccm cards. 34 cards remain in the folder (28 non-ccm).

Also: `scripts/formal_tools.py lint` currently reports one unrelated error,
`RHTower.BandBarrierRatio` unreachable from the RHTower umbrella — another agent's module, not ours.

## PROMOTED 2026-08-16 (1): `scalar-ht-horizon-celestial-sphere`

- `HTGeometry/ProjectiveHorizonCelestialSphere.lean` — `rowHorizon C x c d` = the first derivative
  horizon cut out by the denominator covector `(c,d)`.
  `jetTailField_mobiusObservable_one_eq_rowHorizon` (choice independence), `rowHorizon_eq_iff`,
  `rowHorizon_sup_inf` (exact join `jetTailField C x 0`, exact meet
  `actualSchwarzianDifferentialField C x`), `rowHorizon_mobiusObservable` (equivariance),
  `celestialHorizon` on `ℙ C (Fin 2 → C)` with `celestialHorizon_injective`,
  `celestialHorizon_sup_inf`, `celestialHorizon_infinity_fixed_iff` (parabolic stabilizer),
  `celestialHorizon_pair_fixed_iff` (Cartan stabilizer), `orientedGeodesicSpace`,
  `existsUnique_orientedGeodesic`, `hypertranscendentalOver_celestialSphere_realization_prime`
  (prime-field instance with no constants hypothesis).
- `HTGeometry/HyperbolicThreeSpaceBoundary.lean` — `H^3` as unimodular positive-definite Hermitian
  complex `2x2` matrices; `HyperbolicThreeSpace.symmetricSpace_model` (transitivity by an explicit
  Cholesky factor + isotropy = unitary part), `exists_eq_lightMatrix`, `lightMatrix_smul_iff`
  (light rays modulo positive scale = `ℙ¹(C)`), `lightMatrix_mulVec`.
- `HTGeometry/ScalarHorizonCelestialBoundary.lean` — the weld,
  `scalarHorizon_celestialSphere_realization`.

## PROMOTED 2026-08-16 (2): `nonlinear-rational-observation-curve-horizon-reconstruction`

- `HTGeometry/JetPrincipalSymbolExtraction.lean` — **`exists_mem_pd_ratio`**, the general Lüroth
  principal-symbol theorem: in a derivation-closed `K` strictly above the constants inside
  `JetField C Unit`, two elements of the same exact scalar differential order `n` satisfy
  `∂_{x_n} w / ∂_{x_n} v ∈ K`. Also `pd_differentialJet_top` (principal symbols are unchanged by
  differentiation), `exists_mem_mul_of_mem_adjoin`, `derivation_eq_zero_of_mem_adjoin`,
  `derivation_mem_adjoin_of_mem_adjoin`, `pd_eq_zero_of_mem_jetObservableField`,
  `differentialAdjoin_jets_eq_top_iff` (identity-view dichotomy).
- `HTGeometry/DerivationAlgebraicDescent.lean` — **`mem_of_isAlgebraic_of_derivation_mem`**: for
  `K ≤ Y` and a derivation `D` preserving `K` with no constants in `Y` outside `K`, an element of
  `Y` algebraic over `K` with `D T ∈ K` lies in `K`. Proof differentiates the minimal polynomial.
  Also `derivMapCoeffs`, `derivation_aeval_eq` (chain rule with varying coefficients).
- `HTGeometry/RationalObservationCurveNormalization.lean` — the Main theorem
  **`exists_differentialAdjoin_jetFamily_eq`** and the normalized dichotomy
  `differentialAdjoin_jetFamily_eq_top_iff`; plus `mem_adjoin_of_pd_ratio_mem`,
  `differentialAdjoin_jetFamily_ne_top_of_affine`, `exists_adjoin_range_ratFuncEval_eq_adjoin`
  (ordinary Lüroth transported into the jet field).

## Reusable corpus assets (do not rebuild)

- `differentialLuroth` (`HTGeometry/DifferentialLurothSingleGenerator.lean`) — unconditional.
- `HasScalarDifferentialOrder` + `.comp` (order additivity), `.differentialJet_order`,
  `.transcendental`, `.hypertranscendentalOver`, `existsUnique_hasScalarDifferentialOrder`,
  `hasScalarDifferentialOrder_zero_iff` (`HTGeometry/ScalarDifferentialRationalOrder.lean`).
- `hasScalarDifferentialOrder_differentialJet`, `hasScalarDifferentialOrder_self`
  (`ScalarDifferentialOrderWitness.lean`).
- `JetField.pd`, `pd_deriv_succ`, `commutator_pd_succ`, `derivation_ext`
  (`FreeDifferentialJetField.lean`). `JetField C Unit` is *definitionally*
  `FreeCoordinateRationalField C (Unit × ℕ)`, so the `freeCoordinate*` kernel theorems apply — but
  `rw`/`simp` will not see through the instance paths; only `exact`/type ascription will.
- `exists_algebraMap_of_forall_freeCoordinateDerivation_eq_zero`,
  `mem_freeCoordinateField_of_forall_freeCoordinateDerivation_eq_zero`,
  `mem_freeCoordinateTailField_iff`.
- `ProjectiveJetHorizon.lean`: `mobius_jetTailField_one_eq_iff`, `jetTailField_constSlopeAffine_eq`,
  `mobiusDenominator_ne_zero_of_hypertranscendentalOver`,
  `jetTailField_inv_ne_of_hypertranscendentalOver`, `differentialJet_constSlopeAffine`.
- `rational_positiveJet_observation_eq_top` (Lemma 2 of the rational-observation card),
  `isAlgebraic_ratFuncEval_over_adjoin`, `ratFuncEval` API
  (`RatFuncPositiveJetFieldReconstruction.lean`, `TranscendentalMobius.lean`).
- `Mathlib.FieldTheory.RatFunc.Luroth` (`RatFunc.Luroth.eq_adjoin_generator`),
  `Derivation.mapCoeffs`, `Derivation.apply_aeval_eq'`.
- `eq_algebraMap_of_isAlgebraic_deriv_eq_zero` (`JetFieldAlgebraicBranchRigidity.lean`).
- `Differential.differentialFiniteDimensional` / `differentialAlgebraFiniteDimensional`,
  `Differential.algHom_deriv'`, `differentialJet_algHom` — the normal-closure/embedding scaffolding
  is spelled out inside `RatFuncPositiveJetFieldReconstruction.lean`.

## Lean workflow notes for this tree

- `omit [...] in` must come BEFORE a docstring, not between docstring and `theorem`.
- After `rintro _ ⟨i, rfl⟩` on `Set.range f`, the goal keeps a beta-redex; use
  `rintro z ⟨i, hzi⟩; have hz : z = f i := hzi.symm; rw [hz]`.
- `set` does not always abstract occurrences that carry proof arguments (`ratFuncEval y ⋯`).
