# nsk/other stage-3 sweep — 2026-08-16 session

Standing goal: promote every card in `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other`
to stage 3 with unconditional Lean. Ledgers to tick on a promotion: this memory family, the Serena
memory `nsk-other/stage3-sweep-ledger-2026-08-13`, and the on-disk card
`docs/drafts/pipeline/1-in-progress/other-stage3-closure-ledger.md`.

**Six `ccm-unit-riesz-*` / `ccm-four-unit-*` cards sitting in that folder belong to a concurrently
running CCM agent** (it writes its certificates into `3-formalized/new_scientific_knowledge/ccm/`).
Do not touch them; work the non-ccm cards.

## PROMOTED 2026-08-16: `scalar-ht-horizon-celestial-sphere`

Three new modules, all axiom-clean and umbrella-wired:

- `HTGeometry/ProjectiveHorizonCelestialSphere.lean` — `rowHorizon C x c d` is the first derivative
  horizon cut out by the denominator covector `(c,d)`.
  `jetTailField_mobiusObservable_one_eq_rowHorizon` (choice independence),
  `rowHorizon_eq_iff` (equality iff same projective class), `rowHorizon_sup_inf` (exact join
  `jetTailField C x 0` and exact meet `actualSchwarzianDifferentialField C x` at any distinct pair),
  `rowHorizon_mobiusObservable` (equivariance: the covector transports by the matrix),
  `celestialHorizon` on `ℙ C (Fin 2 → C)` with `celestialHorizon_injective`,
  `celestialHorizon_sup_inf`, `celestialHorizon_infinity_fixed_iff` (parabolic stabilizer),
  `celestialHorizon_pair_fixed_iff` (Cartan stabilizer), `orientedGeodesicSpace`,
  `existsUnique_orientedGeodesic`, and a prime-field instance
  `hypertranscendentalOver_celestialSphere_realization_prime` that discharges the
  "base is constants" hypothesis outright.
- `HTGeometry/HyperbolicThreeSpaceBoundary.lean` — `H^3` as unimodular positive-definite Hermitian
  complex `2x2` matrices; `HyperbolicThreeSpace.symmetricSpace_model` (transitivity of `SL(2,C)` by
  an explicit Cholesky factor plus isotropy = unitary part), `exists_eq_lightMatrix`,
  `lightMatrix_smul_iff` (light rays modulo positive scale = `ℙ¹(C)`), `lightMatrix_mulVec`.
- `HTGeometry/ScalarHorizonCelestialBoundary.lean` — the weld,
  `scalarHorizon_celestialSphere_realization`.

Reusable: the Hermitian `H^3` model and its light-ray boundary are new corpus assets; any later card
needing rank-one hyperbolic geometry or `PSL_2(C)`-boundary language should import them.

## IN PROGRESS: `nonlinear-rational-observation-curve-horizon-reconstruction`

`HTGeometry/JetPrincipalSymbolExtraction.lean` (new, axiom-clean, umbrella-wired) closes Lemma 1 in
full generality and the identity-view dichotomy `(7)`:

- `exists_mem_pd_ratio` — **the general Lüroth principal-symbol theorem**. In a derivation-closed
  `K` strictly above the constants inside `JetField C Unit`, two elements of the same exact scalar
  differential order `n` have `∂_{x_n} w / ∂_{x_n} v ∈ K`. Proof: differential Lüroth `K = C⟨u⟩`,
  order additivity puts both in `C(u,…,u^{(s)})` with `s = n − r`, all lower jets of `u` are killed
  by `∂_{x_n}`, and one adjoin induction shows `∂_{x_n}` maps that subfield into `(that subfield)·t`
  with `t = ∂_{x_n} u^{(s)}`.
- `pd_differentialJet_top`, `exists_mem_mul_of_mem_adjoin`, `derivation_eq_zero_of_mem_adjoin`,
  `derivation_mem_adjoin_of_mem_adjoin`, `pd_eq_zero_of_mem_jetObservableField` — reusable.
- `differentialAdjoin_jets_eq_top_iff` — `C⟨x^{(n)}, (r(x))^{(n)}⟩ = C⟨x⟩ ↔ r not affine`, for
  `n ≥ 1`.

**Remaining for that card: the general `m`-view Main theorem.** Route written out at the tail of the
card. Short version: extraction gives the slope ratios `q_i = R_i'/R_1'` in `L_n`; one nonconstant
order-zero element in `L_n` forces the Lüroth generator `u` of `L_n` to have order zero, i.e.
`u ∈ C(y)`; extraction again gives `R_i'(y)/u'(y) ∈ C(u)`; every `C(u)`-embedding `σ` of `C(y)`
commutes with the unique derivation extension and fixes that ratio, so `σ(R_i(y)) − R_i(y)` is an
algebraic differential constant hence in `C`, and iterating `σ` to its finite order kills it in
characteristic zero; so every embedding fixes each `R_i(y)`, giving `C(y) ⊆ C(u)`. Mirror the
normal-closure/embedding scaffolding of `RatFuncPositiveJetFieldReconstruction.lean` and reuse
`eq_algebraMap_of_isAlgebraic_deriv_eq_zero` from `JetFieldAlgebraicBranchRigidity.lean`.

## Corpus assets found this session (do not rebuild)

- `differentialLuroth` (`HTGeometry/DifferentialLurothSingleGenerator.lean`) — unconditional.
- `HasScalarDifferentialOrder` + `.comp` (order additivity), `.differentialJet_order`,
  `.transcendental`, `.hypertranscendentalOver`, `existsUnique_hasScalarDifferentialOrder`
  (`HTGeometry/ScalarDifferentialRationalOrder.lean`).
- `hasScalarDifferentialOrder_differentialJet` (`ScalarDifferentialOrderWitness.lean`).
- `JetField.pd`, `pd_deriv_succ`, `commutator_pd_succ`, `derivation_ext`
  (`FreeDifferentialJetField.lean`); `JetField C Unit` is *definitionally*
  `FreeCoordinateRationalField C (Unit × ℕ)`, so the `freeCoordinate*` kernel theorems apply — but
  `rw`/`simp` will not see through the instance paths, only `exact`/type ascription will.
- `exists_algebraMap_of_forall_freeCoordinateDerivation_eq_zero`,
  `mem_freeCoordinateField_of_forall_freeCoordinateDerivation_eq_zero`, `mem_freeCoordinateTailField_iff`.
- `ProjectiveJetHorizon.lean` already owns `mobius_jetTailField_one_eq_iff`,
  `jetTailField_constSlopeAffine_eq`, `mobiusDenominator_ne_zero_of_hypertranscendentalOver`,
  `jetTailField_inv_ne_of_hypertranscendentalOver`.
- `Mathlib.FieldTheory.RatFunc.Luroth` exists; `OrdinaryLuroth.lean` gives degree-one Lüroth
  (`ratFunc_generator_mobius`).
