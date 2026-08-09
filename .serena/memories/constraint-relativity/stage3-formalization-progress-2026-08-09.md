# constraint-relativity → stage 3 formalization progress (2026-08-09)

Goal: unconditionally formalize every proven theorem in
`docs/drafts/pipeline/2-fully-proven/constraint-relativity` (49 cards at start), wire into
`GaloisForLFunctions.HTGeometry`, issue `<id>-formalized.md` companions, `git mv` each card to
`docs/drafts/pipeline/3-formalized/constraint-relativity/`.

## Lean area

`formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/` — namespace
`HTGeometry.ConstraintRelativity`. Imports appended at the END of
`formal/GaloisForLFunctions/HTGeometry.lean`. `lake build GaloisForLFunctions.HTGeometry` green
after every batch (~50–120 s incremental).

## DONE — 17 cards in stage 3 (34 files there: card + companion each)

faithful-reencoding-no-law-promotion → `CloneReencoding`;
dynamic-question-relation-balance-law → `QuestionRelationBalance`;
source-word-filtration-and-selection-no-go → `WordFiltrationSelection`;
fixed-transformation-defect-closure-no-promotion → `DefectClosure`;
source-norm-support-forgetful-tower-law → `ForgetfulTower`;
dual-number-static-observer-deformation-erasure-law → `DualNumberErasure`;
cofinal-observer-conservativity-law → `CofinalConservativity`;
rank-one-source-naturality-rigidity-and-framing-law → `RankOneFraming`;
initial-execution-symmetry-inheritance-and-anomaly-necessity → `SymmetryInheritance`;
prime-infinity-port-capacity-and-root-conormal-law → `PortCapacity`;
quadratic-law-discriminant-bockstein-controlled-horizon → `QuadraticLawHorizon`;
monogenic-law-discriminant-observer-shadow-theorem → `MonogenicShadow`;
radial-affine-torsor-and-cross-prime-flatness-no-go → `RadialAffineTorsor`;
framed-provenance-curvature-scalar-no-go → `ProvenanceCurvature`;
heterogeneous-triangle-singular-holonomy-law → `TriangleHolonomy`;
constitutive-soldering-intertwiner-energy-law → `ConstitutiveSoldering` (+ `ReynoldsEnergy`);
observer-ramification-horizon-exponent-no-go → `SincHorizonExponent`.

Infrastructure modules with no card of their own: `MonogenicKaehler`, `ReynoldsEnergy`.

## Notes on the soldering card (DONE)

`ConstitutiveSoldering.lean` reuses the corpus's `QuantumAlg.Util.HilbertSchmidt.hsInner`
(`⟪A,B⟫ = Tr[Aᴴ B]`) — mathlib has NO `InnerProductSpace` on `Matrix`, only scoped Frobenius
*norm* instances. Contains: `hsNormSq` + unitary invariance, `solderDefect` (renamed from
`transportDefect` to avoid an umbrella collision with `ForgetfulTower.transportDefect`),
`solderDefect_mul` (cocycle), `solderAction`, `reynoldsProj`, `curvatureEnergy`,
`curvatureEnergy_eq` (= card (6)), `curvatureEnergy_eq_zero_iff`,
`exists_unitary_curvatureEnergy_eq_zero_iff`, `isCompact_solderingSet`,
`continuous_curvatureEnergy`, `exists_positive_gap` (= card (7)), and the `C₂` minimal example
(`c2_reynoldsProj`, `c2_curvatureEnergy`, `c2_no_flat_soldering`).
`ReynoldsEnergy.lean` is the coordinate-free version on any complex inner product space.

## Reusable infrastructure built here (absent from mathlib AND from the corpus)

- `MonogenicKaehler`: `Ω[R[X]/(f) ⁄ R] ≅ R[X]/(f) ⧸ (f'(α))` (`kaehlerEquivMonogenic`),
  `annihilator_kaehler`. Needed by congruence-order-trace-kahler…, gorenstein-trace-kahler…,
  phase-subdiscriminant-kahler…, prime-radial-excess….
- `QuestionRelationBalance`: `map_mkQ_inf`, `mapMkQEquivQuotient`,
  `finrank_map_add_finrank_inf_ker`.
- `RankOneFraming`: `quadPoly/quadAlgebra/quadDiscr` + split/dual classification.
- `MonogenicShadow`: conormal presentation, Vandermonde observer, discriminant shadows.
- `SincHorizonExponent`: `cos_le_quartic`, `sin_le_quintic` — the alternating Taylor bounds mathlib
  lacks (its `Real.sin_bound` constant 4/100 is too weak for the sharp 19/120), proved by
  `monotoneOn_of_deriv_nonneg` from mathlib's `Real.sin_gt_sub_cube`; plus `exponent_ratio_tendsto`
  and `tendsto_log_abs_atBot`.
- `ReynoldsEnergy`: finite-group averaging energy identity.

## CORPUS ASSETS FOUND (reuse, do not rebuild)

- `HTGeometry/DifferentialTranscendenceDegree.lean`, `DifferentialSubfieldTransfer.lean`,
  `DifferentialMatroid.lean` (`differentialMatroid`, `differentialMatroid_ground`,
  `differentialMatroid_indep_iff`, `differentialMatroid_mem_closure_iff_of_indep`,
  `differentialAlgebraicOver_trans_finite_nonempty`), `DifferentialAdjoinFiniteTrdeg.lean`.
- `HTGeometry/PrimeTorusKroneckerDensity.lean` — `primeTorus_kronecker_dense`,
  `primeTorus_cpow_dense`.
- `HTGeometry/EquidistributedPhaseThreshold.lean` — `sum_sq_spacedPhase_eq_zero`.
- `HTGeometry/NormalCrossingCriticalDerivedPhase.lean` — `NormalCrossingKoszulGradeInput`.
- `HTGeometry/DiscriminantPolynomial.lean`, `GenericPolynomialSeparable.lean` (generic polynomial).
- `HTGeometry/UniversalDeRham.lean`.
- mathlib: `Algebra.discr_powerBasis_eq_norm K pb`, `Matrix.det_vandermonde(_ne_zero_iff)`,
  `KaehlerDifferential.polynomialEquiv`, `Derivation.map_aeval`,
  `Matroid.Spanning.cRank_le_cardinalMk`, `exists_nhds_zero_half`, `Real.sin_bound`,
  `norm_sub_sq`, `RCLike.re_to_complex`, `inner_self_eq_norm_sq`.

## Lean traps hit (do not rediscover)

- `HasQuotient ↥P (Submodule k ↥P)` FAILS when the ambient is `A ⊗[k] ↥V`. Use
  `Submodule.map R.mkQ P` in the ambient quotient.
- `Matrix.fromColumns` absent; `Matrix.inv_smul` takes the matrix first.
- `Polynomial.modByMonic_add_div (p q)` has NO monic hypothesis; `dvd_modByMonic_sub p q`.
- `Ordinal.limitRecOn` cases `zero | add_one | limit`; `Ordinal.pos_iff_ne_zero` gone;
  `le_or_lt` gone → `lt_or_ge`; `Real.exp_eq_one_iff` takes x explicitly;
  `Fin.card_filter_le` absent → `Finset.Ici` + `Fin.card_Ici`.
- `SMulCommClass k A M` derivable from `Algebra k A` + `IsScalarTower k A M`.
- Lint treats warnings as errors: clear unused-simp-arg, `simpa`→`simp`, and unused section
  variables (`omit [...] in` / `omit hU in`).
- `HTGeometry.ConstraintFrameRelativity.*` unreachable-from-umbrella lint errors belong to ANOTHER
  session; do not touch.

## PARTIAL — generalized-prime-compound-countermodel-to-universal-selector

`GeneralizedPrimeCountermodel.lean` is written, green, and wired: `stokesForm`, `legTransport`,
`legTransport_stokes` (card (7)), `radialDefect_ne_zero` (card (8)), `scalarPortDefect` +
`scalarPortDefect_ne_zero` (card (8a), rank one), `coframeDefect` + `coframeDefect_injective`
(hostile-audit item 4). CARD NOT MOVED — still missing the group-algebra layer, card (1)–(6):
`Γ_c` algebra automorphism, `∂_j` derivation, identity-coefficient trace `τ`, and the prime atom
identities `τ(u_i)=1`, `φ_j(u_i)=−δ_ij`, `Γ_c^{⊗2}u_i=u_i`.
TRAP: in this mathlib `AddMonoidAlgebra k G` is NOT defeq to `G →₀ k` — `Finsupp.single`,
`Finsupp.lsum`, `Finsupp.lapply` do not typecheck against it. Use `AddMonoidAlgebra.single`,
`AddMonoidAlgebra.single_mul_single`, and the `ofFinsupp`/`toFinsupp` bridges (or build the maps
with `AddMonoidAlgebra.lift`).

## REMAINING (32 cards)

Planned order and known obstacles:
1. `cofinal-ht-to-recurrence-rank-transfer-bound` — `Matroid.Spanning.cRank_le_cardinalMk`; prove
   `Set.range y` spanning in `differentialMatroid F E` via a matroid basis `I ⊆ range y`,
   `differentialMatroid_mem_closure_iff_of_indep`, then
   `differentialAlgebraicOver_trans_finite_nonempty` over base `differentialAdjoin F I`
   (needs `derivationClosedDifferential` instances).
2. `finite-prime-gibbs-modular-phase-realization` — reuse `primeTorus_kronecker_dense`; needs its
   arithmetic parent `phase-subdiscriminant-kahler-smith-stratification-law` first (the
   "fixed-radius torus meets H₂ = 0" theorem).
3. `simple-horizon-rank-to-depth-transmutation-law` — Koszul homology + Smith normal form over a
   DVR + Vandermonde; heaviest in the folder.
4. `neutral-fusion-unobstructed-relative-cotangent-law` — `Algebra.FormallySmooth` /
   `Algebra.H1Cotangent` for a localized polynomial algebra.
5. finish `generalized-prime-compound-countermodel-to-universal-selector` (see PARTIAL above).
Then the remaining 27.

## Another session is editing the tree

`HTGeometry/ConstitutiveMetricPhaseExactness.lean` (untracked, mtime seconds old) currently FAILS
with three `linarith` errors and breaks the umbrella build. It is NOT ours — do not touch it.
Verify our own modules with `lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.<M>`
until their file is green again.

## Umbrella collision warning

Declaration names must be unique across the WHOLE `HTGeometry` umbrella. `transportDefect` in
`ConstitutiveSoldering` collided with `ForgetfulTower.transportDefect` and only the umbrella build
caught it. Prefix new names distinctively.


## Checkpoint update (session continued)

- 20 of 49 cards are now in stage 3.  29 remain in stage 2.
- NEW: `generalized-prime-compound-countermodel-to-universal-selector` MOVED (group-algebra layer
  completed).  Trap resolved: `AddMonoidAlgebra R M` is a structure with field `coeff : M →₀ R`;
  build linear maps through `coeffLinearEquiv : PrimeAlgebra ι ≃ₗ[ℂ] (PrimeGrades ι →₀ ℂ)` and use
  `AddMonoidAlgebra.single` / `single_mul_single` / `coeff_single` (all `rfl`).
- NEW module `RankOneOrientation.lean` — card `rank-one-orientation-lorentzianization-law` MOVED.
  Key reusable pieces: `IsAbsoluteSplitting` (D H + j T = 1) with `isCompl`/`quotEquiv`/
  `observer_decomp`; Riesz port `portVector`/`portAxis`/`portForm`; and
  `finrank_le_one_of_portForm_nonpos`, which states `ind₋ + dim Rad ≤ 1` uniformly as
  "every subspace with Q ≤ 0 has finrank ≤ 1" — that formulation avoids all signature machinery.
- NEW module `IdentitySectorRadialBlindness.lean` — card
  `identity-sector-radial-gauge-blindness-and-cross-grade-selection-law` MOVED.  Reusable graded
  layer: `gradeComponent`, `gradeDiag` (diagonal multiplier map), `gradeGaugeHom`/`gradeGauge`
  (character ⇒ algebra automorphism), `gradeDiag_leibniz` (additive multiplier ⇒ derivation),
  `identityTrace`, `kummerCocycle`, plus `totalGrade` list lemmas for Hochschild faces.

### Lean traps found this window

- `GradedRing.proj` is only an `AddMonoidHom`; for a `ℂ`-linear projection build it from
  `DirectSum.component` + `decomposeLinearEquiv`, and prove the two component lemmas by
  `have h1 : gradeComponent 𝒜 i x = ((DirectSum.decompose 𝒜 x i : 𝒜 i) : A) := rfl` and then
  `DirectSum.decompose_of_mem_same` / `decompose_of_mem_ne`.
- When a definition's implicit argument is only determined by a hypothesis of the form
  `f 0 = 1`, unification is higher-order and fails: make `f` explicit.
- `omit [Inst] in` must come BEFORE the docstring, never between docstring and `theorem`.
- `Real.log_eq_zero_iff` does not exist; use `Real.eq_one_of_pos_of_log_eq_zero`.
- `Real.finsetProd_rpow` (not `finset_prod_rpow`) is the finite-product rpow lemma.
- mathlib HAS the adelic product formula: `Height.AdmissibleAbsValues`, instantiated for every
  number field (so for `ℚ`).

## Checkpoint (23/49 done, 26 remain)

Moved since last note: neutral-fusion-unobstructed-relative-cotangent-law (NeutralFusionCotangent),
cofinal-ht-to-recurrence-rank-transfer-bound (CofinalRankTransfer),
finite-prime-gibbs-modular-phase-realization (GibbsModularPhase).

New reusable Lean assets in ConstraintRelativity/:
- `kaehlerBasisOfAlgEquiv` — transport of a Kähler basis along an algebra iso (mathlib lacks it);
  proved via "an iso is formally étale" + `KaehlerDifferential.isBaseChange_of_formallyEtale`.
- `cardinalMk_le_differentialTranscendenceDegree`, `differentialTranscendenceDegree_le_of_adjoin_eq_top`
  — the two one-sided differential-matroid rank bounds (corpus only had the equality case).
- `totient_prod_of_pairwise_coprime` — finite-product totient multiplicativity.
- `diagonal_mul_single_mul_diagonal` — matrix-unit conjugation by diagonals.
- `cubeRoot`, `subdiscriminant_three`, `exists_sum_eq_zero_of_triangle`,
  `exists_phase_subdiscriminant_eq_zero` — equilateral criterion for H2 = 0 on concentric circles.

### Traps
- `fin_cases i` leaves indices as `⟨1, ⋯⟩`; `Matrix.cons_val_one` will NOT fire. Avoid `![...]`
  definitions when you need per-index numerals: define `fun j => <arith in (j:ℕ)>` and finish with
  `split_ifs <;> omega`.
- `Real.log_eq_zero_iff` does not exist -> `Real.eq_one_of_pos_of_log_eq_zero`.
- `Complex.norm_eq_sqrt_normSq` does not exist -> `Complex.normSq_eq_norm_sq` + `Real.sqrt_sq`.
- `RingHom.charZero f` transfers CharZero to a subfield.
