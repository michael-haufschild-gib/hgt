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

## Checkpoint (26/49 done, 23 remain)

Also moved: half-sided-modular-conormal-persistence-and-bounded-dilation-no-go (ConormalPersistence),
prime-coframe-completion-port-uncertainty-law (CoframePortUncertainty),
prime-valuation-cyclic-coframe-and-diagonal-dagger-defect-law (PrimeValuationCoframe).

New reusable assets:
- `ConormalPersistence`: `ModularFiltration`, `quotientDistance` + Hahn-Banach duality
  (`isGreatest_quotientDistance`), `eq_zero_of_isometric_scaling`, `scaling_defect_lower_bound`.
- `CoframePortUncertainty`: `augmentation`/`meanZero`/`closedCoframe`, the LCS one-port dichotomy
  (`one_port_dichotomy`), `jLp`/`norm_block`/`uniformWitness`, `ellOneAugmentation`.
- `PrimeValuationCoframe`: `primeAlgebra_induction` (monomial induction via
  `Finsupp.induction_linear` on `.coeff`), `valuationDeriv_mul`, `valuationPairing_*`,
  `linearIndependent_of_dual_identity`, `defectMultiplier_ne_zero`.

### Traps
- `Submodule.topologicalClosure_minimal` needs its FIRST arg explicit (`_ hle hclosed`).
- `lp E p` is a normed group only with `[Fact (1 ≤ p)]`; `lp.single` needs `(E := fun _ => ...)`.
- `RCLike.geometric_hahn_banach_closed_point` + subspace: feed it `((c+1)/f a) • a` to force
  `f a = 0`.
- `AddMonoidAlgebra.induction_on` is phrased via `of` (Multiplicative); build your own monomial
  induction from `Finsupp.induction_linear` instead.
- ℝ≥0∞ notation needs `open scoped ENNReal`.

## Checkpoint (29/49 done, 20 remain)

Also moved: source-soldering-transport-defect-cocycle-and-law-symbol (SolderingTransportSymbol),
cofinal-gamma-linear-relation-and-finite-stage-invisibility-law (CofinalGammaRelation),
cross-observer-lifting-modulus-and-singular-horizon-law (CrossObserverModulus).

New reusable assets:
- `SolderingTransportSymbol`: `bivariantDefect`, `transportCurvature`, `bivariantDefect_curved`
  (prove the CURVED identity first, get the strict cocycle as the flat corollary); `radLayer`/
  `headLayer`/`symbol` first-order law symbol with both lift directions.
- `CofinalGammaRelation`: `summableSubspace`, `gammaRel`, `gammaRel_singleValued_iff`,
  `radialMul_mapsTo_iff`, `defectExchange`.
- `CrossObserverModulus`: `liftingModulus` (ℝ≥0∞-valued!), `sigmaMin` attained on the sphere,
  `liftingModulus_id_linear` (= ε/σ_min exactly), `norm_exp_mul_I_sub_one` (circle chord identity,
  missing from mathlib).

### Traps
- `Submodule.restrictScalars` blocks unification; state a `mem_..._iff` bridge lemma once.
- `Submodule.smul_induction_on` motive is `M → Prop` (one argument), not `(z) → _ → Prop`.
- `lp`/`ℝ≥0∞` need `open scoped ENNReal NNReal`.
- Valuing a sup in ℝ≥0∞ removes every boundedness hypothesis; use
  `eq_top_of_forall_ofReal_le`-style helpers to prove `= ⊤`.

## Checkpoint (31/49 done, 18 remain)

Also moved: marked-port-normal-crossing-covariance (MarkedPortCovariance),
framed-copy-code-recovery-defect-and-wormhole-no-go (FramedCopyCode).

New reusable assets:
- `MarkedPortCovariance`: `exists_le_of_subset_biUnion` (subspace inside a FINITE UNION of
  subspaces over an INFINITE field lies in one — missing from mathlib, proved by strong induction
  + pigeonhole on the affine family y + c·x), `exists_smul_of_ker_le_ker`.
- `FramedCopyCode`: after dephasing a recovery is a classical transition matrix, so the
  entanglement-fidelity bound 1/d needs no channel/separability framework.

### NOT YET STARTED — heavy cards and what they need
- `gorenstein-trace-kahler-monogenic-equivalence-and-corank-two-splitting-law`: Theorem 1 is a
  3-way equivalence (L ≅ Ω / Ω cyclic / A monogenic). (3)=>(2) is nearly free from the existing
  `ConstraintRelativity/MonogenicKaehler.lean` (`kaehlerEquivMonogenic`, `annihilator_kaehler`).
  (3)=>(1) needs the monogenic different formula A^# = (P'(θ))^{-1}A — CHECK
  `Mathlib/RingTheory/DedekindDomain/Different.lean` for
  `differentIdeal`/`aeval_derivative` results before building. (2)=>(3) needs embedding dimension
  + Nakayama + CRT monogeneration. Theorem 2 needs Smith normal form of the Kronecker square of
  `!![-a,0;2,a]` over ℂ[[a]] giving diag(1,a²,a²,a⁴).
- `phase-subdiscriminant-kahler-smith-stratification-law` (717 lines) is the arithmetic parent of
  the Gibbs card; expect the same Smith machinery.

## Checkpoint (32/49 done, 17 remain)

Also moved: relative-law-observer-descent-duality (ObserverDescentDuality).
- `ObserverDescentDuality` assets: `pullback`, `restrictKer`,
  `range_pullback_eq_ker_restrictKer` (uses `LinearMap.exists_extend` — the field hypothesis),
  `observerDescentEquiv`, `descends_iff_vanishes`, `relativeLawEquiv` (mapping-cone LES taken as
  INPUT exactness, as the card itself cites it), `relativeObserverDuality`, `relativePairing`.

## RESOLVED — simple-horizon-rank-to-depth-transmutation-law IS NOW MOVED (33/49)

The dedup was done and all four gaps closed:
- (10) from `unitWeightedRelationsBasis` (corpus), (8) from mathlib `exteriorPower.finrank_eq`;
- (7) from corpus `rowReducedPhysicalKoszulHomologyEquiv` + `card_physicalKoszulSurvivingBasis`
  (the normalized frame makes the sequence row-reduced, which is exactly that file's setting);
- (11)(12) via `Matrix.toLinearEquiv'` on the invertible Vandermonde factor + `Submodule.quotientPi`.
LEAN TRAP: `Submodule.Quotient.equiv` leaves its RingHom args as metavariables under `.symm`/
`.trans`; give each equivalence an explicit type and compose only at the end.

## (superseded) earlier note on that card

Module `ConstraintRelativity/SimpleHorizonTransmutation.lean` is GREEN and wired, and contains:
`span_constraints_eq` (6), `constraintCovector`/`normalizedLeg`/`mem_ker_constraintCovector_iff`
(9)(10), `sheetObserver_eq` (14), `sum_val_eq_choose`, `det_sheetObserver` (15)(16),
`constraint_sub`, `disc_constraints` (16), `successor_bars` (17), `grade_dimension` (13).

STILL MISSING before the card can move:
1. (11)(12) `coker J ≅ ⊕_{j=1}^{N-1} R/(a^j)`. Route: from `sheetObserver_eq`, V is invertible
   over the local R (det V = Vandermonde of units with distinct residues is a unit), so
   `coker J ≅ coker (diagonal (a^j))`; then `range (diagonal d).mulVecLin =
   Submodule.pi univ (fun j => Ideal.span {d j})` and use `Submodule.quotientPi`.
   Add hypothesis `IsUnit (det V)` (or `∀ i≠j, IsUnit (u i - u j)` + local ring).
2. (7)(8) Koszul homology `H_• K(f_1..f_N) ≅ k ⊗ ∧^• E`, `dim H_j = binom (N-1) j`.
   CHECK whether mathlib has a Koszul complex (`Mathlib/RingTheory/Koszul*`) before building.
   The card's own proof is `K(f) ≅ K(a) ⊗ (∧^• E, 0)` since the differential is contraction by
   `a·h` and `h` is split surjective.

## IMPORTANT: corpus already owns the simple-horizon Theorem-1 layer

`GaloisForLFunctions/HTGeometry/CommonFactorKoszulHomology.lean` ALREADY contains:
- `unitWeightedAugmentation u` = the card's `h` (card (2));
- `unitWeightedRelations u` = `E = ker h`;
- `unitWeightedSplitEquiv u i₀` : `R^ι ≅ R·v ⊕ ker h` (the split used in the Koszul proof);
- `unitWeightedRelationsBasis` / `unitWeightedFinsuppRelationsBasis` : E is FREE with basis indexed
  by the non-pivot coordinates, i.e. rank N-1  ⇒ this IS card (10);
- `card_unitWeightedAway` : that index set has card N-1;
- `range_commonFactorKoszulD1` : the ideal saturation (card (6)) for two constraints;
- `commonFactorKoszulH0Equiv`, `commonFactorKoszulH1Equiv`, `commonFactorKoszulH2_eq_bot`,
  `commonFactorKoszulH1CotangentEquiv`, `IsKoszulRegular` : the full N=2 Koszul homology.
Also `PhysicalCharacteristicIncidence.lean` has
`complexPowerSeries_rowReducedPhysicalKoszulHomology_length` = `r * choose(r,k)` and
`ConvergentGermPhysicalArc.lean` the ℂ{λ} analogue.

=> My `ConstraintRelativity/SimpleHorizonTransmutation.lean` DUPLICATES `constraintCovector` and
`normalizedLeg`; REPLACE them by the corpus `unitWeightedAugmentation` / `unitWeightedRelations`
and derive card (10) from `unitWeightedRelationsBasis` instead of reproving it.

Remaining for that card after the dedup:
- (8): `dim_k (∧^j E) = choose (N-1) j` from E free of rank N-1 (look for
  `finrank_exteriorPower` / `Module.finrank_exteriorPower` in mathlib).
- (7): assemble `H_• K(f) ≅ k ⊗ ∧^• E` for general N (corpus has only N=2 explicitly; the general
  statement needs `K(f) ≅ K(a) ⊗ (∧^• E, 0)`).
- (11)(12): coker J ≅ ⊕_{j<N} R/(a^j) via `sheetObserver_eq` + invertible Vandermonde +
  `Submodule.quotientPi`.


## KEY FIND for gorenstein-trace-kahler-monogenic-equivalence (next card)

mathlib HAS the monogenic different formula the earlier checkpoint said to search for:
`Mathlib/RingTheory/DedekindDomain/Different.lean`:
  `traceForm_dualSubmodule_adjoin (hx : Algebra.adjoin K {x} = ⊤) (hAx : IsIntegral A x) :
     (traceForm K L).dualSubmodule (adjoin A {x}) = (aeval x (derivative (minpoly K x)))⁻¹ • adjoin A {x}`
That IS card (11) `A^# = (P'(θ))^{-1} A`.  Also there: `differentIdeal`, `conductor_mul_differentIdeal`,
`aeval_derivative_mem_differentIdeal`, `Submodule.traceDual`.

So Theorem 1 of that card decomposes as:
- (3)=>(1): combine `traceForm_dualSubmodule_adjoin` with
  `ConstraintRelativity/MonogenicKaehler.lean` (`kaehlerEquivMonogenic`, `annihilator_kaehler`,
  `rootDifferent`), then multiplication by P'(θ) gives A^#/A ≅ A/(P'(θ)) ≅ Ω.
- (3)=>(2): immediate from `kaehlerEquivMonogenic` (Ω is a cyclic A-module).
- (1)=>(2): A^# invertible over a semilocal ring is free of rank one, so L = uA/A is cyclic.
- (2)=>(3): the HARD direction — embedding dimension of B=A/aA, Nakayama, CRT monogeneration with
  distinct residues (needs k infinite), then Nakayama lift to A.
Theorem 2 needs the Smith form of the Kronecker square of `!![-a,0;2,a]` = diag(1,a²,a²,a⁴);
reuse the `Matrix.toLinearEquiv'` + `Submodule.quotientPi` pattern from SimpleHorizonTransmutation.

## IN PROGRESS — gorenstein-trace-kahler-monogenic-equivalence (CARD NOT MOVED, 33/49)

New module `ConstraintRelativity/GorensteinMonogenic.lean` is GREEN and wired. It contains:
- `kaehler_isPrincipal_of_monogenic` — Theorem 1 (3)=>(2): Ω of a monogenic order is cyclic,
  generated by `D(root f)`. KEY: under `kaehlerEquivMonogenic`, the class of `mk f p` corresponds
  to `mk f p • D(root f)` (NOT `mk f (derivative p) • …` — that was a wrong first guess).
- `traceQuotient_isPrincipal` — Theorem 1 (1)=>(2): a principal trace dual gives a cyclic trace
  quotient (the semilocal invertible-module step reduces to this).
- `mulDifferentEquiv` — card (12): multiplication by δ identifies `δ⁻¹A/A` with `A/(δ)`.

DONE since: `traceKaehlerEquiv_of_monogenic` — Theorem 1 (3)=>(1).  The trace dual is δ⁻¹A with
δ = rootDifferent (mathlib `traceForm_dualSubmodule_adjoin` = card (11)), so the trace quotient is
the cokernel of multiplication by δ, which `mulDifferentEquiv` sends to A/(δ), which
`kaehlerEquivMonogenic` sends to Ω.  So (1),(2),(3) are now linked in the directions
(3)=>(1), (3)=>(2), (1)=>(2).

STILL TO DO for the card:
1. (2)=>(3): the hard direction — B = A/aA is a finite product of local Artin k-algebras with
   residue field k, cyclic Ω forces dim_k m/m² ≤ 1, Nakayama makes m principal, B_i ≅ k[T]/(T^n),
   CRT with distinct λ_i (k infinite) monogenerates B, then Nakayama lifts to A.
3. Theorem 2 (13)-(17): B = R[x]/(x(x-a)), A = B⊗B; Smith form of the Kronecker square of
   `!![-a,0;2,a]` is diag(1,a²,a²,a⁴) giving L ≅ R/(a²)⊕R/(a²)⊕R/(a⁴), while Ω ≅ (R/(a²))⁴.
   Reuse the `Matrix.toLinearEquiv'` + `Submodule.quotientPi` pattern from
   SimpleHorizonTransmutation.

### gorenstein Theorem 2: Smith + Kronecker are now PROVED in Lean
(`quadDifferentMatrix`, `quadDifferent_mul_left`, `smith_quadDifferent`,
`smith_kronecker_quadDifferent`).  Historical note on the derivation:

For `M = !![-a, 0; 2, a]` over R with `2` a unit and `w := (2:R)⁻¹` (so `2*w = 1`):
    P := !![0, w; 2, a]        Q := !![1, -(a*w); 0, 1]
    P * M     = !![2*w, w*a; 0, a^2]        (= !![1, w*a; 0, a^2])
    P * M * Q = !![1, 0; 0, a^2]            (entry (0,1) is w*a*(1 - 2*w) = 0)
    det P = -(w*2) = -1  (unit),  det Q = 1.
Kronecker square: `(P⊗ₖP) * (M⊗ₖM) * (Q⊗ₖQ) = (P*M*Q) ⊗ₖ (P*M*Q)` by
`Matrix.mul_kronecker_mul` used twice, then `Matrix.diagonal_kronecker_diagonal` gives
`diagonal fun p => d p.1 * d p.2` = diag(1, a², a², a⁴) — card (19).
`Matrix.det_kronecker` gives the unit determinants.

LEAN OBSTACLE HIT: `ext i j; fin_cases i <;> fin_cases j <;> simp` leaves four goals needing
DIFFERENT `linear_combination` coefficients in `hvw : 2*w = 1` (namely 1, w*a, 0, 0), so a single
`<;>` chain cannot close them.  Next time: prove `P * M = !![1, w*a; 0, a^2]` as its own lemma
(one `ext` + per-entry `linear_combination`), then multiply by Q where no unit is needed.


## gorenstein card status after this window (CARD STILL NOT MOVED)

PROVED in `ConstraintRelativity/GorensteinMonogenic.lean` (green, wired):
- `kaehler_isPrincipal_of_monogenic`  — Thm 1 (3)=>(2)
- `traceQuotient_isPrincipal`         — Thm 1 (1)=>(2)
- `mulDifferentEquiv`                 — card (12)
- `traceKaehlerEquiv_of_monogenic`    — Thm 1 (3)=>(1)  [uses mathlib traceForm_dualSubmodule_adjoin = card (11)]
- `quadDifferentMatrix`, `quadDifferent_mul_left`, `smith_quadDifferent` — card (18), Smith form diag(1,a²)
- `smith_kronecker_quadDifferent`     — card (19), Kronecker Smith form diag(1,a²,a²,a⁴)

REMAINING for the card:
(A) Turn (19) into card (16): `L = coker(mul by d_x d_y) ≅ R/(a²) ⊕ R/(a²) ⊕ R/(a⁴)`.
    Use the SimpleHorizonTransmutation pattern: `Matrix.toLinearEquiv'` on the unimodular factors
    + `range_diagonal_mulVecLin`-style lemma + `Submodule.quotientPi`.  (The index type is
    `Fin 2 × Fin 2`; the `1` factor contributes `R/(1) = 0`.)
(B) Card (17): `Ω ≅ (R/(a²))⁴` from `Ω ≅ A/(d_x)dx ⊕ A/(d_y)dy` and `B/(d_x) ≅ R/(a²)`
    (the latter is `smith_quadDifferent` again, one factor).
(C) Thm 1 (2)=>(3): the hard direction (embedding dim of B=A/aA, Nakayama, B_i ≅ k[T]/(T^n),
    CRT with distinct residues since k infinite, Nakayama lift).
LEAN NOTE: `fin_cases i <;> fin_cases j <;> simp [...]` often leaves exactly ONE goal; end with a
plain `ring` on the next line, not `<;> ring` (the unnecessarySeqFocus linter is an error here).

### gorenstein next step is now unblocked (all inputs proved)

`smith_kronecker_quadDifferent` now also returns `IsUnit P.det ∧ IsUnit Q.det` (via
`Matrix.det_kronecker` + `IsUnit.pow`), and `SimpleHorizonTransmutation.range_diagonal_mulVecLin'`
was generalized to an arbitrary index type and arbitrary diagonal `d : n → R`.  So card (16) is
now a mechanical assembly:

  coker (M ⊗ₖ M) ≅ coker D ≅ ∀ p, R ⧸ span {d p}   with d p = ![1,a²] p.1 * ![1,a²] p.2

using exactly the `cokerSheetObserverEquiv` proof shape.

LEAN TRAP that blocked the first attempt: a `noncomputable def` CANNOT `obtain` the matrices out of
the ∃ in `smith_kronecker_quadDifferent` (`Exists.casesOn` only eliminates into `Prop`).  Two fixes:
either (a) state the result as `theorem … : Nonempty (… ≃ₗ[R] …)`, or (b) restate
`smith_kronecker_quadDifferent` as a `def` returning the pair plus proofs (a structure/Σ-type), or
(c) take P and Q as explicit arguments of the def.  Prefer (a).

## gorenstein status (still 33/49 — card NOT moved)

Now PROVED in `GorensteinMonogenic.lean` (green, wired):
Thm 1: (3)=>(2) `kaehler_isPrincipal_of_monogenic`, (1)=>(2) `traceQuotient_isPrincipal`,
       (3)=>(1) `traceKaehlerEquiv_of_monogenic`, plus `mulDifferentEquiv` (card 12).
Thm 2: `quadDifferentMatrix`, `quadDifferent_mul_left`, `smith_quadDifferent` (18),
       `mul_kronecker_mul_smith` (reusable), `smith_kronecker_quadDifferent` (19),
       `nonempty_cokerQuad` (17 input), `nonempty_cokerQuadTensorOne` (20),
       `nonempty_cokerKronecker` (16).
Shared, in `SimpleHorizonTransmutation.lean`:
       `range_diagonal_mulVecLin'` (general index/diagonal) and
       `nonempty_coker_equiv_pi_of_smith` (Smith data => product cokernel).  USE THESE, do not
       re-derive the coker-from-Smith argument again.

ONLY REMAINING for the card:
- assemble card (17) `Ω ≅ (R/(a²))⁴` = two copies of `nonempty_cokerQuadTensorOne` (one per
  hypersurface relation d_x, d_y), i.e. Ω ≅ A/(d_x)dx ⊕ A/(d_y)dy with each summand (R/(a²))²;
- Thm 1 (2)=>(3): B = A/aA is a finite product of local Artin k-algebras with residue field k;
  cyclic Ω forces dim_k m/m² ≤ 1; Nakayama makes m principal so B_i ≅ k[T]/(T^n); CRT with
  distinct λ_i (k infinite) monogenerates B; Nakayama lifts the generator to A.

## gorenstein: THEOREM 2 IS NOW COMPLETE

Added `nonempty_cokerOneTensorQuad` (20, second relation), `nonempty_omega_corank_two` (17 boxed:
Ω ≅ product of the two hypersurface cokernels, each (R/(a²))²), and
`corank_two_length_eq_partition_ne` (same total length 8, invariant-factor exponents 4 vs 2).
So cards (18),(19),(16),(20),(17) and the length/partition comparison are all proved.

## ONLY Theorem 1 (2)=>(3) remains for the gorenstein card

mathlib finds for it (searched, do NOT rebuild):
- `IsLocalRing.finrank_cotangentSpace_le_one_iff [IsNoetherianRing R] :
     finrank (ResidueField R) (CotangentSpace R) ≤ 1 ↔ (maximalIdeal R).IsPrincipal`
  — this packages the card's steps (6) "cotangent fibre = m/m²" AND the Nakayama step
  "dim ≤ 1 ⇒ m principal" in one lemma.  File: Mathlib/RingTheory/Ideal/Cotangent.lean.
- `IsArtinianRing.equivPi` is only for REDUCED Artinian rings (product of FIELDS); it is NOT the
  decomposition needed here (B = A/aA is Artinian but not reduced).  Look instead for the
  local-decomposition of an Artinian ring, or avoid it: the card only needs each local factor
  B_i ≅ k[T]/(T^{n_i}) and then CRT, so `Ideal.quotientInfRingEquivPiQuotient` (CRT) plus the
  principal-maximal-ideal fact may suffice without a global product decomposition.
- Remaining genuinely-new bits: Ω_{B/k} ≅ Ω_{A/R} ⊗_A B (base change — check
  `KaehlerDifferential.tensorProductTo`/`kerToTensor` neighbourhood in Kaehler/Basic.lean), and the
  final Nakayama lift A = R[θ] + aA ⇒ A = R[θ].

## MAJOR FIND — corpus already owns the gorenstein (2)=>(3) endgame

`GaloisForLFunctions/HTGeometry/DedekindOrderMonogenic.lean` contains:
- `maxExt S B` — the base maximal ideal extended to the algebra (the card's `aA`);
- `adjoin_eq_top_of_adjoin_quotient_eq_top [Module.Finite S B] (α) :
     Algebra.adjoin S {mk (maxExt S B) α} = ⊤ → Algebra.adjoin S {α} = ⊤`
  === THIS IS THE CARD'S NAKAYAMA LIFT (9) "A = R[θ] + aA ⇒ A = R[θ]".  DO NOT REBUILD IT.
- `adjoin_base_eq_top_of_adjoin_residue` — generation over the residue field is generation over the
  base (removes the k-vs-R bookkeeping in the card's step (8));
- `exists_adjoin_eq_top_quotient_dedekind` and
  `exists_adjoin_eq_top_of_dedekind_finite` — residue-level monogeneration, assembled.

CONSEQUENCE: the gorenstein card's (2)=>(3) now reduces to ONE genuinely missing step:
  "Ω_{A/R} cyclic  ⇒  B = A/aA is monogenic over k".
Route (card steps 5–8): Ω_{B/k} ≅ Ω_{A/R} ⊗_A B is cyclic ⇒ for each local factor
`dim_k m_i/m_i² ≤ 1` ⇒ (mathlib `IsLocalRing.finrank_cotangentSpace_le_one_iff`) m_i principal ⇒
B_i ≅ k[T]/(T^{n_i}) ⇒ CRT with distinct λ_i (k infinite) gives a single generator of B.
Then `adjoin_base_eq_top_of_adjoin_residue` + `adjoin_eq_top_of_adjoin_quotient_eq_top` finish.

## gorenstein: card (7) local step now PROVED

`exists_sub_aeval_mem_pow` + `adjoin_eq_top_of_isPrincipal_nilpotent` in GorensteinMonogenic.lean:
a local k-algebra whose maximal ideal is principal (`t`) and nilpotent, with residue field k
(hypothesis stated as `∀ b, ∃ c : k, b - algebraMap c ∈ span {t}`, i.e. B = k + (t)), is
`Algebra.adjoin k {t} = ⊤`.  Proof: approximate b by polynomials in t to every order n by
induction, then t^n = 0 kills the error.  This is the card's B_i ≅ k[T]/(T^{n_i}) step in the form
actually needed (no explicit iso required).

REMAINING for (2)=>(3): only the passage
  Ω_{A/R} cyclic ⇒ each local factor of B = A/aA has principal maximal ideal
(via Ω_{B/k} ≅ Ω_{A/R} ⊗_A B and `IsLocalRing.finrank_cotangentSpace_le_one_iff`),
plus CRT to glue the factors into one generator of B.  The lift to A is corpus-owned
(`adjoin_eq_top_of_adjoin_quotient_eq_top`, `adjoin_base_eq_top_of_adjoin_residue`).

## MAJOR FIND 2 — mathlib HAS the non-reduced Artinian local decomposition

`Mathlib/RingTheory/Artinian/Module.lean`:
  `IsArtinianRing.quotNilradicalPowEquivPi (n : ℕ) :
     (R ⧸ nilradical R ^ n) ≃ₐ[R] ∀ I : MaximalSpectrum R, R ⧸ I.asIdeal ^ n`
  "the quotient of a commutative Artinian ring by a POWER of its nilradical is isomorphic to a
   finite product of LOCAL rings".
Since the nilradical of an Artinian ring is nilpotent (`IsArtinianRing.isNilpotent_jacobson_bot`
/ nilradical nilpotent), taking n with `nilradical^n = 0` gives `R ≃ₐ ∏_I R/m_I^n` directly.
So the earlier note "IsArtinianRing.equivPi is only for REDUCED rings, need something else" is
RESOLVED — use `quotNilradicalPowEquivPi`, NOT a hand-built decomposition.

### Full remaining plan for gorenstein Thm 1 (2)=>(3) — every ingredient now located
1. B = A/aA is Artinian (finite-dim over k).
2. `quotNilradicalPowEquivPi` with n such that nilradical^n = 0  ⇒  B ≃ₐ ∏_I B/m_I^n, local factors.
3. Ω_{A/R} cyclic ⇒ Ω_{B/k} cyclic (base change) ⇒ each factor has finrank cotangent ≤ 1
   ⇒ `IsLocalRing.finrank_cotangentSpace_le_one_iff` ⇒ maximal ideal principal.
4. `adjoin_eq_top_of_isPrincipal_nilpotent` (PROVED HERE) ⇒ each factor monogenic over k.
5. CRT glue: distinct λ_i ∈ k (k infinite) ⇒ the element (λ_i + t_i)_i generates ∏; needs
   idempotent extraction from `Ideal.quotientInfRingEquivPiQuotient`.
6. Lift to A: corpus `adjoin_base_eq_top_of_adjoin_residue` then
   `adjoin_eq_top_of_adjoin_quotient_eq_top` (DedekindOrderMonogenic.lean).
Only steps 3 (base change) and 5 (CRT glue) still need Lean work.

## gorenstein CRT step: two of three pieces landed

PROVED and green in GorensteinMonogenic.lean:
- `adjoin_image_singleton_eq_top` — a surjective algebra map carries a single generator to a
  single generator (generally useful; use `(AlgHom.range_eq_top f).2 hf`, the dot form fails).
- `isCoprime_shift_pow` — distinct centres give pairwise coprime `span {(X - C λᵢ)^{nᵢ}}`
  (via `Polynomial.isCoprime_X_sub_C_of_isUnit_sub`, `IsCoprime.pow`,
  `Ideal.isCoprime_span_singleton_iff`).

NOT landed: `exists_adjoin_pi_quotient_eq_top` (card (8) proper).
LEAN TRAP: building the AlgEquiv from `Ideal.quotientInfRingEquivPiQuotient` via
`AlgEquiv.ofRingEquiv halg` with `halg := fun _ => rfl` causes a whnf TIMEOUT (even at 1e6
heartbeats) — the CRT equiv does not reduce.
FIX FOR NEXT TIME: do NOT transport through an AlgEquiv.  Instead use the surjective algebra map
`k[X] → ∀ i, k[X] ⧸ I i` directly (Pi.algHom of the `Ideal.Quotient.mkₐ`), prove its surjectivity
from CRT (look for `Ideal.quotientInfToPiQuotient_surj` / `Ideal.exists_forall_sub_mem_ideal` in
Mathlib/RingTheory/Ideal/Quotient/Operations.lean), then apply
`adjoin_image_singleton_eq_top _ hsurj Polynomial.adjoin_X`.  One line, no rfl on the CRT map.

## gorenstein card (8) IS NOW PROVED

`piQuotAlgHom` (= `AlgHom.pi fun i => Ideal.Quotient.mkₐ k (I i)`),
`piQuotAlgHom_surjective` (from mathlib `Ideal.quotientInfToPiQuotient_surj` +
`Ideal.Quotient.mk_surjective`), and
`exists_adjoin_pi_quotient_eq_top` — a finite product of local quotients at DISTINCT centres is
generated by one element.  Three lines once the AlgEquiv detour is abandoned; the recorded fix
worked exactly as written.  NOTE: `Pi.algHom` is deprecated -> `AlgHom.pi`.

### gorenstein: ONE step left
Only the base change `Ω_{B/k} ≅ Ω_{A/R} ⊗_A B` (card step (5)) is unwritten, i.e. the passage
"Ω_{A/R} cyclic ⇒ Ω_{B/k} cyclic ⇒ each local factor of B has principal maximal ideal".
Everything else of (2)=>(3) is in place:
  local decomposition   = mathlib `IsArtinianRing.quotNilradicalPowEquivPi`
  cotangent ≤ 1 ⇒ principal = mathlib `IsLocalRing.finrank_cotangentSpace_le_one_iff`
  local factor monogenic = `adjoin_eq_top_of_isPrincipal_nilpotent` (here)
  CRT glue              = `exists_adjoin_pi_quotient_eq_top` (here)
  lift to A             = corpus `adjoin_base_eq_top_of_adjoin_residue`,
                          `adjoin_eq_top_of_adjoin_quotient_eq_top`
Look for the base change at `KaehlerDifferential.tensorProductTo` / `kerToTensor` in
Mathlib/RingTheory/Kaehler/Basic.lean, or `KaehlerDifferential.baseChange`.

## gorenstein card DONE (34/49 in stage 3; 15 left in stage 2)

New module `ConstraintRelativity/GorensteinResidualFibre.lean` (green, wired) closes (2)⇒(3):
- `isPushout_quotientMap` — `Algebra.IsPushout R (R⧸I) A (A⧸I·A)`; mathlib has NO such instance.
  Built from `Algebra.TensorProduct.quotIdealMapEquivQuotTensor` + `IsBaseChange.of_equiv`.
  Unlocks `KaehlerDifferential.tensorKaehlerEquiv` = card (5).
- `residueDerivation` / `surjective_liftKaehler` — mathlib has NO map `Ω[C⁄k] ↠ 𝔪/𝔪²`. Built as
  the k-derivation `c ↦ c − σ(c̄)`; Leibniz error is `−(a−σā)(b−σb̄) ∈ 𝔪²`. Then
  `isPrincipal_maximalIdeal_of_kaehler_cyclic` via `finrank_cotangentSpace_le_one_iff`.
- `exists_sub_algebraMap_mem_of_isPrime` — separating family `φ : ι → (A →ₐ[R] R)` ⇒ every prime
  of A has residue ring = image of R. Proof: `⨅ ker φᵢ = ⊥ ≤ p` + `Ideal.IsPrime.inf_le'`.
  This is how "A ⊆ R^N split ⇒ residue fields are k" gets formalized.
- `exists_adjoin_pi_eq_top_of_local` — product step needing only `Infinite k`, NOT CharZero.
  Corpus `ProductMonogenic.exists_adjoin_pi_eq_top` needs CharZero because
  `PolynomialShiftSeparation.eq_zero_of_comp_add_C_eq_self` is FALSE in char p (Artin–Schreier:
  h = X^p − X has period 1). Avoided entirely: our factors all have irreducible X, so translating
  to distinct centres λᵢ suffices — no shift-separation lemma needed.
- `adjoin_eq_top_of_adjoin_residual` — Nakayama via
  `Submodule.sup_eq_sup_smul_of_le_smul_of_le_jacobson` with J = ⊥ (cleanest form: N ⊔ ⊤ = N ⊔ ⊥•⊤).

EDIT MADE TO CORPUS: `ProductMonogenic.lean` variable block lost `[CharZero κ]`; it is now a
binder on `exists_adjoin_pi_eq_top` only. `adjoin_add_algebraMap` is therefore field-general.

Traps hit:
- `ResidueField R` is NOT reducible: `Algebra (ResidueField R) (A⧸IA)` does NOT synthesize.
  Use `R ⧸ maximalIdeal R` and `letI : Field _ := Ideal.Quotient.field _` inside the proof.
- `Field (R ⧸ maximalIdeal R)` is not found by instance search either.
- A type family named `C : ι → Type*` collides with `Polynomial.C` under `open Polynomial`.
- `Derivation.mk'` wants a bare `→ₗ[k]`; build it as
  `toCotangent.restrictScalars k ∘ₗ resShiftLinear` or `map_smul` picks the wrong map.
- `intro a -` is not valid; use `intro a _`.

## IN PROGRESS: congruence-order-trace-kahler-exterior-square-nonmetricity-law
Module `ConstraintRelativity/CongruenceOrderExteriorSquare.lean` (green so far, NOT yet wired).

DONE:
- `congruenceOrder a N : Subalgebra R (Fin N → R)` = `{v | ∀ i j, a ∣ v i - v j}` (= R·1 + a·O).
- `observerProj` / `ker_observerProj` / `observerDefectEquiv` — **card (3)** `O/A ≅ k^m`.
- `congruenceGen i = a • Pi.single i.castSucc 1`; `congruenceEval = aeval congruenceGen`.
- `congruenceRelations`/`congruenceIdeal` = span{X_i²−C a X_i} ∪ {X_i X_j, i≠j}.
- `linForm c₀ c = C c₀ + ∑ C (c i) * X i`; `exists_linForm` — every f is ≡ a linear normal form
  mod the ideal (induction on MvPolynomial, `mul_X` step uses both relation families).
- `congruenceEval_linForm_apply/_castSucc/_last`, `range_congruenceEval = congruenceOrder`,
  `ker_congruenceEval` (needs `[IsDomain R] (ha : a ≠ 0)`), `congruencePresentation` — **card (15)**.

NEXT (card (5), `Ω ≅ (R/a²)^m ⊕ (R/a)^C(m,2)`), the plan that avoids mathlib's conormal machinery:
- `M := (Fin m → A) ⧸ N`, `N = A-span {Pi.single i (2xᵢ−a)} ∪ {Pi.single i xⱼ + Pi.single j xᵢ}`.
- `Ψ : M →ₗ[A] Ω[A⁄R]` by `Submodule.liftQ` of `v ↦ ∑ v i • D(xᵢ)`.
- `d_P := MvPolynomial.mkDerivation R (fun i => ē i) : Derivation R P M`  (mkDerivation EXISTS,
  needs `[Module P M] [IsScalarTower R P M]`; M gets `Module P` from
  `Submodule.Quotient.module'` + `IsScalarTower.right`).
- `d_P` kills each relation generator (that is exactly N), hence kills I, hence descends to
  `d_A : Derivation R A M`; `Φ := d_A.liftKaehlerDifferential`. Φ and Ψ are inverse on generators.
- Then the R-module computation `M ≅ (R/a²)^m ⊕ (R/a)^{i<j}` using the R-basis {eᵢ, xⱼeᵢ}:
  relations give `xᵢdxᵢ = (a/2)dxᵢ`, `a·xⱼdxᵢ = 0`, `a²dxᵢ = 0`, `xⱼdxᵢ = −xᵢdxⱼ`.
Remaining card items after that: (4) trace dual Smith, (6) `Ω/aΩ ≅ C ⊕ Λ²C` (base change is
already available: `kaehlerQuotientBaseChange` in GorensteinResidualFibre), (26k)/(26l) differents,
(26e)–(26g) soldering obstruction, (27)/(28) lengths.

### congruence card: Ω is IDENTIFIED (structural half of card (5) done)
`kaehlerModelEquiv : Ω[(P ⧸ congruenceIdeal)⁄R] ≃ₗ[A] (Fin m → A) ⧸ kaehlerRelations a m`.
Chain: `kaehlerEval` (∑ vᵢ • D xᵢ) → `kaehlerRelations_le_ker` → `modelToKaehler` (liftQ);
`modelDerivation = MvPolynomial.mkDerivation` → `modelDerivation_eq_zero_of_mem` → `quotDerivation`
(descends by `Submodule.liftQ ((congruenceIdeal).restrictScalars R)` — the quotient types
`P ⧸ I` and `P ⧸ I.restrictScalars R` ARE defeq, `Derivation.mk'` + `Quotient.inductionOn'`)
→ `kaehlerToModel`; inverse both ways via `Finset.univ_sum_single` and
`Derivation.ext_of_adjoin_eq_top` + `adjoin_congruenceX_eq_top`.
STILL TO DO for (5): the R-module computation
`(Fin m → A) ⧸ kaehlerRelations ≅ (R/a²)^m ⊕ (R/a)^{i<j}` using the R-basis {eᵢ, xⱼeᵢ} of A^m.

LEAN TRAP (cost me many rounds): on `Ω[A⁄R]` and on `(Fin m → A) ⧸ N`, `rw`/`simp` with
`zero_smul`, `add_smul`, `mul_smul`, `two_smul` FAIL to unify (and the `module` tactic reports
"ℕ is not an A-algebra"). Workarounds that work: give the fully explicit term
(`exact zero_smul (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) w`), or rewrite the HYPOTHESIS
forward instead of contracting the goal. Also: state relations as `x + x - a`, never `2 * x - a`.

### congruence card: order is R-free (module wired + green)
`linFormMap` (coprod of `toSpanSingleton` and `Fintype.linearCombination`), `linFormLinear`,
`congruenceCoordEquiv (ha : a ≠ 0) : (R × (Fin m → R)) ≃ₗ[R] P ⧸ congruenceIdeal a m`.
TRAP: do NOT hand-roll a `→ₗ[R] (P ⧸ I)` with `map_smul' := by rw [Algebra.smul_def]` — the
`Module R (P ⧸ I)` instance elaboration picks `Submodule.Quotient.module'`, not `Algebra.toModule`,
so every smul rewrite fails. Build the map by COMPOSING standard maps with
`(Ideal.Quotient.mkₐ R I).toLinearMap` instead; then all instances agree.
