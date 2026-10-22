import GaloisForLFunctions.HTGeometry.CalibrationSpectrumMechanics
import GaloisForLFunctions.HTGeometry.CayleyFockOrderSpaceConservation
import GaloisForLFunctions.HTGeometry.CayleyPoleResidueTransport
import GaloisForLFunctions.HTGeometry.ComplexAffineAlgebraicNoetherian
import GaloisForLFunctions.HTGeometry.CompositionTransportBianchi
import GaloisForLFunctions.HTGeometry.ConstitutiveBiFormationAllOrder
import GaloisForLFunctions.HTGeometry.ConstitutiveObserverFibreChirality
import GaloisForLFunctions.HTGeometry.ConstitutiveReporterMeetPromotion
import GaloisForLFunctions.HTGeometry.ConstitutiveSplitFormationParallax
import GaloisForLFunctions.HTGeometry.ConstitutiveSymmetricFormationHomology
import GaloisForLFunctions.HTGeometry.ConstitutiveTripleReporterFusion
import GaloisForLFunctions.HTGeometry.ConstitutiveUnitaryReflectionPersistence
import GaloisForLFunctions.HTGeometry.CyclicGaugeAttainmentWallCrossing
import GaloisForLFunctions.HTGeometry.DifferentialOperatorPrincipalIdeal
import GaloisForLFunctions.HTGeometry.EventDescentTransgression
import GaloisForLFunctions.HTGeometry.GammaMeixnerAlienChargePolarization
import GaloisForLFunctions.HTGeometry.InterfinityGeometry.TerminalTransgression
import GaloisForLFunctions.HTGeometry.IteratedBlockHypersurfaceDimension
import GaloisForLFunctions.HTGeometry.IteratedUnitCoefficientBlockDimension
import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonExactConservation
import GaloisForLFunctions.HTGeometry.LongitudinalTransverseFormationMechanics
import GaloisForLFunctions.HTGeometry.MarkedHalfCharacterDualityLaw
import GaloisForLFunctions.HTGeometry.MarkedVariationDynamics
import GaloisForLFunctions.HTGeometry.MultipleGammaPeriodActionRankLaw
import GaloisForLFunctions.HTGeometry.NoetherNormalizationKrullDim
import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.CrossedModule
import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.CyclicActionNoether
import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.CyclicGaugeHolonomyMasterAction
import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.GaugeSpectralFlow
import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.SplitLInfinityObserverExtension
import GaloisForLFunctions.HTGeometry.ProjectiveAffineChartIncidenceDimension
import GaloisForLFunctions.HTGeometry.StaticCircuitTwoMemoryOrthogonalityLaw
import GaloisForLFunctions.HTGeometry.FiniteLawRelationWallSynchronization

/-!
# Noether applications across the reusable corpus

This module records premise-free applications of three mathematical families carrying Noether's
name or mechanism:

* first-Noether conservation under time, unitary, phase, and gauge symmetries;
* second-Noether Bianchi identities forced by redundant descriptions;
* algebraic Noether finiteness, normalization, and descending-chain consequences.

Arguments below are mathematical data, not proposition-valued assumptions.  Laws whose only local
form in the corpus still needs an analytic or invariance hypothesis are intentionally absent.
-/

noncomputable section

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-! ## First and second Noether mechanisms -/

open _root_.HTGeometry.NomologicalHomotopyGeometry

/-- The corpus's complete cyclic variational package: Euler--Lagrange equals Maurer--Cartan,
critical points are Maurer--Cartan solutions, and gauge directions annihilate variation. -/
theorem noether_cyclicAction_complete
    {k L : Type*} [Field k] [CharZero k] [AddCommGroup L] [Module k L]
    (A : CyclicActionNoether.CyclicMaurerCartanLaw (k := k) (L := L)) :
    (∀ N α η,
      CyclicActionNoether.firstVariationPartial A.toCyclicOperations N α η =
        A.pairing η (CyclicActionNoether.mcPartial A.toCyclicOperations N α)) ∧
      (∀ N α, CyclicActionNoether.IsCriticalPartial A.toCyclicOperations N α ↔
        CyclicActionNoether.mcPartial A.toCyclicOperations N α = 0) ∧
      (∀ α, A.twisted α (A.mc α) = 0) ∧
      (∀ α ε, CyclicActionNoether.variationalForm A α
        (CyclicActionNoether.gaugeVariation A α ε) = 0) :=
  CyclicActionNoether.cyclic_action_euler_lagrange_noether A

/-- Second Noether theorem in its sharp off-shell form: every infinitesimal gauge direction is in
the kernel of the variational one-form. -/
theorem noetherSecond_infinitesimalGauge
    {k L : Type*} [Field k] [AddCommGroup L] [Module k L]
    (A : CyclicActionNoether.CyclicMaurerCartanLaw (k := k) (L := L)) (α ε : L) :
    CyclicActionNoether.variationalForm A α
      (CyclicActionNoether.gaugeVariation A α ε) = 0 :=
  CyclicActionNoether.infinitesimal_gauge_invariance A α ε

/-- A strict cyclic coordinate symmetry preserves every finite action quotient. -/
theorem noetherFirst_cyclicCoordinateAction
    {L M : Type*} [AddCommGroup L] [Module ℝ L] [AddCommGroup M] [Module ℝ M]
    {A : CyclicActionNoether.CyclicOperations (k := ℝ) (L := L)}
    {B : CyclicActionNoether.CyclicOperations (k := ℝ) (L := M)}
    (F : CyclicActionNoether.CyclicOperationsEquiv A B) (N : ℕ) (α : L) :
    CyclicActionNoether.actionPartial B N (F.map α) =
      CyclicActionNoether.actionPartial A N α :=
  CyclicGaugeHolonomyMasterAction.actionPartial_natural F N α

/-- BV/Hamiltonian form: classical master equation is exactly square-zero source law. -/
theorem noetherBV_masterEquation
    {C H : Type*} [AddCommGroup C] [Module ℝ C] [AddCommGroup H] [Module ℝ H]
    (A : CyclicGaugeHolonomyMasterAction.HamiltonianCorrespondence (C := C) H)
    (Q : CyclicGaugeHolonomyMasterAction.End (C := C)) :
    A.poisson (A.hamiltonian Q) (A.hamiltonian Q) = 0 ↔
      CyclicAInfinityLaw.QGeometry.square Q = 0 :=
  A.masterEquation_iff_square_zero Q

/-- Crossed-module gauge curvature obeys its covariant Bianchi identity. -/
theorem noetherSecond_crossedModuleBianchi
    {G₁ G₂ G₃ H₂ H₃ : Type*}
    [AddCommGroup G₁] [AddCommGroup G₂] [AddCommGroup G₃]
    [AddCommGroup H₂] [AddCommGroup H₃]
    [Module ℝ G₁] [Module ℝ G₂] [Module ℝ G₃] [Module ℝ H₂] [Module ℝ H₃]
    (D : CrossedModule.DifferentialCrossedModuleCalculus G₁ G₂ G₃ H₂ H₃) (A : G₁) :
    D.covariantG A (D.curvature A) = 0 :=
  D.curvature_bianchi A

/-- Split `L∞` extension curvature obeys the commutator Bianchi identity. -/
theorem noetherSecond_splitExtensionBianchi
    {C : Type*} [AddCommGroup C] [Module ℝ C]
    (A : SplitLInfinityObserverExtension.CyclicExtensionLaw (C := C)) :
    A.totalLaw.comp (CyclicAInfinityLaw.QGeometry.square A.totalLaw) -
        (CyclicAInfinityLaw.QGeometry.square A.totalLaw).comp A.totalLaw = 0 :=
  A.total_square_bianchi

/-- Curvature of every terminal one-cochain satisfies the monoid-cohomology Bianchi identity. -/
theorem noetherSecond_terminalTransgressionBianchi
    {k M E : Type*} [Semiring k] [Monoid M] [AddCommGroup E] [Module k E]
    [TopologicalSpace E] (D : Interfinity.TerminalDatum k M E)
    (b : M → E) (g h q : M) :
    D.curvature b g h + D.curvature b (g * h) q =
      D.π g (D.curvature b h q) + D.curvature b g (h * q) :=
  D.bianchi b g h q

/-- Event-seam defects obey a discrete descent Bianchi identity without flatness assumptions. -/
theorem noetherSecond_eventSeamBianchi
    {R K I C : Type*} [CommRing R]
    [AddCommGroup K] [Module R K] [AddCommGroup I] [Module R I]
    [AddCommGroup C] [Module R C]
    (a : Module.End R K) (d : Module.End R I) (p : Module.End R C)
    (b : I →ₗ[R] K) (r : C →ₗ[R] I) (η : C →ₗ[R] K) :
    (eventSeamDefect a d b).comp r + b.comp (eventSeamDefect d p r) -
        eventSeamDefect a p η =
      eventSeamDefect a p (eventTriangleDefect b r η) :=
  eventSeam_triangleDefect_bianchi a d p b r η

/-- Composition transport has an exact nonlinear triangle Bianchi identity. -/
theorem noetherSecond_compositionTransportBianchi
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (μ₀ μ₁ μ₂ : BilinearComposition R V) (T₀₁ T₁₂ T₀₂ : V →ₗ[R] V) (x y : V) :
    T₁₂ (compositionTransportDefect T₀₁ μ₀ μ₁ x y) +
        compositionTransportDefect T₁₂ μ₁ μ₂ (T₀₁ x) (T₀₁ y) -
        compositionTransportDefect T₀₂ μ₀ μ₂ x y =
      comparisonPathDefect T₀₁ T₁₂ T₀₂ (μ₀ x y) -
        μ₂ (comparisonPathDefect T₀₁ T₁₂ T₀₂ x) (T₀₂ y) -
        μ₂ (T₀₂ x) (comparisonPathDefect T₀₁ T₁₂ T₀₂ y) -
        μ₂ (comparisonPathDefect T₀₁ T₁₂ T₀₂ x)
          (comparisonPathDefect T₀₁ T₁₂ T₀₂ y) :=
  compositionTransportDefect_triangle_bianchi μ₀ μ₁ μ₂ T₀₁ T₁₂ T₀₂ x y

/-- Projective composition transport exposes the central phase anomaly in its Bianchi identity. -/
theorem noetherSecond_projectiveCompositionTransportBianchi
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (a : R) (μ₀ μ₁ μ₂ : BilinearComposition R V)
    (T₀₁ T₁₂ T₀₂ : V →ₗ[R] V) (x y : V) :
    T₁₂ (compositionTransportDefect T₀₁ μ₀ μ₁ x y) +
        compositionTransportDefect T₁₂ μ₁ μ₂ (T₀₁ x) (T₀₁ y) -
        a • compositionTransportDefect T₀₂ μ₀ μ₂ x y =
      projectiveComparisonPathDefect a T₀₁ T₁₂ T₀₂ (μ₀ x y) +
        (a - a ^ 2) • μ₂ (T₀₂ x) (T₀₂ y) -
        a • μ₂ (projectiveComparisonPathDefect a T₀₁ T₁₂ T₀₂ x) (T₀₂ y) -
        a • μ₂ (T₀₂ x) (projectiveComparisonPathDefect a T₀₁ T₁₂ T₀₂ y) -
        μ₂ (projectiveComparisonPathDefect a T₀₁ T₁₂ T₀₂ x)
          (projectiveComparisonPathDefect a T₀₁ T₁₂ T₀₂ y) :=
  compositionTransportDefect_projective_triangle_bianchi
    a μ₀ μ₁ μ₂ T₀₁ T₁₂ T₀₂ x y

/-- Four split formations obey the Bianchi coherence law for ternary interference. -/
theorem noetherSecond_formationInterferenceBianchi
    {R X Z : Type*} [CommRing R] [AddCommGroup X] [Module R X]
    [AddCommGroup Z] [Module R Z]
    (Fi Fj Fk Fl : SplitLinearFormation R X Z) :
    (compressedComparison Fk Fl).comp (ternaryInterference Fi Fj Fk) +
        ternaryInterference Fi Fk Fl =
      ternaryInterference Fi Fj Fl +
        (ternaryInterference Fj Fk Fl).comp (compressedComparison Fi Fj) :=
  ternaryInterference_bianchi Fi Fj Fk Fl

/-- Reflection duality forces cancellation of the coarse holonomy defect. -/
theorem noetherSecond_halfCharacterDualityBianchi (u : ℂˣ) :
    coarseHolonomyDefect (halfCharacterCoarse u) +
        halfCharacterCoarse u * coarseHolonomyDefect (halfCharacterCoarse u)⁻¹ = 0 :=
  coarseHolonomyDefect_duality_bianchi u

/-! ## Premise-free conserved quantities -/

/-- Time-translation Noether law for the free Klein--Gordon field. -/
theorem noetherFirst_freeKleinGordonEnergy
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldGrad (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
          Lp ℂ 2 (volume : Measure E)) g h t‖ ^ 2 +
        ‖kgFieldVel (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
          Lp ℂ 2 (volume : Measure E)) g h t‖ ^ 2 =
      ‖g‖ ^ 2 + ‖h‖ ^ 2 := by
  simpa using kgFieldEnergy_conserved
    (W := (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
      Lp ℂ 2 (volume : Measure E))) (b := 0)
    (le_refl 0) (by simp) (by intro x y; simp) g h t

/-- A unitary evolution conserves the complete nonstatic memory norm. -/
theorem noetherFirst_unitaryMemoryNorm
    {k E : Type*} [RCLike k] [NormedAddCommGroup E]
    [InnerProductSpace k E] [CompleteSpace E]
    (U : E ≃ₗᵢ[k] E) (x : E) :
    ‖dynamicMemory (0 : E →L[k] E) U x‖ ^ 2 = ‖x‖ ^ 2 := by
  have h := twoMemory_norm_conservation
    (0 : E →L[k] E) (0 : E →L[k] E) U x
    (by simp [IsSelfAdjoint]) (by simp) (by simp) (by simp)
  simpa [staticMemory] using h

/-- Unit-slope Gamma--Meixner phase rotation conserves normalized two-channel charge. -/
theorem noetherFirst_unitGammaMeixnerCharge (a : ℝ) :
    Complex.normSq
          (gammaMeixnerNormalizedSymmetricChargeAt 1 one_ne_zero a 1) +
        Complex.normSq
          (gammaMeixnerNormalizedChiralChargeAt 1 one_ne_zero a 1) = 1 := by
  simpa using gammaMeixnerNormalizedCharge_normSq_add_eq_one
    1 one_ne_zero a 1 one_ne_zero

/-- The same phase-charge conservation is isometric on every finite source packet. -/
theorem noetherFirst_unitGammaMeixnerPacket
    {d : ℕ} (weight : Fin d → ℂ) (a : ℝ) :
    ∑ i, (Complex.normSq
            (weight i * gammaMeixnerNormalizedSymmetricChargeAt 1 one_ne_zero a 1) +
          Complex.normSq
            (weight i * gammaMeixnerNormalizedChiralChargeAt 1 one_ne_zero a 1)) =
      ∑ i, Complex.normSq (weight i) := by
  simpa using finiteGammaMeixnerNormalizedCharge_isometry
    (fun _ : Fin d => (1 : ℂ)) (fun _ => one_ne_zero) weight a 1 one_ne_zero

/-- Time-translation eigenmodes conserve their factorially normalized derivative energy as an
exact Poisson order packet. -/
theorem noetherFirst_coherentJetPoisson
    (c b : ℂ) (x : ℝ) (r : ℕ) :
    x ^ r / r.factorial * ‖coherentExponentialJet c b x r‖ ^ 2 =
      ‖c‖ ^ 2 * Real.exp (cayleyFockExponent b * x) *
        poissonOrderWeight (cayleyFockDrift b * x) r :=
  coherentExponentialJet_poisson_conservation c b x r

/-- Transported residues inherit the coherent-flow Poisson conservation law. -/
theorem noetherFirst_cayleyResiduePoisson
    (m c rho : ℂ) (x : ℝ) (r : ℕ) :
    x ^ r / r.factorial *
        ‖iteratedDeriv r (cayleyPoleResidueMode m c rho) (x : ℂ)‖ ^ 2 =
      ‖m‖ ^ 2 * Real.exp (cayleyFockExponent ((rho - c)⁻¹) * x) *
        poissonOrderWeight (cayleyFockDrift ((rho - c)⁻¹) * x) r :=
  cayleyPoleResidueMode_poisson_conservation m c rho x r

/-- Observer-current continuity: source KL chirality splits into visible and fibre currents. -/
theorem noetherFirst_observerChiralityCurrent
    {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (P R : Measure Ω) (q : Ω → Y) :
    klChirality P R = klChirality (P.map q) (R.map q) +
      observerFibreChirality P R q :=
  klChirality_observer_conservation P R q

/-- Finite observer towers telescope source chirality into terminal chirality and stage currents. -/
theorem noetherFirst_observerTowerChirality
    (visibleChirality : ℕ → ℝ) (n : ℕ) :
    visibleChirality 0 = visibleChirality n +
      ∑ i ∈ Finset.range n, observerTowerCurrent visibleChirality i :=
  observerTower_chirality_conservation visibleChirality n

/-- Rank conservation for observer-created overlap and ternary formation charge. -/
theorem noetherFirst_observerOverlapRank
    {K V Y : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup Y] [Module K Y] [FiniteDimensional K V] [FiniteDimensional K Y]
    (L : V →ₗ[K] Y) (W Z : Submodule K V) :
    Module.finrank K (FormationCharge (LinearMap.ker L) W Z) +
        Module.finrank K ↥((W ⊓ Z).map L) =
      Module.finrank K ↥(W.map L ⊓ Z.map L) :=
  observerOverlap_finrank_conservation L W Z

/-- Mean-normalized formation response is conserved at every positive successor depth. -/
theorem noetherFirst_meanNormalizedFormation
    (k : ℕ) (B : MultilinearMap ℝ (fun _ : HadamardCumulantIndex k => ℝ) ℝ)
    (a : ℝ) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) ^ (k + 2) *
        hadamardTensorDepthCurrent k B (a / ((n + 1 : ℕ) : ℝ)) (n + 1) =
      hadamardTensorResponse k B a :=
  hadamardTensor_meanNormalized_conservation k B a (n + 1) (Nat.succ_ne_zero n)

/-- Variance-normalized formation response is conserved at every positive successor depth. -/
theorem noetherFirst_varianceNormalizedFormation
    (k : ℕ) (B : MultilinearMap ℝ (fun _ : HadamardCumulantIndex k => ℝ) ℝ)
    (a : ℝ) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) ^ (k + 1) *
        hadamardTensorDepthCurrent k B (a / ((n + 1 : ℕ) : ℝ)) ((n + 1) ^ 2) =
      hadamardTensorResponse k B a :=
  hadamardTensor_varianceNormalized_conservation k B a (n + 1) (Nat.succ_ne_zero n)

/-- Every linear intervention splits exactly into longitudinal response and mixing current. -/
theorem noetherFirst_longitudinalIntervention
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (c : X →L[ℂ] ℂ) (e : ℂ →L[ℂ] X) (T : X →L[ℂ] X) (x : X) :
    c (T x) = longitudinalMixingDefect c e T x + c (T (e (c x))) :=
  longitudinal_intervention_conservation c e T x

/-- Discrete summation by parts conserves depth-weighted formation as bulk deficit plus flux. -/
theorem noetherFirst_successiveFormationFlux (a : ℕ → ℂ) (N : ℕ) :
    ∑ j ∈ Finset.range (N + 1), (j : ℂ) * successiveFormation a j =
      ∑ j ∈ Finset.range N, (1 - a j) + (N : ℂ) * (a N - 1) :=
  weighted_successiveFormation_conservation a N

/-- Midpoint dissipation of a fused reporter is the sum of its three component currents. -/
theorem noetherFirst_tripleReporterDissipation
    {E F₁ F₂ F₃ : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
    (R₁ : E →L[ℝ] F₁) (R₂ : E →L[ℝ] F₂) (R₃ : E →L[ℝ] F₃)
    (W₁ : F₁ → ℝ) (W₂ : F₂ → ℝ) (W₃ : F₃ → ℝ) (a b : E) :
    midpointDissipation (tripleFusionEnergy R₁ R₂ R₃ W₁ W₂ W₃) a b =
      midpointDissipation W₁ (R₁ a) (R₁ b) +
        midpointDissipation W₂ (R₂ a) (R₂ b) +
        midpointDissipation W₃ (R₃ a) (R₃ b) :=
  tripleFusion_midpointDissipation_conservation R₁ R₂ R₃ W₁ W₂ W₃ a b

/-- Genuine and splice sectors conserve total envelope defect plus interference. -/
theorem noetherFirst_genuineSpliceInterference
    (genuine splice : ℂ) (genuineEnvelope spliceEnvelope : ℝ) :
    genuineEnvelope + spliceEnvelope - ‖genuine + splice‖ =
      (genuineEnvelope - ‖genuine‖) + (spliceEnvelope - ‖splice‖) +
        (‖genuine‖ + ‖splice‖ - ‖genuine + splice‖) :=
  genuineSpliceInterference_conservation genuine splice genuineEnvelope spliceEnvelope

/-- Positive observer response splits into coherent stiffness and phase-loss current. -/
theorem noetherFirst_responseStiffness
    {Y Z : Type*} [Fintype Y] (S : FinitePositiveKernel Y Z) (c : Y → ℂ) (z : Z) :
    S.applyReal (fun y => ‖c y‖) z =
      ‖S.applyComplex c z‖ + positiveObserverLoss S c z :=
  responseStiffness_conservation S c z

/-- Gauge-jet escape and inverse incidence blow-up differ by one at every cyclic scale. -/
theorem noetherFirst_cyclicGaugeAttainment (n : ℕ) :
    ‖GaloisForLFunctions.regularizedPeriodWeight (cyclicWallPeriod n)‖⁻¹ =
      1 + ‖iteratedDeriv 1 (cyclicWallGauge n) 0‖ / (2 * Real.pi) :=
  cyclicWall_gaugeAttainment_conservation n

/-- Closed Jordan formation example: unit head charge migrates to a new primitive. -/
theorem noetherFirst_jordanUnitHead :
    jordanFormationHeadTwo jordanFormationOldHorizon = 1 ∧
      jordanFormationHeadThree (jordanFormationEmbed jordanFormationOldHorizon) = 0 ∧
      jordanFormationHeadThree jordanFormationNewPrimitive = 1 :=
  jordanFormation_unit_head_conservation

/-- Closed obstruction: pairing an insensitive reporter with a delayed-exchange reporter cannot
restore conservation-compatible strict promotion. -/
theorem noetherObstruction_delayedExchangeReporter :
    ¬ ReporterStrictExchangePromotionExists delayedExchangeLeft delayedExchangeRight
      (pairedReporter (unitReporter : DelayedExchangeState → Unit) delayedExchangeReporter) :=
  delayedExchange_unitPair_conservation_veto

/-- A unitary change of target coordinates preserves the Gram charge of every linear law. -/
theorem noetherFirst_gramOperatorUnitaryInvariant
    {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ V] [InnerProductSpace ℂ W]
    [CompleteSpace V] [CompleteSpace W]
    (U : W ≃ₗᵢ[ℂ] W) (A : V →L[ℂ] W) :
    gramOperator ((U : W →L[ℂ] W).comp A) = gramOperator A :=
  gramOperator_leftUnitary_invariant U A

/-- Integral period action conserves excess plus isotropy under source-basis symmetry. -/
theorem noetherFirst_periodActionSourceBasisInvariant
    {N : ℕ} {V : Type*} [AddCommGroup V]
    (p : IntegralPeriodSource N →+ V)
    (e : IntegralPeriodSource N ≃+ IntegralPeriodSource N) (d : ℕ) :
    integralPeriodExcess (p.comp e.toAddMonoidHom) d +
        integralPeriodKernelRank (p.comp e.toAddMonoidHom) =
      integralPeriodExcess p d + integralPeriodKernelRank p :=
  periodActionConservation_sourceBasisInvariant p e d

/-- Integral period action conserves excess plus isotropy under target-coordinate symmetry. -/
theorem noetherFirst_periodActionTargetCoordinatesInvariant
    {N : ℕ} {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module ℝ V] [Module ℝ W]
    (p : IntegralPeriodSource N →+ V) (e : V ≃ₗ[ℝ] W) (d : ℕ) :
    integralPeriodExcess (e.toAddEquiv.toAddMonoidHom.comp p) d +
        integralPeriodKernelRank (e.toAddEquiv.toAddMonoidHom.comp p) =
      integralPeriodExcess p d + integralPeriodKernelRank p :=
  periodActionConservation_targetCoordinatesInvariant p e d

/-- On the flat Hessian, the crossing tensor is invariant under every unitary gauge jet. -/
theorem noetherFirst_flatCrossingFormGaugeInvariant
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (U : E ≃ₗᵢ[𝕜] E)
    (Hdot K : Module.End 𝕜 E) (x y : E) :
    _root_.HTGeometry.NomologicalHomotopyGeometry.GaugeSpectralFlow.crossingForm
        (_root_.HTGeometry.NomologicalHomotopyGeometry.GaugeSpectralFlow.gaugeDerivative
          U 0 Hdot K) (U x) (U y) =
      _root_.HTGeometry.NomologicalHomotopyGeometry.GaugeSpectralFlow.crossingForm Hdot x y := by
  apply _root_.HTGeometry.NomologicalHomotopyGeometry.GaugeSpectralFlow.crossingForm_gauge_invariant
  · intro a b
    simp
  · simp
  · simp

/-! ## Algebraic Noether applications -/

/-- Noether normalization supplies a finite transcendence-dimension witness for every finite-type
algebra over a field. -/
theorem noetherNormalization_finiteTypeDimension
    (k R : Type*) [Field k] [CommRing R] [Nontrivial R]
    [Algebra k R] [Algebra.FiniteType k R] :
    ∃ s : ℕ, ringKrullDim R = (s : WithBot ℕ∞) :=
  exists_ringKrullDim_eq_of_finiteType k R

/-- Every finite-coordinate complex affine algebraic descending chain terminates. -/
theorem noetherian_complexAffineDescent {σ : Type*} [Finite σ] :
    WellFounded (fun T S : {Z : Set (σ → ℂ) // IsComplexAffineAlgebraicSet Z} =>
      T.1 ⊂ S.1) :=
  wellFounded_ssubset_complexAffineAlgebraicSet

/-- Iterated finite-variable hypersurface quotients remain Noetherian. -/
theorem noetherian_iteratedBlockHypersurface
    {σ : Type} [Finite σ] (Ps : List (MvPolynomial σ ℂ)) :
    IsNoetherianRing (iteratedBlockHypersurfaceRing Ps) :=
  iteratedBlockHypersurfaceRing_isNoetherian Ps

/-- Unit-coefficient block quotients preserve Noetherianity over any Noetherian base. -/
theorem noetherian_iteratedUnitCoefficientBlock
    {A : Type} [CommRing A] [IsNoetherianRing A] {n : ℕ}
    (Ps : List (MvPolynomial (Fin n) A)) :
    IsNoetherianRing (iteratedUnitCoefficientBlockRing A Ps) :=
  iteratedUnitCoefficientBlockRing_isNoetherian Ps

/-- Every lattice in a finite power of the differential-operator ring is finitely generated. -/
theorem noetherian_differentialOperatorLattice
    {K : Type*} [Field K] [Differential K] {ι : Type*} [Finite ι]
    (N : Submodule (DiffOp K) (ι → DiffOp K)) : N.FG :=
  DiffOp.fg_submodule N

/-- Every projective active-block coordinate ring in the corpus is Noetherian. -/
theorem noetherian_projectiveActiveBlock
    {row κ : Type} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → Fin n →₀ ℕ)
    (p : Ideal (MvPolynomial (projectiveChartVar j) ℂ)) [p.IsPrime] :
    IsNoetherianRing (projectiveChartActiveBlockRing q n z j exponent p) :=
  projectiveChartActiveBlockRing_isNoetherian q n z j exponent p

end GaloisForLFunctions.HTGeometry
