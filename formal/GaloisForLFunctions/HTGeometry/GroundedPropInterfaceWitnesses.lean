import GaloisForLFunctions.HTGeometry.ConstitutiveFinitaryFormation
import GaloisForLFunctions.HTGeometry.EllipticGammaConeDivisor
import GaloisForLFunctions.HTGeometry.CompletionKernelPairTransversalityLaw
import GaloisForLFunctions.HTGeometry.PlaceGrading
import GaloisForLFunctions.HTGeometry.HalfPlaneFlatFilter
import GaloisForLFunctions.HTGeometry.VerticalAlmostPeriodicDerivative
import GaloisForLFunctions.HTGeometry.GermNegligible
import GaloisForLFunctions.HTGeometry.HalfPlaneGermRing
import GaloisForLFunctions.HTGeometry.PolynomialShiftHT
import GaloisForLFunctions.HTGeometry.ConstitutiveDoctrineMemorySpectrum
import GaloisForLFunctions.HTGeometry.FormationScaleReceiver
import GaloisForLFunctions.HTGeometry.ExponentialPieceFourierDecay
import GaloisForLFunctions.HTGeometry.ConstitutiveFailureKernelTransversal
import GaloisForLFunctions.HTGeometry.ConstitutiveBipolarObserverRepair
import GaloisForLFunctions.HTGeometry.CofinalGenerativeAdmission
import GaloisForLFunctions.HTGeometry.ConstitutiveCoefficientLiftTransgression
import GaloisForLFunctions.HTGeometry.ConstitutivePrimitiveExecutionGenesis
import GaloisForLFunctions.HTGeometry.NormingFaceFusion
import GaloisForLFunctions.HTGeometry.BeurlingCrossSystemBlindness
import GaloisForLFunctions.HTGeometry.RankThreeMinorWitnesses
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaPeriodRankDichotomy
import GaloisForLFunctions.HTGeometry.InterfinityGeometry.CoherentSourceFunctor
import GaloisForLFunctions.HTGeometry.ClockChangeTriangular
import GaloisForLFunctions.HTGeometry.QDigammaHypertranscendental
import GaloisForLFunctions.HTGeometry.GammaPoleReciprocalBellGrading
import GaloisForLFunctions.HTGeometry.ThermalAnalyticAlgebraicFacetKernelUniversalityLaw
import GaloisForLFunctions.HTGeometry.NevanlinnaNoncriticalProjectiveCompactPatch
import GaloisForLFunctions.HTGeometry.PairwiseFirstCoalescenceLaw
import GaloisForLFunctions.HTGeometry.StretchedExponentialConvexConfinement
import GaloisForLFunctions.HTGeometry.FlatVolterraDecay

/-!
# Ground witnesses for proposition interfaces

Canonical identity, zero, empty-family, and exact rank-three models make a broad family of
proposition-valued interfaces directly inhabitable.  These laws separate genuinely obstructive
interfaces from predicates whose first witnesses were merely hidden behind downstream theorems.
-/

open Filter Topology IsDedekindDomain MeasureTheory
open scoped ENNReal OnePoint

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Algebraic and set-theoretic interfaces -/

/-- Identity formation is finitary, with the consequence itself as singleton support. -/
theorem isFinitaryFormation_id {α : Type*} [DecidableEq α] :
    IsFinitaryFormation (id : Set α → Set α) := by
  intro A x hx
  exact ⟨{x}, by simpa using hx, by simpa using hx⟩

/-- Zero belongs to every integral period group. -/
theorem periodGroupMem_zero (a b : ℂ) : PeriodGroupMem a b 0 := by
  exact ⟨0, 0, 0, by simp⟩

/-- Every observation identifies a point with itself. -/
theorem mapKernelPair_refl {X Y : Type*} (f : X → Y) (x : X) :
    MapKernelPair f x x :=
  rfl

/-- A constant target factors exactly through the attained range of every observation. -/
theorem factorsThroughRange_const
    {X Q C : Type*} (π : X → Q) (c : C) :
    FactorsThroughRange π (fun _ => c) := by
  exact ⟨fun _ => c, fun _ => rfl⟩

/-- The multiplicative unit is free at every place. -/
theorem placeFree_one
    {R K : Type*} [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) :
    PlaceFree v (1 : K) := by
  simp [PlaceFree]

/-- Zero has either reflection parity. -/
theorem reflectionParity_zero
    {X R : Type*} [AddGroup R] (odd : Bool) (σ : X → X) :
    ReflectionParity odd σ (fun _ => 0) := by
  intro x
  cases odd <;> simp

/-- Constant tuple at its centre lies in the sharp zero-width window. -/
theorem tupleInWindow_const (q : ℕ) {D : ℕ} :
    tupleInWindow q 0 (fun _ : Fin D => q) := by
  simp [tupleInWindow]

/-- One zero coordinate is a boundary offset candidate in the zero-radius window. -/
theorem boundaryOffsetCandidate_zero :
    boundaryOffsetCandidate (D := 1) (L := 0)
      (fun _ => 0) (fun _ => 0) := by
  simp [boundaryOffsetCandidate]

/-! ## Analytic zero laws -/

/-- Zero is flat to every polynomial order on every upper half-plane. -/
theorem isFlatOn_zero (σ₀ : ℝ) :
    GaloisForLFunctions.IsFlatOn σ₀ (fun _ => 0) := by
  intro N
  simpa using (tendsto_const_nhds :
    Tendsto (fun _ : ℂ => (0 : ℝ))
      (GaloisForLFunctions.halfPlaneUpper σ₀) (nhds 0))

/-- Zero is uniformly almost periodic on every closed vertical strip. -/
theorem isStripAlmostPeriodicOn_zero (σ r : ℝ) :
    GaloisForLFunctions.IsStripAlmostPeriodicOn (fun _ : ℂ => (0 : ℂ)) σ r := by
  intro ε hε
  refine ⟨1, zero_lt_one, fun a => ⟨a, ?_, ?_⟩⟩
  · exact ⟨le_rfl, le_add_of_nonneg_right zero_le_one⟩
  · intro z hz
    simpa using hε.le

/-- Zero represents a negligible upper-end germ. -/
theorem isGermNegligible_zero :
    IsGermNegligible ((fun _ : ℂ => 0 : ℂ → ℂ) : Germ upperEndFilter ℂ) := by
  exact isGermNegligible_coe.mpr isVerticallyNegligible_zero

/-- Zero represents a flat half-plane germ. -/
theorem isFlatGerm_zero (σ₀ : ℝ) :
    GaloisForLFunctions.IsFlatGerm σ₀
      ((fun _ : ℂ => 0 : ℂ → ℂ) : GaloisForLFunctions.HalfPlaneGerm σ₀) := by
  change GaloisForLFunctions.IsFlatOn σ₀ (fun _ : ℂ => 0)
  exact isFlatOn_zero σ₀

/-- Zero is a polynomial formal power series. -/
theorem isPolySeries_zero : IsPolySeries (0 : PowerSeries ℂ) := by
  exact ⟨0, by simp⟩

/-! ## Finite-memory and Fourier interfaces -/

/-- Zero obeys the nonzero constant recurrence with polynomial `1`. -/
theorem seqConstantRecurrence_zero : SeqConstantRecurrence (fun _ => 0) := by
  refine ⟨1, one_ne_zero, ?_⟩
  intro n
  simp

/-- Consequently, the zero response has uniformly bounded Hankel rank. -/
theorem bddHankelRank_zero : BddHankelRank (fun _ => 0) :=
  bddHankelRank_of_seqConstantRecurrence seqConstantRecurrence_zero

/-- Zero satisfies a nonzero constant-coefficient differential equation near the origin. -/
theorem germConstantODE_zero : GermConstantODE (fun _ => 0) := by
  refine ⟨1, one_ne_zero, Filter.Eventually.of_forall ?_⟩
  intro z
  simp

/-- Zero is locally the zero exponential polynomial. -/
theorem germExpPoly_zero : GermExpPoly (fun _ => 0) := by
  exact ⟨0, Submodule.zero_mem _, Filter.Eventually.of_forall fun _ => rfl⟩

/-- Zero is Wiener summable at every exponential scale. -/
theorem formationWienerSummable_zero (ρ : ℝ) :
    FormationWienerSummable ρ (fun _ => 0) := by
  simp [FormationWienerSummable]

/-- The zero circle function has Fourier decay with sharp constant zero. -/
theorem hasFourierDecay_zero :
    GaloisForLFunctions.HasFourierDecay (fun _ => 0) 0 := by
  intro j
  simp [fourierCoeff]

/-! ## Empty-family and zero-cochain interfaces -/

/-- Every removal hits every member of the empty failure family. -/
theorem hitsFailureFamily_empty
    {α : Type*} [DecidableEq α] (R : Finset α) :
    HitsFailureFamily R ∅ := by
  intro K hK
  simp at hK

/-- Empty unary words are admitted by every law dictionary. -/
theorem unaryLawWordAdmitted_nil
    {α : Type*} (F : Set (α → α)) :
    UnaryLawWordAdmitted F [] := by
  simp [UnaryLawWordAdmitted]

/-- Zero base and tangent are admitted at the unit scale. -/
theorem admittedAt_zero {ι : Type*} :
    AdmittedAt (fun _ : ι => 0) (fun _ => 0) 1 := by
  simp [AdmittedAt]

/-- Zero tangent is dominated by zero copies of the zero base. -/
theorem dominatedAt_zero {ι : Type*} :
    DominatedAt (fun _ : ι => 0) (fun _ => 0) 0 := by
  simp [DominatedAt]

/-- Zero compensator is a promotion cocycle. -/
theorem isPromotionCocycle_zero
    {M A : Type*} [Add M] [AddGroup A] :
    IsPromotionCocycle (fun _ _ : M => (0 : A)) := by
  simp [IsPromotionCocycle, PromotionAssociator]

/-- Every additive observer maps the zero compensator to the zero compensator. -/
theorem isCompensatorLift_zero
    {M A B : Type*} [AddGroup A] [AddGroup B] (q : A →+ B) :
    IsCompensatorLift q (fun _ _ : M => (0 : A)) (fun _ _ => (0 : B)) := by
  simp [IsCompensatorLift]

/-- Grade two with zero resources splits over an empty failure family. -/
theorem weightedDominatedSplit_empty_two_zero
    {α : Type*} [DecidableEq α] :
    WeightedDominatedSplit (∅ : Finset (Finset α)) 2 (fun _ => 0) := by
  refine ⟨1, 1, (fun _ => 0), (fun _ => 0), by simp [WeightedLocalRepair]⟩

/-- Zero polynomial annihilates every q-digamma jet packet. -/
theorem annihilatesQDigamma_zero (q : RealEulerNome) (m : ℕ) :
    AnnihilatesQDigamma q m 0 := by
  intro z hz
  simp [qPolyJetEval]

/-- Zero is differentially algebraic for every derivation over every nontrivial ambient algebra. -/
theorem isDifferentiallyAlgebraicOver_zero
    {R A : Type*} [CommRing R] [CommRing A] [Nontrivial A] [Algebra R A]
    (K : Subalgebra R A) (δ : Derivation R A A) :
    IsDifferentiallyAlgebraicOver K δ 0 := by
  refine ⟨0, MvPolynomial.X 0, MvPolynomial.X_ne_zero 0, ?_⟩
  simp

/-- A constant weak-star family converges to its own value along every filter. -/
theorem tendstoWeakStar_const
    {ι Φ : Type*} [AddCommGroup Φ] [Module ℂ Φ]
    (l : Filter ι) (L : Φ →ₗ[ℂ] ℂ) :
    Interfinity.TendstoWeakStar (fun _ => L) l L := by
  intro f
  exact tendsto_const_nhds

/-- Zero cochain is a stable primitive for every source semigroup. -/
theorem isStablePrimitive_zero
    {Φ : Type*} [AddCommGroup Φ] [Module ℂ Φ]
    (S : NNReal → (Φ →ₗ[ℂ] Φ)) :
    Interfinity.IsStablePrimitive S (fun _ => 0) 0 := by
  constructor
  · intro V f
    simp
  · intro f
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : NNReal => (0 : ℂ)) atTop (nhds 0))

/-- Constant coherent functionals have a coherent boundary equal to themselves. -/
theorem hasCoherentBoundary_const
    {Φ : Type*} [AddCommGroup Φ] [Module ℂ Φ]
    (L : Φ →ₗ[ℂ] ℂ) :
    Interfinity.HasCoherentBoundary (fun _ => L) L :=
  Interfinity.hasCoherentBoundary_of_tendstoWeakStar
    (tendstoWeakStar_const atTop L)

/-- A homogeneous Boolean transport collapsing every input first coalesces `true,false` at edge 0. -/
theorem pairFirstCoalescesAt_bool_zero :
    PairFirstCoalescesAt (X := fun _ => Bool)
      (fun _ (_ : Bool) => false) true false 0 := by
  simp [PairFirstCoalescesAt, iteratedObservationTransport, MapKernelPair]

/-! ## Calibration, asymptotic, and rank-three interfaces -/

/-- Zero sequence beats every polynomial rate with exact envelope zero. -/
theorem superpolynomiallyFlat_zero :
    SuperpolynomiallyFlat (fun _ : ℕ => (0 : ℝ)) := by
  intro N
  refine ⟨0, ?_⟩
  intro n hn
  simp

/-- Zero functional calibrates every vector family on the empty index set. -/
theorem isCommonCalibratorOn_empty
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (v : ι → V) :
    IsCommonCalibratorOn (∅ : Finset ι) v (0 : StrongDual ℝ V) := by
  simp [IsCommonCalibratorOn]

/-- `log` itself is Mertens-normal with exact constant zero. -/
theorem mertensNormal_log : Beurling.MertensNormal Real.log 0 := by
  simpa [Beurling.MertensNormal] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (nhds 0))

/-- The concrete period pair `i, i√2` is a rank-three obstruction edge. -/
theorem multipleEllipticGammaRankThreeEdge_I_sqrtTwo :
    MultipleEllipticGammaRankThreeEdge
      (![Complex.I, Complex.I * (Real.sqrt 2 : ℂ)] : Fin 2 → ℂ) 0 1 := by
  exact ⟨by decide,
    GaloisForLFunctions.linearIndependent_ellipticGammaSourcePeriods_I_I_sqrtTwo⟩

/-- The full two-point section contains the concrete rank-three edge. -/
theorem multipleEllipticGammaFiniteSectionContainsRankThreeEdge_I_sqrtTwo :
    MultipleEllipticGammaFiniteSectionContainsRankThreeEdge
      (![Complex.I, Complex.I * (Real.sqrt 2 : ℂ)] : Fin 2 → ℂ) Finset.univ := by
  refine ⟨⟨0, Finset.mem_univ _⟩, ⟨1, Finset.mem_univ _⟩, ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp at this
  · simpa [multipleEllipticGammaFiniteSubfamily] using
      GaloisForLFunctions.linearIndependent_ellipticGammaSourcePeriods_I_I_sqrtTwo

/-! ## Universal zero kernels -/

/-- Zero source and zero polynomial lie in every simultaneous thermal analytic--algebraic kernel. -/
theorem thermalAnalyticAlgebraicFacetKernel_zero
    {J R α S : Type*} [Fintype J] [CommRing R] [CommRing S] [DecidableEq α]
    [Algebra (MvPolynomial α R) S]
    (facets : Finset (Finset α)) (c : J → facets → ℂ)
    (base energy : facets → ℝ) (level : ℝ) :
    thermalAnalyticAlgebraicFacetKernel (R := R) (S := S)
      facets c base energy level (fun _ => 0) 0 := by
  constructor
  · simp [HTGeometry.finiteSourceSuperlevelGramEnergy]
  · exact Submodule.zero_mem _

/-- Zero Gamma-jet polynomial obeys every native affine pole cutoff. -/
theorem gammaAffineJetTowerPoleCutoff_zero (n r : ℕ) :
    GammaAffineJetTowerPoleCutoff n r
      (0 : MvPolynomial (Fin (n + 2)) ℂ) := by
  rw [gammaAffineJetTowerPoleCutoff_iff_reciprocalBellNativePoleDegree]
  simp [reciprocalBellNativePoleDegree, reciprocalBellBihomogeneousSupport,
    reciprocalBellBihomogeneousComponent]

/-- Empty row and coefficient types give a vacuous but exact expanded full-rank model. -/
theorem actualNevanlinnaExpandedFullRankWitness_empty
    {ι : Type} [Fintype ι]
    (m0 a q : ℂ → ℂ) (degree : ℕ) (orders : ι → ℕ)
    (exponent : Empty → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu]
    (baseDensity : Lp ℝ (⊤ : ENNReal) mu)
    (S : Submodule ℝ (Lp ℝ (⊤ : ENNReal) mu))
    (w : S) (shift : InjectiveShiftConfiguration ι) :
    actualNevanlinnaExpandedFullRankWitness (row := Empty) (κ := Empty)
      m0 a q degree orders exponent mu baseDensity S w shift := by
  let packet : InjectiveProjectiveRowPacket Empty :=
    ⟨fun x => x.elim, fun x => x.elim⟩
  refine ⟨packet, ?_, ?_⟩
  · intro x
    exact x.1.elim
  · intro u v huv
    funext x
    exact x.1.elim

end

end GaloisForLFunctions.HTGeometry
