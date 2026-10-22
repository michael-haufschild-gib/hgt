import GaloisForLFunctions.HTGeometry.HarmonicLogEquidistribution
import GaloisForLFunctions.HTGeometry.PrimePoissonProductState
import GaloisForLFunctions.HTGeometry.FiniteSpectralHaarRecurrenceLaw
import GaloisForLFunctions.HTGeometry.CompletedObserverTimeTorus
import GaloisForLFunctions.HTGeometry.ResolvedRecurrenceRelationCompletenessLaw
import GaloisForLFunctions.HTGeometry.SummableCircleFourierDensity
import GaloisForLFunctions.HTGeometry.RadialPoissonMixture
import GaloisForLFunctions.HTGeometry.CirclePoissonProductEquivalence
import GaloisForLFunctions.HTGeometry.UniversalClockSamplingPhaseLaw
import GaloisForLFunctions.HTGeometry.PrimePoissonSuperselectionScreen
import GaloisForLFunctions.HTGeometry.CharacteristicEquilibriumDefect
import GaloisForLFunctions.HTGeometry.WignerSmithFiniteResolutionLawEscape
import GaloisForLFunctions.HTGeometry.JuliaDefectEquilibriumPositiveDefinite
import GaloisForLFunctions.RHTower.MobiusCriticalClockWeakConvergence
import GaloisForLFunctions.RHTower.GammaMeixnerRootSeamScale
import GaloisForLFunctions.RHTower.SoninSemilocalGammaMoments
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCarlemanFlatPortAsymptotic
import GaloisForLFunctions.RHTower.ConnesHarmonicMeasure
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailConvexCore
import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiPositiveConnectedLogChord
import GaloisForLFunctions.RHTower.CCM.CCMRadialProlateProfileMeasure
import GaloisForLFunctions.RHTower.SoninSemilocalDampedCovariancePositivity
import GaloisForLFunctions.RHTower.XiPoissonHilbertPhaseAmplification
import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszQuadratureDefect
import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszCesaroCurvature
import GaloisForLFunctions.RHTower.PoissonDigammaReproduction
import GaloisForLFunctions.RHTower.Suzuki.SuzukiGammaMollifiedEquation
import GaloisForLFunctions.RHTower.RadialLeakageArcsineMeasure
import GaloisForLFunctions.RHTower.CCM.CCMEndpointFourierJet
import GaloisForLFunctions.HTGeometry.ErlangWignerSmithPacket
import GaloisForLFunctions.HTGeometry.BumpMollifierFamily
import GaloisForLFunctions.HTGeometry.GoldenRuleKernel
import GaloisForLFunctions.HTGeometry.GaussianRadialLaw
import GaloisForLFunctions.HTGeometry.BinomialTailBetaThreshold
import GaloisForLFunctions.HTGeometry.HyperbolicLevyKhintchine
import GaloisForLFunctions.HTGeometry.ShiftedFactorialMomentDensity
import GaloisForLFunctions.RHTower.FermiMellinObserver
import GaloisForLFunctions.RHTower.MassJetSubordinationKernel
import GaloisForLFunctions.RHTower.InfiniteLocalRecurrenceSeparation
import GaloisForLFunctions.RHTower.MobiusIncidenceUniversalGapResponse
import GaloisForLFunctions.RHTower.GammaMixtureConcentration
import GaloisForLFunctions.RHTower.CentredPoleProfile
import GaloisForLFunctions.RHTower.BandLeakageEnvelope
import GaloisForLFunctions.RHTower.SoninScaledProfileSquare
import GaloisForLFunctions.RHTower.SoninScaledMeanBound
import GaloisForLFunctions.RHTower.HermiteLineIntegral
import GaloisForLFunctions.RHTower.BesselEndpointVariation
import GaloisForLFunctions.RHTower.PrimeArchConjugatePairQuadraticConcentration
import GaloisForLFunctions.RHTower.RadialPSWFLeadingTightness
import GaloisForLFunctions.RHTower.FieldOnePositiveLogSchwartzDensity
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadQuantileGammaChiSquareProducer
import GaloisForLFunctions.RHTower.CCM.CCMRawStieltjesChamberIndexInflation
import GaloisForLFunctions.RHTower.ProlateOscProfileLimit
import GaloisForLFunctions.RHTower.SoninMellinWeight
import GaloisForLFunctions.RHTower.XiThetaReaderConditioning
import GaloisForLFunctions.RHTower.SoninAmplitudeFourier
import GaloisForLFunctions.RHTower.ConstrainedProlateEvaluationIdentity
import GaloisForLFunctions.HTGeometry.TorusFejerDisplacement
import GaloisForLFunctions.HTGeometry.RoundingVarianceFloor
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiRealZeroNormBound
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Rajchman transfer laws from critical circle chaos

This module transfers deterministic mechanisms isolated in Cai--Chen--Fang--Guo,
*Critical Gaussian Multiplicative Chaos on the Circle Is Rajchman* (arXiv:2608.28328),
to existing circle and torus measures in the corpus.

The source theorem concerns critical Gaussian multiplicative chaos.  Results below are mechanical
bridges: they identify already-constructed Haar, Poisson, orbit-closure, and spectral-relation
ensembles as Rajchman along their nonresonant directions.  No Gaussian-chaos claim is made.
-/

open Complex Filter MeasureTheory Set Submodule Topology
open scoped BigOperators ComplexConjugate FourierTransform

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance caiChenFangGuoCircleMeasurableSpace : MeasurableSpace Circle :=
  instMeasurableSpaceCircle_galoisForLFunctions

/-- Native-circle Rajchman decay, expressed through positive and conjugate power moments. -/
def IsCircleRajchman (μ : Measure Circle) : Prop :=
  IsFiniteMeasure μ ∧
    Tendsto (fun n : ℕ => ∫ z, (z : ℂ) ^ n ∂μ) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ∫ z, conj ((z : ℂ) ^ (n + 1)) ∂μ) atTop (𝓝 0)

/-- Native normalized circle Haar is Rajchman by exact nonzero-mode cancellation. -/
theorem circleLebesgue_isCircleRajchman : IsCircleRajchman circleLebesgue := by
  refine ⟨inferInstance, ?_, ?_⟩
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [integral_circleLebesgue_coe_pow_eq_zero n]
    omega
  · apply tendsto_const_nhds.congr'
    filter_upwards [] with n
    rw [integral_conj, integral_circleLebesgue_coe_pow_eq_zero (n + 1), map_zero]
    omega

/-- Native circle Poisson laws are Rajchman before transport to the additive circle. -/
theorem circlePoissonMeasure_isCircleRajchman (a : CirclePoissonParameter) :
    IsCircleRajchman (circlePoissonMeasure a) := by
  refine ⟨inferInstance, ?_, ?_⟩
  · simpa only [integral_circlePoissonMeasure_coe_pow] using
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
        (by simpa only [mem_ball_zero_iff] using a.2) :
        Tendsto (fun n : ℕ => (a : ℂ) ^ n) atTop (𝓝 0))
  · have hpow : Tendsto (fun n : ℕ => conj (a : ℂ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one
        (by simpa only [norm_conj, mem_ball_zero_iff] using a.2)
    have hshift := hpow.comp (tendsto_add_atTop_nat 1)
    apply hshift.congr'
    filter_upwards [] with n
    rw [integral_conj, integral_circlePoissonMeasure_coe_pow, map_pow]
    rfl

/-- Summable real Fourier data whose associated symmetric density is nonnegative. -/
def NonnegativeSummableSymmetricCircleDensity :=
  {a : ℕ → ℝ // Summable (fun n : ℕ => |a (n + 1)|) ∧
    ∀ z : Circle, 0 ≤ symmetricCircleFourierDensity a z}

private theorem nonnegativeSummableSymmetricCircleDensity_tendsto_zero
    (a : NonnegativeSummableSymmetricCircleDensity) :
    Tendsto (fun n : ℕ => (a.1 n : ℂ)) atTop (𝓝 0) := by
  have habs : Tendsto (fun n : ℕ => |a.1 (n + 1)|) atTop (𝓝 0) :=
    a.2.1.tendsto_atTop_zero
  have hrealShift : Tendsto (fun n : ℕ => a.1 (n + 1)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Real.norm_eq_abs] using habs
  have hreal : Tendsto (fun n : ℕ => a.1 n) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mp (by simpa only [Nat.add_comm] using hrealShift)
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  apply hc.congr'
  filter_upwards [] with n
  rfl

/-- Every nonnegative symmetric density with absolutely summable nonconstant Fourier data defines
a finite Rajchman circle measure. -/
theorem symmetricCircleFourierDensityMeasure_isCircleRajchman
    (a : NonnegativeSummableSymmetricCircleDensity) :
    IsCircleRajchman (symmetricCircleFourierDensityMeasure a.1) := by
  have hzero := nonnegativeSummableSymmetricCircleDensity_tendsto_zero a
  refine ⟨symmetricCircleFourierDensityMeasure_finite a.2.1, ?_, ?_⟩
  · apply hzero.congr'
    filter_upwards [] with n
    exact (integral_coe_pow_symmetricCircleFourierDensityMeasure a.2.1 a.2.2 n).symm
  · have hshift := hzero.comp (tendsto_add_atTop_nat 1)
    apply hshift.congr'
    filter_upwards [] with n
    rw [integral_conj,
      integral_coe_pow_symmetricCircleFourierDensityMeasure a.2.1 a.2.2 (n + 1),
      Complex.conj_ofReal]
    rfl

/-- Two-sided Fourier decay on the additive unit circle. -/
def IsAddCircleRajchman (μ : Measure UnitAddCircle) : Prop :=
  IsFiniteMeasure μ ∧
    Tendsto (fun n : ℕ => ∫ z, fourier (n : ℤ) z ∂μ) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ∫ z, fourier (Int.negSucc n) z ∂μ) atTop (𝓝 0)

/-- Transport a native circle measure through the canonical circle/additive-circle homeomorphism. -/
def circleMeasureToAddCircle (μ : Measure Circle) : Measure UnitAddCircle :=
  μ.map (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm

/-- Fourier coefficients of the transported measure are exactly native Laurent moments. -/
theorem integral_fourier_circleMeasureToAddCircle (μ : Measure Circle) (q : ℤ) :
    ∫ z, fourier q z ∂circleMeasureToAddCircle μ =
      match q with
      | Int.ofNat n => ∫ z, (z : ℂ) ^ n ∂μ
      | Int.negSucc n => ∫ z, conj ((z : ℂ) ^ (n + 1)) ∂μ := by
  let e : UnitAddCircle ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
  rw [circleMeasureToAddCircle, integral_map e.symm.continuous.aemeasurable
    (fourier q).continuous.aestronglyMeasurable]
  have hfourier (z : Circle) : fourier q (e.symm z) = (z : ℂ) ^ q := by
    rw [fourier_apply, AddCircle.toCircle_zsmul]
    have he : AddCircle.toCircle (e.symm z) = z := by
      rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
      exact e.apply_symm_apply z
    rw [he]
    exact Circle.coe_zpow z q
  simp only [hfourier]
  cases q with
  | ofNat n => simp only [Int.ofNat_eq_natCast, zpow_natCast]
  | negSucc n =>
      apply integral_congr_ae
      filter_upwards [] with z
      rw [zpow_negSucc, ← inv_pow]
      have hz : (z : ℂ)⁻¹ = conj (z : ℂ) := by
        simpa using Circle.coe_inv_eq_conj z
      rw [hz, map_pow]

/-- Rajchman decay is invariant under the canonical circle/additive-circle transport. -/
theorem circleMeasureToAddCircle_isAddCircleRajchman
    (M : {μ : Measure Circle // IsCircleRajchman μ}) :
    IsAddCircleRajchman (circleMeasureToAddCircle M) := by
  letI : IsFiniteMeasure (M : Measure Circle) := M.2.1
  have hfinite : IsFiniteMeasure (circleMeasureToAddCircle M) := by
    unfold circleMeasureToAddCircle
    infer_instance
  refine ⟨hfinite, ?_, ?_⟩
  · apply M.2.2.1.congr'
    filter_upwards [] with n
    exact (integral_fourier_circleMeasureToAddCircle M (n : ℤ)).symm
  · apply M.2.2.2.congr'
    filter_upwards [] with n
    exact (integral_fourier_circleMeasureToAddCircle M (Int.negSucc n)).symm

/-- Normalized circle Haar measure is Rajchman; every nonzero coefficient vanishes exactly. -/
theorem unitCircleHaar_isAddCircleRajchman :
    IsAddCircleRajchman GaloisForLFunctions.unitCircleHaar := by
  refine ⟨inferInstance, ?_, ?_⟩
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [GaloisForLFunctions.integral_fourier_unitCircleHaar, if_neg]
    omega
  · apply tendsto_const_nhds.congr'
    filter_upwards [] with n
    rw [GaloisForLFunctions.integral_fourier_unitCircleHaar, if_neg]
    omega

/-- Every circle Poisson law is Rajchman.  Its disk parameter packages the strict contraction that
forces both positive and negative Fourier powers to vanish. -/
theorem addCirclePoissonProbabilityMeasure_isAddCircleRajchman
    (a : CirclePoissonParameter) :
    IsAddCircleRajchman
      (addCirclePoissonProbabilityMeasure a : Measure UnitAddCircle) := by
  refine ⟨inferInstance, ?_, ?_⟩
  · simpa only [integral_fourier_addCirclePoissonProbabilityMeasure] using
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
        (by simpa only [mem_ball_zero_iff] using a.2) :
        Tendsto (fun n : ℕ => (a : ℂ) ^ n) atTop (𝓝 0))
  · have hpow : Tendsto (fun n : ℕ => conj (a : ℂ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one
        (by simpa only [norm_conj, mem_ball_zero_iff] using a.2)
    simpa only [integral_fourier_addCirclePoissonProbabilityMeasure, pow_succ, zero_mul] using
      hpow.mul_const (conj (a : ℂ))

/-- Coordinatewise two-sided Fourier decay on a product unit torus. -/
def IsInfiniteTorusCoordinateRajchman {I : Type*}
    (μ : Measure (I → UnitAddCircle)) (i : I) : Prop :=
  IsFiniteMeasure μ ∧
    Tendsto (fun n : ℕ =>
      ∫ x, infiniteTorusFourier (Finsupp.single i (n : ℤ)) x ∂μ) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ =>
      ∫ x, infiniteTorusFourier (Finsupp.single i (Int.negSucc n)) x ∂μ) atTop (𝓝 0)

/-- Every coordinate marginal of an arbitrary product Poisson state is Rajchman. -/
theorem torusPoissonMeasure_isInfiniteTorusCoordinateRajchman
    {I : Type*} (a : I → CirclePoissonParameter) (i : I) :
    IsInfiniteTorusCoordinateRajchman (torusPoissonMeasure a) i := by
  classical
  refine ⟨inferInstance, ?_, ?_⟩
  · have hpow : Tendsto (fun n : ℕ => (a i : ℂ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one
        (by simpa only [mem_ball_zero_iff] using (a i).2)
    apply hpow.congr'
    filter_upwards [] with n
    rw [integral_infiniteTorusFourier_torusPoissonMeasure]
    simp [circlePoissonFourierMoment, Finsupp.prod_single_index]
  · have hpow : Tendsto (fun n : ℕ => conj (a i : ℂ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one
        (by simpa only [norm_conj, mem_ball_zero_iff] using (a i).2)
    have hlim : Tendsto (fun n : ℕ => conj (a i : ℂ) ^ n * conj (a i : ℂ))
        atTop (𝓝 0) := by simpa only [zero_mul] using hpow.mul_const (conj (a i : ℂ))
    apply hlim.congr'
    filter_upwards [] with n
    rw [integral_infiniteTorusFourier_torusPoissonMeasure]
    simp [circlePoissonFourierMoment, Finsupp.prod_single_index, pow_succ]

/-- Every local prime phase in the ordinary-prime Poisson spectral law is Rajchman. -/
theorem primePoissonMeasure_isInfiniteTorusCoordinateRajchman
    (σ : {x : ℝ // 0 < x}) (t : ℝ) (p : Nat.Primes) :
    IsInfiniteTorusCoordinateRajchman
      (primePoissonMeasure σ t σ.2) p := by
  exact torusPoissonMeasure_isInfiniteTorusCoordinateRajchman
    (primePoissonParameter σ t σ.2) p

/-- Two-sided cancellation along integer multiples of a finite-torus character. -/
def IsFiniteTorusRayRajchman {d : Type*} [Fintype d]
    (μ : Measure (UnitAddTorus d)) (m : d → ℤ) : Prop :=
  IsFiniteMeasure μ ∧
    Tendsto (fun n : ℕ =>
      ∫ x, UnitAddTorus.mFourier (fun i => (n : ℤ) * m i) x ∂μ) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ =>
      ∫ x, UnitAddTorus.mFourier (fun i => Int.negSucc n * m i) x ∂μ) atTop (𝓝 0)

/-- Finite-torus Haar measure is Rajchman along every nonzero character ray. -/
theorem finiteTorusHaarProbabilityMeasure_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (m : {m : d → ℤ // m ≠ 0}) :
    IsFiniteTorusRayRajchman
      (finiteTorusHaarProbabilityMeasure d : Measure (UnitAddTorus d)) m := by
  classical
  refine ⟨inferInstance, ?_, ?_⟩
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [finiteTorusHaarProbabilityMeasure_mFourier_integral, if_neg]
    intro hzero
    apply m.2
    funext i
    have hi := congrFun hzero i
    simpa using (mul_eq_zero.mp hi).resolve_left (by omega : (n : ℤ) ≠ 0)
  · apply tendsto_const_nhds.congr'
    filter_upwards [] with n
    rw [finiteTorusHaarProbabilityMeasure_mFourier_integral, if_neg]
    intro hzero
    apply m.2
    funext i
    have hi := congrFun hzero i
    simpa using (mul_eq_zero.mp hi).resolve_left (by omega : Int.negSucc n ≠ 0)

/-- Integer scaling is linear for finite spectral detuning. -/
theorem finiteTorusCharacterDetuning_int_mul
    {d : Type*} [Fintype d] (c : ℤ) (m : d → ℤ) (energy : d → ℝ) :
    finiteTorusCharacterDetuning (fun i => c * m i) energy =
      (c : ℝ) * finiteTorusCharacterDetuning m energy := by
  unfold finiteTorusCharacterDetuning
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Integer scaling commutes with the transpose character map of a torus presentation. -/
theorem orbitClosureCharacter_int_mul
    {d k : Type*} [Fintype d] [Fintype k]
    (c : ℤ) (m : d → ℤ) (M : d → k → ℤ) :
    (fun j => ∑ i, (c * m i) * M i j) =
      fun j => c * ∑ i, m i * M i j := by
  funext j
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Character directions transverse to a presented orbit-closure torus. -/
def OrbitClosureTransverseDirection
    {d k : Type*} [Fintype d] [Fintype k] (M : d → k → ℤ) :=
  {m : d → ℤ // (fun j => ∑ i, m i * M i j) ≠ 0}

/-- Haar measure of a completed-time orbit closure is Rajchman on every transverse character ray.
The excluded kernel is exactly its resonance lattice. -/
theorem orbitClosureHaar_isFiniteTorusRayRajchman
    {d k : Type*} [Fintype d] [Fintype k]
    (M : d → k → ℤ) (m : OrbitClosureTransverseDirection M) :
    IsFiniteTorusRayRajchman
      (orbitClosureHaar M : Measure (UnitAddTorus d)) m.1 := by
  classical
  refine ⟨inferInstance, ?_, ?_⟩
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [orbitClosureHaar_mFourier_integral, if_neg]
    intro hzero
    apply m.2
    rw [orbitClosureCharacter_int_mul] at hzero
    funext j
    have hj := congrFun hzero j
    simpa using (mul_eq_zero.mp hj).resolve_left (by omega : (n : ℤ) ≠ 0)
  · apply tendsto_const_nhds.congr'
    filter_upwards [] with n
    rw [orbitClosureHaar_mFourier_integral, if_neg]
    intro hzero
    apply m.2
    rw [orbitClosureCharacter_int_mul] at hzero
    funext j
    have hj := congrFun hzero j
    simpa using (mul_eq_zero.mp hj).resolve_left (by omega : Int.negSucc n ≠ 0)

/-- Nonresonant characters of a finite spectral packet. -/
def NonresonantFiniteTorusCharacter
    {d : Type*} [Fintype d] (energy : d → ℝ) :=
  {m : d → ℤ // finiteTorusCharacterDetuning m energy ≠ 0}

/-- The canonical spectral-relation phase ensemble is Rajchman along every nonresonant ray. -/
theorem spectralRelationPhaseEnsemble_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (spectralRelationPhaseEnsemble energy : Measure (UnitAddTorus d)) m.1 := by
  classical
  refine ⟨inferInstance, ?_, ?_⟩
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [spectralRelationPhaseEnsemble_mFourier_integral,
      spectralRelationIndicator, if_neg]
    rw [mem_spectralRelationLattice_iff]
    rw [finiteTorusCharacterDetuning_int_mul]
    exact mul_ne_zero (by exact_mod_cast (by omega : n ≠ 0)) m.2
  · apply tendsto_const_nhds.congr'
    filter_upwards [] with n
    rw [spectralRelationPhaseEnsemble_mFourier_integral,
      spectralRelationIndicator, if_neg]
    rw [mem_spectralRelationLattice_iff]
    rw [finiteTorusCharacterDetuning_int_mul]
    exact mul_ne_zero (by exact_mod_cast (by omega : Int.negSucc n ≠ 0)) m.2

/-- Complexified sinc along every nonzero natural ray vanishes. -/
theorem tendsto_complex_sinc_nat_mul
    (d : {x : ℝ // x ≠ 0}) :
    Tendsto (fun n : ℕ => (Real.sinc ((n : ℝ) * d) : ℂ)) atTop (𝓝 0) := by
  have harg : Tendsto (fun n : ℕ => (n : ℝ) * |(d : ℝ)|) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const (abs_pos.mpr d.2)
  have hs : Tendsto (fun n : ℕ => Real.sinc ((n : ℝ) * |(d : ℝ)|))
      atTop (𝓝 0) := tendsto_real_sinc_atTop_zero.comp harg
  have hs' : Tendsto (fun n : ℕ => (Real.sinc ((n : ℝ) * |(d : ℝ)|) : ℂ))
      atTop (𝓝 0) := Complex.continuous_ofReal.continuousAt.tendsto.comp hs
  apply hs'.congr'
  filter_upwards [] with n
  by_cases hd : 0 ≤ (d : ℝ)
  · rw [abs_of_nonneg hd]
  · rw [abs_of_nonpos (le_of_not_ge hd), ← Real.sinc_neg]
    congr 2
    ring

/-- A nonzero finite observation window already gives Rajchman decay along every nonresonant
character ray; the coefficient is an explicit sinc rather than an exact zero. -/
theorem finiteTorusPhaseProbabilityMeasure_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (energy : d → ℝ)
    (A : {x : ℝ // x ≠ 0}) (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteTorusPhaseProbabilityMeasure energy A : Measure (UnitAddTorus d)) m.1 := by
  classical
  let δ : {x : ℝ // x ≠ 0} :=
    ⟨(A : ℝ) * finiteTorusCharacterDetuning m.1 energy, mul_ne_zero A.2 m.2⟩
  have hpos := tendsto_complex_sinc_nat_mul δ
  refine ⟨inferInstance, ?_, ?_⟩
  · apply hpos.congr'
    filter_upwards [] with n
    rw [finiteTorusPhaseProbabilityMeasure_mFourier_integral,
      finiteTorusCharacterDetuning_int_mul]
    congr 2
    dsimp only [δ]
    push_cast
    ring
  · have hshift := hpos.comp (tendsto_add_atTop_nat 1)
    apply hshift.congr'
    filter_upwards [] with n
    rw [finiteTorusPhaseProbabilityMeasure_mFourier_integral,
      finiteTorusCharacterDetuning_int_mul]
    apply congrArg Complex.ofReal
    rw [← Real.sinc_neg]
    congr 2
    dsimp only [δ]
    push_cast
    ring

private theorem rajchman_tendsto_fourier_add_nat
    (M : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ}) (j : ℤ) :
    Tendsto (fun n : ℕ => ∫ z, fourier (j + (n : ℤ)) z ∂(M : Measure UnitAddCircle))
      atTop (𝓝 0) := by
  rcases j with k | k
  · have h := M.2.2.1.comp (tendsto_add_atTop_nat k)
    apply h.congr'
    filter_upwards [] with n
    dsimp only [Function.comp_apply]
    have hidx : ((n + k : ℕ) : ℤ) = Int.ofNat k + (n : ℤ) := by
      simp only [Int.ofNat_eq_natCast]
      push_cast
      ring
    rw [hidx]
  · have h := M.2.2.1.comp (tendsto_sub_atTop_nat (k + 1))
    apply h.congr'
    filter_upwards [eventually_ge_atTop (k + 1)] with n hn
    dsimp only [Function.comp_apply]
    have hidx : Int.negSucc k + (n : ℤ) = (n - (k + 1) : ℕ) := by
      rw [Int.natCast_sub hn]
      simp only [Int.negSucc_eq]
      push_cast
      ring
    rw [hidx]

private theorem rajchman_tendsto_fourier_add_negSucc
    (M : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ}) (j : ℤ) :
    Tendsto (fun n : ℕ => ∫ z, fourier (j + Int.negSucc n) z ∂(M : Measure UnitAddCircle))
      atTop (𝓝 0) := by
  rcases j with k | k
  · have h := M.2.2.2.comp (tendsto_sub_atTop_nat k)
    apply h.congr'
    filter_upwards [eventually_ge_atTop k] with n hn
    dsimp only [Function.comp_apply]
    have hidx : Int.ofNat k + Int.negSucc n = Int.negSucc (n - k) := by
      rw [Int.negSucc_eq, Int.negSucc_eq, Int.natCast_sub hn]
      simp only [Int.ofNat_eq_natCast]
      ring
    rw [hidx]
  · have h := M.2.2.2.comp (tendsto_add_atTop_nat (k + 1))
    apply h.congr'
    filter_upwards [] with n
    dsimp only [Function.comp_apply]
    have hidx : Int.negSucc k + Int.negSucc n = Int.negSucc (n + (k + 1)) := by
      simp only [Int.negSucc_eq]
      push_cast
      ring
    rw [hidx]

private theorem continuous_mul_fourier_integrable
    (M : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ})
    (g : C(UnitAddCircle, ℂ)) (j : ℤ) :
    Integrable (fun z => g z * fourier j z) (M : Measure UnitAddCircle) := by
  letI : IsFiniteMeasure (M : Measure UnitAddCircle) := M.2.1
  apply Continuous.integrable_of_hasCompactSupport
  · fun_prop
  · exact HasCompactSupport.of_compactSpace _

private theorem rajchman_tendsto_continuous_weight_pos_span
    (M : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ})
    {g : C(UnitAddCircle, ℂ)} (hg : g ∈ span ℂ (Set.range (@fourier (1 : ℝ)))) :
    Tendsto (fun n : ℕ => ∫ z, g z * fourier (n : ℤ) z ∂(M : Measure UnitAddCircle))
      atTop (𝓝 0) := by
  letI : IsFiniteMeasure (M : Measure UnitAddCircle) := M.2.1
  refine Submodule.span_induction (p := fun g _ => Tendsto
    (fun n : ℕ => ∫ z, g z * fourier (n : ℤ) z ∂(M : Measure UnitAddCircle))
    atTop (𝓝 0)) ?_ ?_ ?_ ?_ hg
  · rintro _ ⟨j, rfl⟩
    apply (rajchman_tendsto_fourier_add_nat M j).congr'
    filter_upwards [] with n
    apply integral_congr_ae
    filter_upwards [] with z
    exact fourier_add
  · simp
  · intro f g _ _ hf hg
    have h : Tendsto (fun n : ℕ =>
        (∫ z, f z * fourier (n : ℤ) z ∂(M : Measure UnitAddCircle)) +
        ∫ z, g z * fourier (n : ℤ) z ∂(M : Measure UnitAddCircle)) atTop (𝓝 0) := by
      simpa using hf.add hg
    apply h.congr'
    filter_upwards [] with n
    rw [← integral_add (continuous_mul_fourier_integrable M f (n : ℤ))
      (continuous_mul_fourier_integrable M g (n : ℤ))]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [ContinuousMap.add_apply]
    ring
  · intro c f _ hf
    have h : Tendsto (fun n : ℕ =>
        c * ∫ z, f z * fourier (n : ℤ) z ∂(M : Measure UnitAddCircle))
        atTop (𝓝 0) := by
      simpa using hf.const_mul c
    apply h.congr'
    filter_upwards [] with n
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    ring

private theorem rajchman_tendsto_continuous_weight_neg_span
    (M : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ})
    {g : C(UnitAddCircle, ℂ)} (hg : g ∈ span ℂ (Set.range (@fourier (1 : ℝ)))) :
    Tendsto (fun n : ℕ => ∫ z, g z * fourier (Int.negSucc n) z ∂(M : Measure UnitAddCircle))
      atTop (𝓝 0) := by
  letI : IsFiniteMeasure (M : Measure UnitAddCircle) := M.2.1
  refine Submodule.span_induction (p := fun g _ => Tendsto
    (fun n : ℕ => ∫ z, g z * fourier (Int.negSucc n) z ∂(M : Measure UnitAddCircle))
    atTop (𝓝 0)) ?_ ?_ ?_ ?_ hg
  · rintro _ ⟨j, rfl⟩
    apply (rajchman_tendsto_fourier_add_negSucc M j).congr'
    filter_upwards [] with n
    apply integral_congr_ae
    filter_upwards [] with z
    exact fourier_add
  · simp
  · intro f g _ _ hf hg
    have h : Tendsto (fun n : ℕ =>
        (∫ z, f z * fourier (Int.negSucc n) z ∂(M : Measure UnitAddCircle)) +
        ∫ z, g z * fourier (Int.negSucc n) z ∂(M : Measure UnitAddCircle))
        atTop (𝓝 0) := by
      simpa using hf.add hg
    apply h.congr'
    filter_upwards [] with n
    rw [← integral_add (continuous_mul_fourier_integrable M f (Int.negSucc n))
      (continuous_mul_fourier_integrable M g (Int.negSucc n))]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [ContinuousMap.add_apply]
    ring
  · intro c f _ hf
    have h : Tendsto (fun n : ℕ =>
        c * ∫ z, f z * fourier (Int.negSucc n) z ∂(M : Measure UnitAddCircle))
        atTop (𝓝 0) := by
      simpa using hf.const_mul c
    apply h.congr'
    filter_upwards [] with n
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    ring

/-- Two-sided Fourier decay after multiplication by a continuous complex weight. -/
def IsAddCircleContinuousWeightRajchman (μ : Measure UnitAddCircle)
    (g : C(UnitAddCircle, ℂ)) : Prop :=
  Tendsto (fun n : ℕ => ∫ z, g z * fourier (n : ℤ) z ∂μ) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ∫ z, g z * fourier (Int.negSucc n) z ∂μ) atTop (𝓝 0)

private theorem norm_weighted_fourier_integral_sub_le
    (M : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ})
    (f g : C(UnitAddCircle, ℂ)) (j : ℤ) :
    ‖(∫ z, f z * fourier j z ∂(M : Measure UnitAddCircle)) -
        ∫ z, g z * fourier j z ∂(M : Measure UnitAddCircle)‖ ≤
      ‖f - g‖ * (M : Measure UnitAddCircle).real univ := by
  letI : IsFiniteMeasure (M : Measure UnitAddCircle) := M.2.1
  rw [← integral_sub (continuous_mul_fourier_integrable M f j)
    (continuous_mul_fourier_integrable M g j)]
  apply norm_integral_le_of_norm_le_const
  filter_upwards [] with z
  rw [← sub_mul, norm_mul, fourier_apply, Circle.norm_coe, mul_one]
  exact ContinuousMap.norm_coe_le_norm (f - g) z

private theorem rajchman_tendsto_continuous_weight_of_span
    (M : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ})
    (g : C(UnitAddCircle, ℂ)) (index : ℕ → ℤ)
    (hspan : ∀ q : C(UnitAddCircle, ℂ), q ∈ span ℂ (Set.range (@fourier (1 : ℝ))) →
      Tendsto (fun n : ℕ =>
        ∫ z, q z * fourier (index n) z ∂(M : Measure UnitAddCircle)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      ∫ z, g z * fourier (index n) z ∂(M : Measure UnitAddCircle)) atTop (𝓝 0) := by
  letI : IsFiniteMeasure (M : Measure UnitAddCircle) := M.2.1
  rw [Metric.tendsto_atTop]
  intro ε hε
  let mass := (M : Measure UnitAddCircle).real univ
  have hmass : 0 ≤ mass := measureReal_nonneg
  have hclosure : g ∈ (span ℂ
      (Set.range (@fourier (1 : ℝ)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    exact Submodule.mem_top
  obtain ⟨q, hqspan, hgq⟩ := Metric.mem_closure_iff.mp hclosure
    (ε / (2 * (mass + 1))) (by positivity)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (hspan q hqspan)) (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_zero_right]
  have hqsmall : ‖∫ z, q z * fourier (index n) z
      ∂(M : Measure UnitAddCircle)‖ < ε / 2 := by
    simpa only [dist_zero_right] using hN n hn
  have herr : ‖(∫ z, g z * fourier (index n) z ∂(M : Measure UnitAddCircle)) -
      ∫ z, q z * fourier (index n) z ∂(M : Measure UnitAddCircle)‖ < ε / 2 := by
    refine (norm_weighted_fourier_integral_sub_le M g q (index n)).trans_lt ?_
    calc
      ‖g - q‖ * mass ≤ ‖g - q‖ * (mass + 1) := by
        exact mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      _ < (ε / (2 * (mass + 1))) * (mass + 1) := by
        exact mul_lt_mul_of_pos_right (by simpa only [dist_eq_norm] using hgq) (by positivity)
      _ = ε / 2 := by field_simp
  calc
    ‖∫ z, g z * fourier (index n) z ∂(M : Measure UnitAddCircle)‖
        ≤ ‖(∫ z, g z * fourier (index n) z ∂(M : Measure UnitAddCircle)) -
            ∫ z, q z * fourier (index n) z ∂(M : Measure UnitAddCircle)‖ +
          ‖∫ z, q z * fourier (index n) z ∂(M : Measure UnitAddCircle)‖ := by
          simpa only [sub_add_cancel] using norm_add_le
            ((∫ z, g z * fourier (index n) z ∂(M : Measure UnitAddCircle)) -
              ∫ z, q z * fourier (index n) z ∂(M : Measure UnitAddCircle))
            (∫ z, q z * fourier (index n) z ∂(M : Measure UnitAddCircle))
    _ < ε := by linarith

/-- Cai--Chen--Fang--Guo's continuous-multiplier mechanism: every continuous observation weight
preserves two-sided Rajchman decay of a finite circle measure. -/
theorem addCircleRajchman_continuous_weight
    (M : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ})
    (g : C(UnitAddCircle, ℂ)) :
    IsAddCircleContinuousWeightRajchman M g := by
  constructor
  · exact rajchman_tendsto_continuous_weight_of_span M g (fun n => (n : ℤ))
      (fun q hq => rajchman_tendsto_continuous_weight_pos_span M hq)
  · exact rajchman_tendsto_continuous_weight_of_span M g Int.negSucc
      (fun q hq => rajchman_tendsto_continuous_weight_neg_span M hq)

/-- A continuous nonnegative density on the unit circle. -/
def ContinuousNonnegativeCircleWeight :=
  {g : C(UnitAddCircle, ℝ) // ∀ z, 0 ≤ g z}

def ContinuousNonnegativeCircleWeight.complex
    (g : ContinuousNonnegativeCircleWeight) : C(UnitAddCircle, ℂ) :=
  ⟨fun z => (g.1 z : ℂ), Complex.continuous_ofReal.comp g.1.continuous⟩

/-- Reweight a Rajchman circle measure by a continuous nonnegative density. -/
def continuousWeightedCircleMeasure
    (M : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ})
    (g : ContinuousNonnegativeCircleWeight) : Measure UnitAddCircle :=
  (M : Measure UnitAddCircle).withDensity (fun z => ENNReal.ofReal (g.1 z))

private theorem continuousNonnegativeCircleWeight_hasFiniteIntegral
    (M : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ})
    (g : ContinuousNonnegativeCircleWeight) :
    HasFiniteIntegral (fun z => g.1 z) (M : Measure UnitAddCircle) := by
  letI : IsFiniteMeasure (M : Measure UnitAddCircle) := M.2.1
  exact (g.1.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)).hasFiniteIntegral

private theorem integral_fourier_continuousWeightedCircleMeasure
    (M : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ})
    (g : ContinuousNonnegativeCircleWeight) (j : ℤ) :
    ∫ z, fourier j z ∂continuousWeightedCircleMeasure M g =
      ∫ z, g.complex z * fourier j z ∂(M : Measure UnitAddCircle) := by
  letI : IsFiniteMeasure (M : Measure UnitAddCircle) := M.2.1
  rw [continuousWeightedCircleMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (g.1.continuous.measurable.ennreal_ofReal)
      (Filter.Eventually.of_forall fun z => ENNReal.ofReal_lt_top) (fun z => fourier j z)]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [ENNReal.toReal_ofReal (g.2 z), ContinuousNonnegativeCircleWeight.complex,
    ContinuousMap.coe_mk, Complex.real_smul]

/-- Positive-measure form of the multiplier theorem: a continuous nonnegative density turns any
Rajchman circle measure into another finite Rajchman measure. -/
theorem continuousWeightedCircleMeasure_isAddCircleRajchman
    (M : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ})
    (g : ContinuousNonnegativeCircleWeight) :
    IsAddCircleRajchman (continuousWeightedCircleMeasure M g) := by
  letI : IsFiniteMeasure (M : Measure UnitAddCircle) := M.2.1
  have hfinite : IsFiniteMeasure (continuousWeightedCircleMeasure M g) := by
    exact isFiniteMeasure_withDensity_ofReal
      (continuousNonnegativeCircleWeight_hasFiniteIntegral M g)
  have hweighted := addCircleRajchman_continuous_weight M g.complex
  refine ⟨hfinite, ?_, ?_⟩
  · apply hweighted.1.congr'
    filter_upwards [] with n
    exact (integral_fourier_continuousWeightedCircleMeasure M g (n : ℤ)).symm
  · apply hweighted.2.congr'
    filter_upwards [] with n
    exact (integral_fourier_continuousWeightedCircleMeasure M g (Int.negSucc n)).symm

/-- An integrable complex observation weight for a fixed Rajchman circle measure. -/
def IntegrableCircleWeight
    (M : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ}) :=
  {g : UnitAddCircle → ℂ // Integrable g (M : Measure UnitAddCircle)}

/-- Two-sided Fourier decay after multiplication by an arbitrary integrable weight. -/
def IsAddCircleIntegrableWeightRajchman
    (M : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ})
    (g : IntegrableCircleWeight M) : Prop :=
  Tendsto (fun n : ℕ => ∫ z, g.1 z * fourier (n : ℤ) z ∂(M : Measure UnitAddCircle))
      atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ∫ z, g.1 z * fourier (Int.negSucc n) z
      ∂(M : Measure UnitAddCircle)) atTop (𝓝 0)

private theorem integrable_weight_mul_fourier
    (M : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ})
    (g : IntegrableCircleWeight M) (j : ℤ) :
    Integrable (fun z => g.1 z * fourier j z) (M : Measure UnitAddCircle) := by
  apply g.2.mul_bdd (fourier j).continuous.aestronglyMeasurable
  filter_upwards [] with z
  rw [fourier_apply, Circle.norm_coe]

private theorem norm_integrable_weighted_fourier_integral_sub_le
    (M : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ})
    (g : IntegrableCircleWeight M) (q : C(UnitAddCircle, ℂ)) (j : ℤ) :
    ‖(∫ z, g.1 z * fourier j z ∂(M : Measure UnitAddCircle)) -
        ∫ z, q z * fourier j z ∂(M : Measure UnitAddCircle)‖ ≤
      ∫ z, ‖g.1 z - q z‖ ∂(M : Measure UnitAddCircle) := by
  letI : IsFiniteMeasure (M : Measure UnitAddCircle) := M.2.1
  rw [← integral_sub (integrable_weight_mul_fourier M g j)
    (continuous_mul_fourier_integrable M q j)]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply integral_congr_ae
  filter_upwards [] with z
  rw [← sub_mul, norm_mul, fourier_apply, Circle.norm_coe, mul_one]

private theorem rajchman_tendsto_integrable_weight_of_continuous
    (M : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ})
    (g : IntegrableCircleWeight M) (index : ℕ → ℤ)
    (hcontinuous : ∀ q : C(UnitAddCircle, ℂ), Tendsto (fun n : ℕ =>
      ∫ z, q z * fourier (index n) z ∂(M : Measure UnitAddCircle)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      ∫ z, g.1 z * fourier (index n) z ∂(M : Measure UnitAddCircle)) atTop (𝓝 0) := by
  letI : IsFiniteMeasure (M : Measure UnitAddCircle) := M.2.1
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨q, hgq, _⟩ := g.2.exists_boundedContinuous_integral_sub_le
    (ε := ε / 2) (by positivity)
  let qc : C(UnitAddCircle, ℂ) := q.toContinuousMap
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (hcontinuous qc)) (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_zero_right]
  have hqsmall : ‖∫ z, qc z * fourier (index n) z
      ∂(M : Measure UnitAddCircle)‖ < ε / 2 := by
    simpa only [dist_zero_right] using hN n hn
  have herr : ‖(∫ z, g.1 z * fourier (index n) z ∂(M : Measure UnitAddCircle)) -
      ∫ z, qc z * fourier (index n) z ∂(M : Measure UnitAddCircle)‖ ≤ ε / 2 := by
    refine (norm_integrable_weighted_fourier_integral_sub_le M g qc (index n)).trans ?_
    simpa only [qc, BoundedContinuousFunction.coe_toContinuousMap] using hgq
  calc
    ‖∫ z, g.1 z * fourier (index n) z ∂(M : Measure UnitAddCircle)‖
        ≤ ‖(∫ z, g.1 z * fourier (index n) z ∂(M : Measure UnitAddCircle)) -
            ∫ z, qc z * fourier (index n) z ∂(M : Measure UnitAddCircle)‖ +
          ‖∫ z, qc z * fourier (index n) z ∂(M : Measure UnitAddCircle)‖ := by
          simpa only [sub_add_cancel] using norm_add_le
            ((∫ z, g.1 z * fourier (index n) z ∂(M : Measure UnitAddCircle)) -
              ∫ z, qc z * fourier (index n) z ∂(M : Measure UnitAddCircle))
            (∫ z, qc z * fourier (index n) z ∂(M : Measure UnitAddCircle))
    _ < ε := by linarith

/-- Full `L¹` form of Cai--Chen--Fang--Guo Lemma 6.4: every integrable complex multiplier of a
finite Rajchman circle measure remains Rajchman at coefficient level. -/
theorem addCircleRajchman_integrable_weight
    (M : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ})
    (g : IntegrableCircleWeight M) :
    IsAddCircleIntegrableWeightRajchman M g := by
  have hc := addCircleRajchman_continuous_weight M
  constructor
  · exact rajchman_tendsto_integrable_weight_of_continuous M g (fun n => (n : ℤ))
      (fun q => (hc q).1)
  · exact rajchman_tendsto_integrable_weight_of_continuous M g Int.negSucc
      (fun q => (hc q).2)

/-- Haar measure bundled with its Rajchman proof for repeated transfer applications. -/
def circleLebesgueRajchmanMeasure :
    {μ : Measure Circle // IsCircleRajchman μ} :=
  ⟨circleLebesgue, circleLebesgue_isCircleRajchman⟩

/-- A native circle Poisson law bundled with its Rajchman proof. -/
def circlePoissonRajchmanMeasure (a : CirclePoissonParameter) :
    {μ : Measure Circle // IsCircleRajchman μ} :=
  ⟨circlePoissonMeasure a, circlePoissonMeasure_isCircleRajchman a⟩

/-- A summable symmetric density measure bundled with its Rajchman proof. -/
def symmetricCircleFourierDensityRajchmanMeasure
    (a : NonnegativeSummableSymmetricCircleDensity) :
    {μ : Measure Circle // IsCircleRajchman μ} :=
  ⟨symmetricCircleFourierDensityMeasure a.1,
    symmetricCircleFourierDensityMeasure_isCircleRajchman a⟩

/-- Transported summable symmetric density, ready for additive-circle multiplier transfer. -/
def transportedSymmetricCircleFourierDensityRajchmanMeasure
    (a : NonnegativeSummableSymmetricCircleDensity) :
    {μ : Measure UnitAddCircle // IsAddCircleRajchman μ} :=
  ⟨circleMeasureToAddCircle (symmetricCircleFourierDensityMeasure a.1),
    circleMeasureToAddCircle_isAddCircleRajchman
      (symmetricCircleFourierDensityRajchmanMeasure a)⟩

/-- Native Haar transported to the additive circle remains Rajchman. -/
theorem circleLebesgueTransport_isAddCircleRajchman :
    IsAddCircleRajchman (circleMeasureToAddCircle circleLebesgue) :=
  circleMeasureToAddCircle_isAddCircleRajchman circleLebesgueRajchmanMeasure

/-- Every native Poisson law transported to the additive circle remains Rajchman. -/
theorem circlePoissonTransport_isAddCircleRajchman (a : CirclePoissonParameter) :
    IsAddCircleRajchman (circleMeasureToAddCircle (circlePoissonMeasure a)) :=
  circleMeasureToAddCircle_isAddCircleRajchman (circlePoissonRajchmanMeasure a)

/-- Every transported summable symmetric density admits arbitrary `L¹` observations with
vanishing high-frequency response. -/
theorem transportedSymmetricCircleFourierDensity_integrable_weight_isRajchman
    (a : NonnegativeSummableSymmetricCircleDensity)
    (g : IntegrableCircleWeight (transportedSymmetricCircleFourierDensityRajchmanMeasure a)) :
    IsAddCircleIntegrableWeightRajchman
      (transportedSymmetricCircleFourierDensityRajchmanMeasure a) g :=
  addCircleRajchman_integrable_weight
    (transportedSymmetricCircleFourierDensityRajchmanMeasure a) g

/-- Every continuous nonnegative tilt of a transported summable symmetric density is Rajchman. -/
theorem transportedSymmetricCircleFourierDensity_continuousWeighted_isAddCircleRajchman
    (a : NonnegativeSummableSymmetricCircleDensity)
    (g : ContinuousNonnegativeCircleWeight) :
    IsAddCircleRajchman (continuousWeightedCircleMeasure
      (transportedSymmetricCircleFourierDensityRajchmanMeasure a) g) :=
  continuousWeightedCircleMeasure_isAddCircleRajchman
    (transportedSymmetricCircleFourierDensityRajchmanMeasure a) g

/-- Haar measure bundled with its Rajchman proof for repeated transfer applications. -/
def unitCircleHaarRajchmanMeasure :
    {μ : Measure UnitAddCircle // IsAddCircleRajchman μ} :=
  ⟨GaloisForLFunctions.unitCircleHaar, unitCircleHaar_isAddCircleRajchman⟩

/-- A transported Poisson law bundled with its Rajchman proof. -/
def addCirclePoissonRajchmanMeasure (a : CirclePoissonParameter) :
    {μ : Measure UnitAddCircle // IsAddCircleRajchman μ} :=
  ⟨addCirclePoissonProbabilityMeasure a,
    addCirclePoissonProbabilityMeasure_isAddCircleRajchman a⟩

/-- Every `L¹` observable against circle Haar has vanishing high-frequency response. -/
theorem unitCircleHaar_integrable_weight_isRajchman
    (g : IntegrableCircleWeight unitCircleHaarRajchmanMeasure) :
    IsAddCircleIntegrableWeightRajchman unitCircleHaarRajchmanMeasure g :=
  addCircleRajchman_integrable_weight unitCircleHaarRajchmanMeasure g

/-- Every `L¹` observable against a circle Poisson law has vanishing high-frequency response. -/
theorem addCirclePoisson_integrable_weight_isRajchman
    (a : CirclePoissonParameter)
    (g : IntegrableCircleWeight (addCirclePoissonRajchmanMeasure a)) :
    IsAddCircleIntegrableWeightRajchman (addCirclePoissonRajchmanMeasure a) g :=
  addCircleRajchman_integrable_weight (addCirclePoissonRajchmanMeasure a) g

/-- Every continuous nonnegative tilt of circle Haar is a finite Rajchman measure. -/
theorem unitCircleHaar_continuousWeighted_isAddCircleRajchman
    (g : ContinuousNonnegativeCircleWeight) :
    IsAddCircleRajchman (continuousWeightedCircleMeasure unitCircleHaarRajchmanMeasure g) :=
  continuousWeightedCircleMeasure_isAddCircleRajchman unitCircleHaarRajchmanMeasure g

/-- Every continuous nonnegative tilt of a circle Poisson law is a finite Rajchman measure. -/
theorem addCirclePoisson_continuousWeighted_isAddCircleRajchman
    (a : CirclePoissonParameter) (g : ContinuousNonnegativeCircleWeight) :
    IsAddCircleRajchman
      (continuousWeightedCircleMeasure (addCirclePoissonRajchmanMeasure a) g) :=
  continuousWeightedCircleMeasure_isAddCircleRajchman (addCirclePoissonRajchmanMeasure a) g

/-- A Poisson likelihood, transported from the multiplicative circle to the additive circle. -/
def addCirclePoissonContinuousWeight (a : CirclePoissonParameter) :
    ContinuousNonnegativeCircleWeight :=
  ⟨⟨fun z => poissonKernel 0 (a : ℂ) (AddCircle.toCircle z : ℂ),
      (continuous_circlePoissonDensity_real a).comp AddCircle.continuous_toCircle⟩,
    fun z => circlePoissonDensity_nonneg a (AddCircle.toCircle z)⟩

/-- Haar reweighted by any single Poisson likelihood remains Rajchman. -/
theorem unitCircleHaar_poissonWeighted_isAddCircleRajchman
    (a : CirclePoissonParameter) :
    IsAddCircleRajchman (continuousWeightedCircleMeasure unitCircleHaarRajchmanMeasure
      (addCirclePoissonContinuousWeight a)) :=
  unitCircleHaar_continuousWeighted_isAddCircleRajchman
    (addCirclePoissonContinuousWeight a)

/-- Multiplying one Poisson law by another Poisson likelihood preserves Rajchman decay. -/
theorem addCirclePoisson_poissonWeighted_isAddCircleRajchman
    (a b : CirclePoissonParameter) :
    IsAddCircleRajchman
      (continuousWeightedCircleMeasure (addCirclePoissonRajchmanMeasure a)
        (addCirclePoissonContinuousWeight b)) :=
  addCirclePoisson_continuousWeighted_isAddCircleRajchman a
    (addCirclePoissonContinuousWeight b)

/-- A finite product of Poisson likelihoods on the additive circle. -/
def finitePoissonLikelihoodCircleWeight {ι : Type*} [Fintype ι]
    (a : ι → CirclePoissonParameter) : ContinuousNonnegativeCircleWeight :=
  ⟨⟨fun z => ∏ i, poissonKernel 0 (a i : ℂ) (AddCircle.toCircle z : ℂ),
      continuous_finsetProd _ fun i _ =>
        (continuous_circlePoissonDensity_real (a i)).comp AddCircle.continuous_toCircle⟩,
    fun z => Finset.prod_nonneg fun i _ =>
      circlePoissonDensity_nonneg (a i) (AddCircle.toCircle z)⟩

/-- Finite Bayesian fusion of Poisson likelihoods over Haar preserves Rajchman decay. -/
theorem unitCircleHaar_finitePoissonLikelihoodWeighted_isAddCircleRajchman
    {ι : Type*} [Fintype ι] (a : ι → CirclePoissonParameter) :
    IsAddCircleRajchman
      (continuousWeightedCircleMeasure unitCircleHaarRajchmanMeasure
        (finitePoissonLikelihoodCircleWeight a)) :=
  unitCircleHaar_continuousWeighted_isAddCircleRajchman
    (finitePoissonLikelihoodCircleWeight a)

/-- Finite Bayesian fusion of Poisson likelihoods over a Poisson prior preserves Rajchman decay. -/
theorem addCirclePoisson_finitePoissonLikelihoodWeighted_isAddCircleRajchman
    {ι : Type*} [Fintype ι] (prior : CirclePoissonParameter)
    (a : ι → CirclePoissonParameter) :
    IsAddCircleRajchman
      (continuousWeightedCircleMeasure (addCirclePoissonRajchmanMeasure prior)
        (finitePoissonLikelihoodCircleWeight a)) :=
  addCirclePoisson_continuousWeighted_isAddCircleRajchman prior
    (finitePoissonLikelihoodCircleWeight a)

/-- A pair of distinct coordinates, packaging the separation premise in its data. -/
def DistinctCoordinatePair (I : Type*) :=
  {p : I × I // p.1 ≠ p.2}

/-- Product Poisson coordinates are independent; this is the corpus analogue of the separated-cell
conditional independence used by Cai--Chen--Fang--Guo. -/
theorem torusPoissonMeasure_distinctCoordinates_indepFun
    {I : Type*} (a : I → CirclePoissonParameter) (p : DistinctCoordinatePair I) :
    ProbabilityTheory.IndepFun (fun x : I → UnitAddCircle => x p.1.1)
      (fun x : I → UnitAddCircle => x p.1.2) (torusPoissonMeasure a) := by
  have hcoords : ProbabilityTheory.iIndepFun
      (fun i (x : I → UnitAddCircle) => x i) (torusPoissonMeasure a) := by
    exact ProbabilityTheory.iIndepFun_infinitePi
      (X := fun _ (z : UnitAddCircle) => z) (fun _ => measurable_id)
  exact hcoords.indepFun p.2

/-- Arbitrary continuous observables on two distinct Poisson coordinates have factorized
correlation. -/
theorem torusPoissonMeasure_distinctContinuousObservables_factorization
    {I : Type*} (a : I → CirclePoissonParameter) (p : DistinctCoordinatePair I)
    (f g : C(UnitAddCircle, ℂ)) :
    (∫ x, f (x p.1.1) * g (x p.1.2) ∂torusPoissonMeasure a) =
      (∫ x, f (x p.1.1) ∂torusPoissonMeasure a) *
        ∫ x, g (x p.1.2) ∂torusPoissonMeasure a := by
  have h := (torusPoissonMeasure_distinctCoordinates_indepFun a p).integral_fun_comp_mul_comp
    (measurable_pi_apply p.1.1).aemeasurable
    (measurable_pi_apply p.1.2).aemeasurable
    f.continuous.aestronglyMeasurable g.continuous.aestronglyMeasurable
  simpa only [Function.comp_apply] using h

/-- Fourier-mode version of separated-coordinate factorization. -/
theorem torusPoissonMeasure_distinctFourier_factorization
    {I : Type*} (a : I → CirclePoissonParameter) (p : DistinctCoordinatePair I) (m n : ℤ) :
    (∫ x, fourier m (x p.1.1) * fourier n (x p.1.2) ∂torusPoissonMeasure a) =
      (∫ x, fourier m (x p.1.1) ∂torusPoissonMeasure a) *
        ∫ x, fourier n (x p.1.2) ∂torusPoissonMeasure a :=
  torusPoissonMeasure_distinctContinuousObservables_factorization a p (fourier m) (fourier n)

/-- Distinct ordinary-prime phase coordinates have factorized Fourier correlations. -/
theorem primePoissonMeasure_distinctFourier_factorization
    (σ : {x : ℝ // 0 < x}) (t : ℝ) (p : DistinctCoordinatePair Nat.Primes) (m n : ℤ) :
    (∫ x, fourier m (x p.1.1) * fourier n (x p.1.2)
        ∂primePoissonMeasure σ t σ.2) =
      (∫ x, fourier m (x p.1.1) ∂primePoissonMeasure σ t σ.2) *
        ∫ x, fourier n (x p.1.2) ∂primePoissonMeasure σ t σ.2 :=
  torusPoissonMeasure_distinctFourier_factorization (primePoissonParameter σ t σ.2) p m n

/-- Circle Poisson laws also satisfy the atomlessness conclusion paired with Rajchman decay in the
paper; here it follows mechanically from their Haar density. -/
theorem circlePoissonMeasure_nullSingletonClass (a : CirclePoissonParameter) :
    NullSingletonClass (circlePoissonMeasure a) := by
  unfold circlePoissonMeasure
  infer_instance

/-- Nonnegative summable symmetric Fourier densities are atomless as well as Rajchman. -/
theorem symmetricCircleFourierDensityMeasure_nullSingletonClass
    (a : NonnegativeSummableSymmetricCircleDensity) :
    NullSingletonClass (symmetricCircleFourierDensityMeasure a.1) := by
  unfold symmetricCircleFourierDensityMeasure
  infer_instance

/-- Additive-circle Haar has no atoms. -/
theorem unitCircleHaar_nullSingletonClass :
    NullSingletonClass GaloisForLFunctions.unitCircleHaar := by
  constructor
  intro x
  have h := AddCircle.volume_closedBall (1 : ℝ) (x := x) 0
  rw [AddCircle.volume_eq_smul_haarAddCircle] at h
  simpa [GaloisForLFunctions.unitCircleHaar] using h

/-- Every continuous nonnegative tilt of additive-circle Haar remains atomless. -/
theorem unitCircleHaar_continuousWeighted_nullSingletonClass
    (g : ContinuousNonnegativeCircleWeight) :
    NullSingletonClass
      (continuousWeightedCircleMeasure unitCircleHaarRajchmanMeasure g) := by
  letI := unitCircleHaar_nullSingletonClass
  unfold continuousWeightedCircleMeasure unitCircleHaarRajchmanMeasure
  infer_instance

/-- A Poisson likelihood tilt of Haar is simultaneously Rajchman and atomless. -/
theorem unitCircleHaar_poissonWeighted_nullSingletonClass
    (a : CirclePoissonParameter) :
    NullSingletonClass (continuousWeightedCircleMeasure unitCircleHaarRajchmanMeasure
      (addCirclePoissonContinuousWeight a)) :=
  unitCircleHaar_continuousWeighted_nullSingletonClass (addCirclePoissonContinuousWeight a)

/-- Any finite Poisson-likelihood fusion over Haar is simultaneously Rajchman and atomless. -/
theorem unitCircleHaar_finitePoissonLikelihoodWeighted_nullSingletonClass
    {ι : Type*} [Fintype ι] (a : ι → CirclePoissonParameter) :
    NullSingletonClass
      (continuousWeightedCircleMeasure unitCircleHaarRajchmanMeasure
        (finitePoissonLikelihoodCircleWeight a)) :=
  unitCircleHaar_continuousWeighted_nullSingletonClass
    (finitePoissonLikelihoodCircleWeight a)

/-! ## Strict radial Poisson mixtures -/

/-- A compact radial aperture staying strictly inside the unit disk. -/
def StrictRadialPoissonAperture :=
  {R : ℝ // 0 ≤ R ∧ R < 1}

/-- A probability law for randomly choosing a Poisson radius inside a strict aperture. -/
abbrev StrictRadialPoissonMixingLaw (R : StrictRadialPoissonAperture) :=
  ProbabilityMeasure (RadialPoissonParameter R.1)

/-- Power moments of a strict radial Poisson mixing law. -/
def radialPoissonMomentSequence (R : StrictRadialPoissonAperture)
    (ν : StrictRadialPoissonMixingLaw R) (n : ℕ) : ℝ :=
  ∫ r, (r : ℝ) ^ n ∂(ν : Measure (RadialPoissonParameter R.1))

private theorem radialPoissonMomentSequence_nonneg
    (R : StrictRadialPoissonAperture) (ν : StrictRadialPoissonMixingLaw R) (n : ℕ) :
    0 ≤ radialPoissonMomentSequence R ν n := by
  apply integral_nonneg
  intro r
  exact pow_nonneg r.2.1 n

private theorem radialPoissonMomentSequence_le_pow
    (R : StrictRadialPoissonAperture) (ν : StrictRadialPoissonMixingLaw R) (n : ℕ) :
    radialPoissonMomentSequence R ν n ≤ R.1 ^ n := by
  unfold radialPoissonMomentSequence
  calc
    (∫ r : RadialPoissonParameter R.1, (r : ℝ) ^ n ∂ν) ≤
        ∫ _r : RadialPoissonParameter R.1, R.1 ^ n ∂ν := by
      apply integral_mono_ae
      · exact (show Continuous (fun r : RadialPoissonParameter R.1 => (r : ℝ) ^ n) by
          fun_prop).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      · exact integrable_const _
      · exact Filter.Eventually.of_forall fun r => by
          simpa using pow_le_pow_left₀ r.2.1 r.2.2 n
    _ = R.1 ^ n := by simp

private theorem summable_abs_radialPoissonMomentSequence_tail
    (R : StrictRadialPoissonAperture) (ν : StrictRadialPoissonMixingLaw R) :
    Summable (fun n : ℕ => |radialPoissonMomentSequence R ν (n + 1)|) := by
  have hgeo : Summable (fun n : ℕ => R.1 ^ (n + 1)) := by
    exact ((summable_geometric_of_lt_one R.2.1 R.2.2).mul_left R.1).congr
      fun n => by rw [pow_succ']
  exact Summable.of_nonneg_of_le (fun n => abs_nonneg _)
    (fun n => by
      rw [abs_of_nonneg (radialPoissonMomentSequence_nonneg R ν (n + 1))]
      exact radialPoissonMomentSequence_le_pow R ν (n + 1)) hgeo

private theorem radialPoissonBarycenter_nonneg
    (R : StrictRadialPoissonAperture) (ν : StrictRadialPoissonMixingLaw R) (z : Circle) :
    0 ≤ radialPoissonBarycenter R.2.2
      (ν : Measure (RadialPoissonParameter R.1)) z := by
  rw [radialPoissonBarycenter_apply]
  exact integral_nonneg fun r => radialPoissonKernel_nonneg R.2.2 r z

/-- Strict radial mixture moments form nonnegative absolutely summable Fourier data. -/
def radialPoissonMomentDensityData (R : StrictRadialPoissonAperture)
    (ν : StrictRadialPoissonMixingLaw R) :
    NonnegativeSummableSymmetricCircleDensity :=
  ⟨radialPoissonMomentSequence R ν,
    summable_abs_radialPoissonMomentSequence_tail R ν,
    fun z => by
      unfold radialPoissonMomentSequence
      rw [← radialPoissonBarycenter_eq_symmetricCircleFourierDensity_moments
        R.2.1 R.2.2 (ν : Measure (RadialPoissonParameter R.1)) z]
      exact radialPoissonBarycenter_nonneg R ν z⟩

/-- Circle measure whose density is a probability barycenter of strict radial Poisson kernels. -/
def radialPoissonBarycenterMeasure (R : StrictRadialPoissonAperture)
    (ν : StrictRadialPoissonMixingLaw R) : Measure Circle :=
  circleLebesgue.withDensity fun z => ENNReal.ofReal
    (radialPoissonBarycenter R.2.2
      (ν : Measure (RadialPoissonParameter R.1)) z)

private theorem radialPoissonBarycenterMeasure_eq_symmetricDensity
    (R : StrictRadialPoissonAperture) (ν : StrictRadialPoissonMixingLaw R) :
    radialPoissonBarycenterMeasure R ν =
      symmetricCircleFourierDensityMeasure (radialPoissonMomentSequence R ν) := by
  unfold radialPoissonBarycenterMeasure symmetricCircleFourierDensityMeasure
  congr 1
  funext z
  rw [radialPoissonBarycenter_eq_symmetricCircleFourierDensity_moments
    R.2.1 R.2.2 (ν : Measure (RadialPoissonParameter R.1)) z]
  rfl

/-- Every strict radial Poisson mixture is a finite Rajchman circle measure. -/
theorem radialPoissonBarycenterMeasure_isCircleRajchman
    (R : StrictRadialPoissonAperture) (ν : StrictRadialPoissonMixingLaw R) :
    IsCircleRajchman (radialPoissonBarycenterMeasure R ν) := by
  rw [radialPoissonBarycenterMeasure_eq_symmetricDensity]
  exact symmetricCircleFourierDensityMeasure_isCircleRajchman
    (radialPoissonMomentDensityData R ν)

/-- A strict radial Poisson mixture bundled with its Rajchman certificate. -/
def radialPoissonBarycenterRajchmanMeasure
    (R : StrictRadialPoissonAperture) (ν : StrictRadialPoissonMixingLaw R) :
    {μ : Measure Circle // IsCircleRajchman μ} :=
  ⟨radialPoissonBarycenterMeasure R ν,
    radialPoissonBarycenterMeasure_isCircleRajchman R ν⟩

/-- Canonical additive-circle transport of a strict radial Poisson mixture. -/
def radialPoissonBarycenterAddCircleMeasure
    (R : StrictRadialPoissonAperture) (ν : StrictRadialPoissonMixingLaw R) :
    Measure UnitAddCircle :=
  circleMeasureToAddCircle (radialPoissonBarycenterMeasure R ν)

/-- Every transported strict radial Poisson mixture is Rajchman on the additive circle. -/
theorem radialPoissonBarycenterAddCircleMeasure_isAddCircleRajchman
    (R : StrictRadialPoissonAperture) (ν : StrictRadialPoissonMixingLaw R) :
    IsAddCircleRajchman (radialPoissonBarycenterAddCircleMeasure R ν) :=
  circleMeasureToAddCircle_isAddCircleRajchman
    (radialPoissonBarycenterRajchmanMeasure R ν)

/-- Transported strict radial mixtures bundled with their Rajchman certificates. -/
def radialPoissonBarycenterAddCircleRajchmanMeasure
    (R : StrictRadialPoissonAperture) (ν : StrictRadialPoissonMixingLaw R) :
    {μ : Measure UnitAddCircle // IsAddCircleRajchman μ} :=
  ⟨radialPoissonBarycenterAddCircleMeasure R ν,
    radialPoissonBarycenterAddCircleMeasure_isAddCircleRajchman R ν⟩

/-- Every integrable observable of a transported strict radial mixture has vanishing Fourier tail. -/
theorem radialPoissonBarycenter_integrable_weight_isRajchman
    (R : StrictRadialPoissonAperture) (ν : StrictRadialPoissonMixingLaw R)
    (g : IntegrableCircleWeight (radialPoissonBarycenterAddCircleRajchmanMeasure R ν)) :
    IsAddCircleIntegrableWeightRajchman
      (radialPoissonBarycenterAddCircleRajchmanMeasure R ν) g :=
  addCircleRajchman_integrable_weight
    (radialPoissonBarycenterAddCircleRajchmanMeasure R ν) g

/-- Every strict radial Poisson mixture is atomless. -/
theorem radialPoissonBarycenterMeasure_nullSingletonClass
    (R : StrictRadialPoissonAperture) (ν : StrictRadialPoissonMixingLaw R) :
    NullSingletonClass (radialPoissonBarycenterMeasure R ν) := by
  rw [radialPoissonBarycenterMeasure_eq_symmetricDensity]
  exact symmetricCircleFourierDensityMeasure_nullSingletonClass
    (radialPoissonMomentDensityData R ν)

/-! ## Strictly positive multiplier equivalence -/

/-- Continuous observation weight that never vanishes. -/
def ContinuousStrictlyPositiveCircleWeight :=
  {g : C(UnitAddCircle, ℝ) // ∀ z, 0 < g z}

/-- Forget strict positivity while retaining nonnegativity. -/
def ContinuousStrictlyPositiveCircleWeight.nonnegative
    (g : ContinuousStrictlyPositiveCircleWeight) : ContinuousNonnegativeCircleWeight :=
  ⟨g.1, fun z => (g.2 z).le⟩

/-- Reciprocal of a strictly positive continuous weight is another nonnegative continuous weight. -/
def ContinuousStrictlyPositiveCircleWeight.invNonnegative
    (g : ContinuousStrictlyPositiveCircleWeight) : ContinuousNonnegativeCircleWeight :=
  ⟨⟨fun z => (g.1 z)⁻¹,
      g.1.continuous.inv₀ fun z => (g.2 z).ne'⟩,
    fun z => (inv_pos.mpr (g.2 z)).le⟩

/-- Weight an arbitrary finite additive-circle measure by a strictly positive continuous density. -/
def strictlyPositiveWeightedFiniteCircleMeasure
    (M : {μ : Measure UnitAddCircle // IsFiniteMeasure μ})
    (g : ContinuousStrictlyPositiveCircleWeight) : Measure UnitAddCircle :=
  (M : Measure UnitAddCircle).withDensity fun z => ENNReal.ofReal (g.1 z)

/-- Full multiplier equivalence from Cai--Chen--Fang--Guo: multiplication by a continuous,
strictly positive density preserves and reflects the Rajchman property. -/
theorem strictlyPositiveWeightedFiniteCircleMeasure_rajchman_iff
    (M : {μ : Measure UnitAddCircle // IsFiniteMeasure μ})
    (g : ContinuousStrictlyPositiveCircleWeight) :
    IsAddCircleRajchman (strictlyPositiveWeightedFiniteCircleMeasure M g) ↔
      IsAddCircleRajchman (M : Measure UnitAddCircle) := by
  constructor
  · intro hweighted
    let W : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ} :=
      ⟨strictlyPositiveWeightedFiniteCircleMeasure M g, hweighted⟩
    have hback := continuousWeightedCircleMeasure_isAddCircleRajchman W g.invNonnegative
    have heq : continuousWeightedCircleMeasure W g.invNonnegative =
        (M : Measure UnitAddCircle) := by
      unfold continuousWeightedCircleMeasure W
      change ((M : Measure UnitAddCircle).withDensity
          (fun z => ENNReal.ofReal (g.1 z))).withDensity
            (fun z => ENNReal.ofReal ((g.1 z)⁻¹)) = (M : Measure UnitAddCircle)
      rw [show (fun z => ENNReal.ofReal ((g.1 z)⁻¹)) =
          fun z => (ENNReal.ofReal (g.1 z))⁻¹ by
        funext z
        exact ENNReal.ofReal_inv_of_pos (g.2 z)]
      exact MeasureTheory.withDensity_inv_same
        (g.1.continuous.measurable.ennreal_ofReal)
        (Filter.Eventually.of_forall fun z => by simp [g.2 z])
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_ne_top)
    rwa [heq] at hback
  · intro hM
    let MR : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ} :=
      ⟨(M : Measure UnitAddCircle), hM⟩
    change IsAddCircleRajchman
      (continuousWeightedCircleMeasure MR g.nonnegative)
    exact continuousWeightedCircleMeasure_isAddCircleRajchman MR g.nonnegative

/-! ## Infinite Poisson-product likelihood limits -/

/-- A convergent `L²` half-likelihood limit, with convergence packaged as data rather than as a
theorem premise. -/
def CirclePoissonHalfLikelihoodLimitWitness
    (a b : ℕ → CirclePoissonParameter) :=
  {G : Lp ℝ 2 (natCirclePoissonProductMeasure b) //
    Tendsto (circlePoissonPrefixHalfLikelihoodLp a b) atTop (𝓝 G)}

/-- Additive infinite-torus transport of the squared `L²` half-likelihood limit law. -/
def circlePoissonLimitDensityTorusMeasure
    (a b : ℕ → CirclePoissonParameter)
    (W : CirclePoissonHalfLikelihoodLimitWitness a b) :
    Measure (ℕ → UnitAddCircle) :=
  (circlePoissonLimitDensityMeasure b W.1).map circleProductHomeomorphUnitTorus

/-- Every finite-support character of the transported likelihood limit has the exact target
Poisson-product coefficient. -/
theorem integral_infiniteTorusFourier_circlePoissonLimitDensityTorusMeasure
    (a b : ℕ → CirclePoissonParameter)
    (W : CirclePoissonHalfLikelihoodLimitWitness a b) (n : ℕ →₀ ℤ) :
    ∫ x, infiniteTorusFourier n x ∂circlePoissonLimitDensityTorusMeasure a b W =
      n.prod fun i q => circlePoissonFourierMoment (a i) q := by
  rw [circlePoissonLimitDensityTorusMeasure,
    integral_map circleProductHomeomorphUnitTorus.continuous.aemeasurable
      (infiniteTorusFourier n).continuous.aestronglyMeasurable]
  simpa only [infiniteTorusFourier_circleProductHomeomorphUnitTorus] using
    integral_infiniteCircleFourier_circlePoissonLimitDensityMeasure a b n W.2

/-- Every coordinate marginal of an infinite Poisson-product `L²` likelihood limit is Rajchman. -/
theorem circlePoissonLimitDensityTorusMeasure_isInfiniteTorusCoordinateRajchman
    (a b : ℕ → CirclePoissonParameter)
    (W : CirclePoissonHalfLikelihoodLimitWitness a b) (i : ℕ) :
    IsInfiniteTorusCoordinateRajchman
      (circlePoissonLimitDensityTorusMeasure a b W) i := by
  classical
  letI : IsProbabilityMeasure (circlePoissonLimitDensityMeasure b W.1) :=
    isProbabilityMeasure_circlePoissonLimitDensityMeasure a b W.2
  refine ⟨by
    unfold circlePoissonLimitDensityTorusMeasure
    infer_instance, ?_, ?_⟩
  · have hpow : Tendsto (fun n : ℕ => (a i : ℂ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one
        (by simpa only [mem_ball_zero_iff] using (a i).2)
    apply hpow.congr'
    filter_upwards [] with n
    rw [integral_infiniteTorusFourier_circlePoissonLimitDensityTorusMeasure]
    simp [circlePoissonFourierMoment, Finsupp.prod_single_index]
  · have hpow : Tendsto (fun n : ℕ => conj (a i : ℂ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one
        (by simpa only [norm_conj, mem_ball_zero_iff] using (a i).2)
    have hlim : Tendsto (fun n : ℕ => conj (a i : ℂ) ^ n * conj (a i : ℂ))
        atTop (𝓝 0) := by
      simpa only [zero_mul] using hpow.mul_const (conj (a i : ℂ))
    apply hlim.congr'
    filter_upwards [] with n
    rw [integral_infiniteTorusFourier_circlePoissonLimitDensityTorusMeasure]
    simp [circlePoissonFourierMoment, Finsupp.prod_single_index, pow_succ]

/-! ## Uniform-clock phase laws -/

/-- Two-sided cancellation along integer multiples of a finite-support character on an infinite
product torus. -/
def IsInfiniteTorusRayRajchman {I : Type*}
    (μ : Measure (I → UnitAddCircle)) (m : I →₀ ℤ) : Prop :=
  IsFiniteMeasure μ ∧
    Tendsto (fun n : ℕ =>
      ∫ x, infiniteTorusFourier ((n : ℤ) • m) x ∂μ) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ =>
      ∫ x, infiniteTorusFourier ((Int.negSucc n) • m) x ∂μ) atTop (𝓝 0)

/-- Infinite-torus detuning is homogeneous under integer scaling of a finite-support character. -/
theorem infiniteTorusCharacterDetuning_zsmul
    {I : Type*} (k : ℤ) (m : I →₀ ℤ) (omega : I → ℝ) :
    infiniteTorusCharacterDetuning (k • m) omega =
      (k : ℝ) * infiniteTorusCharacterDetuning m omega := by
  classical
  rw [infiniteTorusCharacterDetuning, infiniteTorusCharacterDetuning,
    Finsupp.sum_smul_index (fun _ => by simp)]
  simp only [Int.cast_mul, Finsupp.sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A finite-support character whose selected countable-spectrum detuning is nonzero. -/
def NonresonantInfiniteTorusCharacter {I : Type*} (omega : I → ℝ) :=
  {m : I →₀ ℤ // infiniteTorusCharacterDetuning m omega ≠ 0}

/-- A real probability clock whose characteristic function vanishes along every nonzero integer
frequency ray. -/
def IsRajchmanClockLaw (clockLaw : ProbabilityMeasure ℝ) : Prop :=
  ∀ d : {x : ℝ // x ≠ 0},
    Tendsto (fun n : ℕ => charFun (clockLaw : Measure ℝ) ((n : ℝ) * d.1))
      atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ =>
      charFun (clockLaw : Measure ℝ) (-(n + 1 : ℝ) * d.1)) atTop (𝓝 0)

/-- Probability clock bundled with its two-sided Rajchman certificate. -/
def RajchmanClockLaw :=
  {clockLaw : ProbabilityMeasure ℝ // IsRajchmanClockLaw clockLaw}

/-- Nonnegative integrable real density normalized to total mass one. -/
def RealProbabilityDensityData :=
  {f : ℝ → ℝ // Integrable f ∧ (∀ x, 0 ≤ f x) ∧ ∫ x, f x = 1}

/-- Probability measure represented by a normalized integrable real density. -/
def realProbabilityDensityMeasure (f : RealProbabilityDensityData) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (f.1 x)

instance realProbabilityDensityMeasure.instProbability (f : RealProbabilityDensityData) :
    IsProbabilityMeasure (realProbabilityDensityMeasure f) := by
  rw [isProbabilityMeasure_iff, realProbabilityDensityMeasure,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal f.2.1
    (Filter.Eventually.of_forall f.2.2.1)]
  rw [f.2.2.2]
  norm_num

/-- Bundled probability clock represented by an integrable density. -/
def realProbabilityDensityClock (f : RealProbabilityDensityData) : ProbabilityMeasure ℝ :=
  ⟨realProbabilityDensityMeasure f, inferInstance⟩

/-- Every real probability-density clock is atomless. -/
theorem realProbabilityDensityClock_nullSingletonClass
    (f : RealProbabilityDensityData) :
    NullSingletonClass (realProbabilityDensityClock f : Measure ℝ) := by
  change NullSingletonClass (realProbabilityDensityMeasure f)
  unfold realProbabilityDensityMeasure
  infer_instance

private theorem charFun_realProbabilityDensityClock
    (f : RealProbabilityDensityData) (t : ℝ) :
    charFun (realProbabilityDensityClock f : Measure ℝ) t =
      ∫ x : ℝ, Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) * (f.1 x : ℂ) := by
  change charFun (realProbabilityDensityMeasure f) t = _
  rw [charFun_apply_real, realProbabilityDensityMeasure,
    integral_withDensity_eq_integral_toReal_smul₀
      (f.2.1.aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal (f.2.2.1 x), Complex.real_smul]
  ring

private theorem fourierChar_density_eq_charFun_integrand (x t : ℝ) (c : ℂ) :
    𝐞 (-(x * (-t / (2 * Real.pi)))) * c =
      Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) * c := by
  rw [Real.fourierChar_apply]
  congr 2
  push_cast
  field_simp [Real.pi_ne_zero]

private theorem realProbabilityDensityClock_pos_ray
    (f : RealProbabilityDensityData) (d : {x : ℝ // x ≠ 0}) :
    Tendsto (fun n : ℕ =>
      charFun (realProbabilityDensityClock f : Measure ℝ) ((n : ℝ) * d.1))
      atTop (𝓝 0) := by
  let path : ℕ → ℝ := fun n => -((n : ℝ) * d.1) / (2 * Real.pi)
  have hc : 0 < |d.1| / (2 * Real.pi) :=
    div_pos (abs_pos.mpr d.2) (mul_pos zero_lt_two Real.pi_pos)
  have hdist : Tendsto (fun n => dist (path n) 0) atTop atTop := by
    have h := tendsto_natCast_atTop_atTop.atTop_mul_const hc
    apply h.congr'
    filter_upwards [] with n
    dsimp only [path]
    rw [Real.dist_eq, sub_zero, abs_div, abs_neg, abs_mul,
      abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    have hn : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
    rw [hn]
    ring
  have hpath : Tendsto path atTop (cocompact ℝ) :=
    tendsto_cocompact_of_tendsto_dist_comp_atTop 0 hdist
  have hRL := (Real.tendsto_integral_exp_smul_cocompact
    (fun x : ℝ => (f.1 x : ℂ))).comp hpath
  apply hRL.congr'
  filter_upwards [] with n
  rw [charFun_realProbabilityDensityClock]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Circle.smul_def]
  exact fourierChar_density_eq_charFun_integrand
    x ((n : ℝ) * d.1) (f.1 x : ℂ)

private theorem realProbabilityDensityClock_neg_ray
    (f : RealProbabilityDensityData) (d : {x : ℝ // x ≠ 0}) :
    Tendsto (fun n : ℕ =>
      charFun (realProbabilityDensityClock f : Measure ℝ) (-(n + 1 : ℝ) * d.1))
      atTop (𝓝 0) := by
  let dn : {x : ℝ // x ≠ 0} := ⟨-d.1, neg_ne_zero.mpr d.2⟩
  have h := (realProbabilityDensityClock_pos_ray f dn).comp (tendsto_add_atTop_nat 1)
  apply h.congr'
  filter_upwards [] with n
  dsimp only [Function.comp_apply, dn]
  apply congrArg (charFun (realProbabilityDensityClock f : Measure ℝ))
  push_cast
  ring

/-- Every integrable real probability density defines a Rajchman clock by the
Riemann--Lebesgue lemma. -/
def realProbabilityDensityRajchmanClockLaw
    (f : RealProbabilityDensityData) : RajchmanClockLaw :=
  ⟨realProbabilityDensityClock f, fun d =>
    ⟨realProbabilityDensityClock_pos_ray f d,
      realProbabilityDensityClock_neg_ray f d⟩⟩

/-- Every Rajchman clock produces finite-spectrum Rajchman decay on every nonresonant ray. -/
theorem finiteRajchmanClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (clockLaw : RajchmanClockLaw) (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure clockLaw.1 energy :
        Measure (UnitAddTorus d)) m.1 := by
  classical
  let δ : {x : ℝ // x ≠ 0} :=
    ⟨finiteTorusCharacterDetuning m.1 energy, m.2⟩
  refine ⟨inferInstance, ?_, ?_⟩
  · apply (clockLaw.2 δ).1.congr'
    filter_upwards [] with n
    rw [finiteClockSampledPhaseProbabilityMeasure_mFourier_integral,
      finiteTorusCharacterDetuning_int_mul]
    congr 2
  · apply (clockLaw.2 δ).2.congr'
    filter_upwards [] with n
    rw [finiteClockSampledPhaseProbabilityMeasure_mFourier_integral,
      finiteTorusCharacterDetuning_int_mul]
    congr 2
    push_cast
    ring

/-- Every Rajchman clock produces countable-spectrum Rajchman decay on every nonresonant
finite-support ray. -/
theorem countableRajchmanClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (clockLaw : RajchmanClockLaw) (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure clockLaw.1 omega :
        Measure (I → UnitAddCircle)) m.1 := by
  classical
  let δ : {x : ℝ // x ≠ 0} :=
    ⟨infiniteTorusCharacterDetuning m.1 omega, m.2⟩
  refine ⟨inferInstance, ?_, ?_⟩
  · apply (clockLaw.2 δ).1.congr'
    filter_upwards [] with n
    rw [countableClockSampledPhaseProbabilityMeasure_fourier_integral,
      infiniteTorusCharacterDetuning_zsmul]
    congr 2
  · apply (clockLaw.2 δ).2.congr'
    filter_upwards [] with n
    rw [countableClockSampledPhaseProbabilityMeasure_fourier_integral,
      infiniteTorusCharacterDetuning_zsmul]
    congr 2
    push_cast
    ring

/-- Every integrable real probability density samples every finite spectrum with Rajchman decay
on nonresonant rays. -/
theorem finiteRealDensityClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (f : RealProbabilityDensityData) (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure (realProbabilityDensityClock f) energy :
        Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (realProbabilityDensityRajchmanClockLaw f) energy m

/-- Every integrable real probability density samples every countable spectrum with Rajchman decay
on nonresonant finite-support rays. -/
theorem countableRealDensityClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (f : RealProbabilityDensityData) (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure (realProbabilityDensityClock f) omega :
        Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (realProbabilityDensityRajchmanClockLaw f) omega m

/-- Every integrable real probability density suppresses every nonzero finite prime-log character
ray. -/
theorem primeLogRealDensityClockSample_isInfiniteTorusRayRajchman
    (f : RealProbabilityDensityData) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure (realProbabilityDensityClock f)
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (realProbabilityDensityRajchmanClockLaw f)
    (fun p : Nat.Primes => Real.log (p : ℝ))
    ⟨m.1, fun h => m.2
      ((infiniteTorusCharacterDetuning_logPrime_eq_zero_iff m.1).mp h)⟩

/-- Every nondegenerate centered uniform clock is Rajchman. -/
def centeredUniformRajchmanClockLaw (A : {x : ℝ // x ≠ 0}) : RajchmanClockLaw :=
  ⟨centeredUniformClockProbabilityMeasure A.1, fun d => by
    let δ : {x : ℝ // x ≠ 0} :=
      ⟨A.1 * d.1, mul_ne_zero A.2 d.2⟩
    have hpos := tendsto_complex_sinc_nat_mul δ
    constructor
    · apply hpos.congr'
      filter_upwards [] with n
      rw [charFun_centeredUniformClockProbabilityMeasure]
      congr 2
      dsimp only [δ]
      ring
    · have hshift := hpos.comp (tendsto_add_atTop_nat 1)
      apply hshift.congr'
      filter_upwards [] with n
      rw [charFun_centeredUniformClockProbabilityMeasure]
      apply congrArg Complex.ofReal
      rw [← Real.sinc_neg]
      congr 2
      dsimp only [δ]
      push_cast
      ring⟩

/-- Centered triangular clock is Rajchman; its characteristic function is squared sinc. -/
def triangularRajchmanClockLaw : RajchmanClockLaw :=
  ⟨triangularClockProbabilityMeasure, fun d => by
    let δ : {x : ℝ // x ≠ 0} := ⟨d.1 / 2, div_ne_zero d.2 two_ne_zero⟩
    have hpos : Tendsto (fun n : ℕ => (Real.sinc ((n : ℝ) * δ.1) : ℂ) ^ 2)
        atTop (𝓝 0) := by
      simpa using (tendsto_complex_sinc_nat_mul δ).pow 2
    constructor
    · apply hpos.congr'
      filter_upwards [] with n
      rw [charFun_triangularClockProbabilityMeasure]
      congr 2
      dsimp only [δ]
      ring
    · have hshift := hpos.comp (tendsto_add_atTop_nat 1)
      apply hshift.congr'
      filter_upwards [] with n
      simp only [Function.comp_apply]
      rw [charFun_triangularClockProbabilityMeasure]
      push_cast
      apply congrArg (fun z : ℂ => z ^ 2)
      apply congrArg Complex.ofReal
      rw [← Real.sinc_neg]
      apply congrArg Real.sinc
      dsimp only [δ]
      ring⟩

/-- Difference of two independent centered uniforms is a Rajchman clock through its triangular
law identity. -/
def centeredUniformDifferenceRajchmanClockLaw : RajchmanClockLaw := by
  refine ⟨centeredUniformDifferenceProbabilityMeasure, ?_⟩
  intro d
  have hclock : centeredUniformDifferenceProbabilityMeasure =
      triangularClockProbabilityMeasure :=
    ProbabilityMeasure.toMeasure_injective
      centeredUniformDifferenceProbabilityMeasure_eq_triangular
  rw [hclock]
  exact triangularRajchmanClockLaw.2 d

/-- Corpus Möbius critical Laplace-gap density packaged for the general `L¹` clock theorem. -/
def mobiusCriticalLaplaceGapDensityData : RealProbabilityDensityData :=
  ⟨RHTower.mobiusCriticalLaplaceGapDensity,
    RHTower.integrable_mobiusCriticalLaplaceGapDensity,
    RHTower.mobiusCriticalLaplaceGapDensity_nonneg,
    RHTower.integral_mobiusCriticalLaplaceGapDensity⟩

private theorem realDensityClock_mobiusCriticalLaplaceGap_eq :
    realProbabilityDensityClock mobiusCriticalLaplaceGapDensityData =
      RHTower.mobiusCriticalLaplaceGapProbabilityMeasure := by
  apply ProbabilityMeasure.toMeasure_injective
  change realProbabilityDensityMeasure mobiusCriticalLaplaceGapDensityData =
    RHTower.mobiusCriticalLaplaceGapMeasure
  unfold realProbabilityDensityMeasure RHTower.mobiusCriticalLaplaceGapMeasure
  congr 1
  funext x
  exact ENNReal.ofReal_eq_coe_nnreal
    (RHTower.mobiusCriticalLaplaceGapDensity_nonneg x)

/-- Explicit Möbius critical Laplace-gap clock is Rajchman. -/
def mobiusCriticalLaplaceGapRajchmanClockLaw : RajchmanClockLaw := by
  refine ⟨RHTower.mobiusCriticalLaplaceGapProbabilityMeasure, ?_⟩
  rw [← realDensityClock_mobiusCriticalLaplaceGap_eq]
  exact (realProbabilityDensityRajchmanClockLaw
    mobiusCriticalLaplaceGapDensityData).2

/-- Difference of two independent unit-rate exponential critical clocks is Rajchman. -/
def mobiusCriticalExponentialGapRajchmanClockLaw : RajchmanClockLaw := by
  refine ⟨RHTower.mobiusCriticalExponentialGapProbabilityMeasure, ?_⟩
  rw [RHTower.mobiusCriticalExponentialGapProbabilityMeasure_eq_laplace]
  exact mobiusCriticalLaplaceGapRajchmanClockLaw.2

/-- Möbius critical Laplace-gap sampling of every finite spectrum is Rajchman on nonresonant
rays. -/
theorem finiteMobiusLaplaceGapClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        RHTower.mobiusCriticalLaplaceGapProbabilityMeasure energy :
          Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    mobiusCriticalLaplaceGapRajchmanClockLaw energy m

/-- Independent-exponential-gap sampling of every finite spectrum is Rajchman on nonresonant
rays. -/
theorem finiteMobiusExponentialGapClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        RHTower.mobiusCriticalExponentialGapProbabilityMeasure energy :
          Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    mobiusCriticalExponentialGapRajchmanClockLaw energy m

/-- Möbius critical Laplace-gap sampling of every countable spectrum is Rajchman on nonresonant
finite-support rays. -/
theorem countableMobiusLaplaceGapClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        RHTower.mobiusCriticalLaplaceGapProbabilityMeasure omega :
          Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    mobiusCriticalLaplaceGapRajchmanClockLaw omega m

/-- Independent-exponential-gap sampling of every countable spectrum is Rajchman on nonresonant
finite-support rays. -/
theorem countableMobiusExponentialGapClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        RHTower.mobiusCriticalExponentialGapProbabilityMeasure omega :
          Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    mobiusCriticalExponentialGapRajchmanClockLaw omega m

/-- Möbius critical Laplace-gap observation suppresses every nonzero finite prime-log character. -/
theorem primeLogMobiusLaplaceGapClockSample_isInfiniteTorusRayRajchman
    (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        RHTower.mobiusCriticalLaplaceGapProbabilityMeasure
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    mobiusCriticalLaplaceGapRajchmanClockLaw
    (fun p : Nat.Primes => Real.log (p : ℝ))
    ⟨m.1, fun h => m.2
      ((infiniteTorusCharacterDetuning_logPrime_eq_zero_iff m.1).mp h)⟩

/-- Independent-exponential-gap observation suppresses every nonzero finite prime-log character. -/
theorem primeLogMobiusExponentialGapClockSample_isInfiniteTorusRayRajchman
    (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        RHTower.mobiusCriticalExponentialGapProbabilityMeasure
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    mobiusCriticalExponentialGapRajchmanClockLaw
    (fun p : Nat.Primes => Real.log (p : ℝ))
    ⟨m.1, fun h => m.2
      ((infiniteTorusCharacterDetuning_logPrime_eq_zero_iff m.1).mp h)⟩

/-- Triangular-clock sampling of every finite spectrum is Rajchman on each nonresonant ray. -/
theorem finiteTriangularClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure triangularClockProbabilityMeasure energy :
        Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    triangularRajchmanClockLaw energy m

/-- Triangular-clock sampling of every countable spectrum is Rajchman on each nonresonant
finite-support ray. -/
theorem countableTriangularClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure triangularClockProbabilityMeasure omega :
        Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    triangularRajchmanClockLaw omega m

/-- Any Rajchman clock suppresses every nonzero finite prime-log character ray. -/
theorem primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (clockLaw : RajchmanClockLaw) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure clockLaw.1
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 := by
  exact countableRajchmanClockSample_isInfiniteTorusRayRajchman clockLaw
    (fun p : Nat.Primes => Real.log (p : ℝ))
    ⟨m.1, fun h => m.2
      ((infiniteTorusCharacterDetuning_logPrime_eq_zero_iff m.1).mp h)⟩

/-- Triangular observation time suppresses every nonzero finite prime-log character ray. -/
theorem primeLogTriangularClockSample_isInfiniteTorusRayRajchman
    (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure triangularClockProbabilityMeasure
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman triangularRajchmanClockLaw m

/-- Difference-of-uniforms observation time suppresses every nonzero finite prime-log character
ray. -/
theorem primeLogUniformDifferenceClockSample_isInfiniteTorusRayRajchman
    (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        centeredUniformDifferenceProbabilityMeasure
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    centeredUniformDifferenceRajchmanClockLaw m

/-- Uniform-clock sampling of a finite spectrum is Rajchman along every nonresonant character ray. -/
theorem finiteCenteredUniformClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (energy : d → ℝ)
    (A : {x : ℝ // x ≠ 0}) (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        (centeredUniformClockProbabilityMeasure A.1) energy :
          Measure (UnitAddTorus d)) m.1 := by
  classical
  let δ : {x : ℝ // x ≠ 0} :=
    ⟨A.1 * finiteTorusCharacterDetuning m.1 energy, mul_ne_zero A.2 m.2⟩
  have hpos := tendsto_complex_sinc_nat_mul δ
  refine ⟨inferInstance, ?_, ?_⟩
  · apply hpos.congr'
    filter_upwards [] with n
    rw [finiteClockSampledPhaseProbabilityMeasure_mFourier_integral,
      charFun_centeredUniformClockProbabilityMeasure,
      finiteTorusCharacterDetuning_int_mul]
    congr 2
    dsimp only [δ]
    push_cast
    ring
  · have hshift := hpos.comp (tendsto_add_atTop_nat 1)
    apply hshift.congr'
    filter_upwards [] with n
    rw [finiteClockSampledPhaseProbabilityMeasure_mFourier_integral,
      charFun_centeredUniformClockProbabilityMeasure,
      finiteTorusCharacterDetuning_int_mul]
    apply congrArg Complex.ofReal
    rw [← Real.sinc_neg]
    congr 2
    dsimp only [δ]
    push_cast
    ring

/-- A countable spectrum with every individual frequency nonzero. -/
def CoordinatewiseNonzeroCountableSpectrum (I : Type*) :=
  I → {x : ℝ // x ≠ 0}

/-- Uniform-clock sampling of a countable spectrum is Rajchman along every nonresonant
finite-support character ray. -/
theorem countableCenteredUniformClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (omega : I → ℝ)
    (A : {x : ℝ // x ≠ 0}) (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (centeredUniformClockProbabilityMeasure A.1) omega :
          Measure (I → UnitAddCircle)) m.1 := by
  classical
  let δ : {x : ℝ // x ≠ 0} :=
    ⟨A.1 * infiniteTorusCharacterDetuning m.1 omega, mul_ne_zero A.2 m.2⟩
  have hpos := tendsto_complex_sinc_nat_mul δ
  refine ⟨inferInstance, ?_, ?_⟩
  · apply hpos.congr'
    filter_upwards [] with n
    rw [countableClockSampledPhaseProbabilityMeasure_fourier_integral,
      charFun_centeredUniformClockProbabilityMeasure,
      infiniteTorusCharacterDetuning_zsmul]
    congr 2
    dsimp only [δ]
    push_cast
    ring
  · have hshift := hpos.comp (tendsto_add_atTop_nat 1)
    apply hshift.congr'
    filter_upwards [] with n
    rw [countableClockSampledPhaseProbabilityMeasure_fourier_integral,
      charFun_centeredUniformClockProbabilityMeasure,
      infiniteTorusCharacterDetuning_zsmul]
    apply congrArg Complex.ofReal
    rw [← Real.sinc_neg]
    congr 2
    dsimp only [δ]
    push_cast
    ring

/-- Uniform-clock sampling of a countable coordinatewise-nonzero spectrum is Rajchman in every
coordinate. -/
theorem countableCenteredUniformClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (omega : CoordinatewiseNonzeroCountableSpectrum I)
    (A : {x : ℝ // x ≠ 0}) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (centeredUniformClockProbabilityMeasure A.1) (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i := by
  classical
  let δ : {x : ℝ // x ≠ 0} :=
    ⟨A.1 * (omega i).1, mul_ne_zero A.2 (omega i).2⟩
  have hpos := tendsto_complex_sinc_nat_mul δ
  refine ⟨inferInstance, ?_, ?_⟩
  · apply hpos.congr'
    filter_upwards [] with n
    rw [countableClockSampledPhaseProbabilityMeasure_fourier_integral,
      charFun_centeredUniformClockProbabilityMeasure]
    simp [infiniteTorusCharacterDetuning]
    apply congrArg Real.sinc
    dsimp only [δ]
    ring

  · have hshift := hpos.comp (tendsto_add_atTop_nat 1)
    apply hshift.congr'
    filter_upwards [] with n
    rw [countableClockSampledPhaseProbabilityMeasure_fourier_integral,
      charFun_centeredUniformClockProbabilityMeasure]
    simp [infiniteTorusCharacterDetuning]
    rw [← Real.sinc_neg]
    apply congrArg Real.sinc
    dsimp only [δ]
    ring

/-- Centered uniform sampling of ordinary-prime logarithmic phases is Rajchman along every nonzero
finite-support character ray. -/
theorem primeLogCenteredUniformClockSample_isInfiniteTorusRayRajchman
    (A : {x : ℝ // x ≠ 0}) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (centeredUniformClockProbabilityMeasure A.1)
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 := by
  exact countableCenteredUniformClockSample_isInfiniteTorusRayRajchman
    (fun p : Nat.Primes => Real.log (p : ℝ)) A
    ⟨m.1, fun h => m.2
      ((infiniteTorusCharacterDetuning_logPrime_eq_zero_iff m.1).mp h)⟩

/-! ## Corpus probability-density clocks -/

/-- Positive shape parameter for the normalized Gamma-height law. -/
def PositiveGammaHeightShape := {r : ℝ // 0 < r}

/-- Normalized Gamma-height density packaged as nonnegative `L¹` data. -/
def gammaHeightDensityData (r : PositiveGammaHeightShape) :
    RealProbabilityDensityData :=
  ⟨RHTower.gammaHeightDensity r.1,
    RHTower.integrable_gammaHeightDensity r.2,
    RHTower.gammaHeightDensity_nonneg r.2,
    RHTower.integral_gammaHeightDensity_eq_one r.2⟩

/-- Probability clock generated by the normalized Gamma-height density. -/
def gammaHeightClockProbabilityMeasure
    (r : PositiveGammaHeightShape) : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock (gammaHeightDensityData r)

/-- Exact characteristic function of every normalized Gamma-height clock. -/
theorem charFun_gammaHeightClockProbabilityMeasure
    (r : PositiveGammaHeightShape) (t : ℝ) :
    charFun (gammaHeightClockProbabilityMeasure r : Measure ℝ) t =
      ((Real.cosh (t / 2) ^ (-r.1) : ℝ) : ℂ) := by
  rw [gammaHeightClockProbabilityMeasure, charFun_realProbabilityDensityClock]
  convert RHTower.integral_cexp_mul_gammaHeightDensity r.2 t using 1
  apply integral_congr_ae
  filter_upwards [] with s
  congr 2
  push_cast
  ring

/-- Every positive-shape Gamma-height clock is Rajchman. -/
def gammaHeightRajchmanClockLaw (r : PositiveGammaHeightShape) : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw (gammaHeightDensityData r)

/-- Exact finite-spectrum coefficient under Gamma-height time sampling. -/
theorem finiteGammaHeightClockSample_fourier_integral
    {d : Type*} [Fintype d] (r : PositiveGammaHeightShape)
    (energy : d → ℝ) (m : d → ℤ) :
    ∫ x, UnitAddTorus.mFourier m x
        ∂(finiteClockSampledPhaseProbabilityMeasure
          (gammaHeightClockProbabilityMeasure r) energy : Measure (UnitAddTorus d)) =
      ((Real.cosh (finiteTorusCharacterDetuning m energy / 2) ^ (-r.1) : ℝ) : ℂ) := by
  rw [finiteClockSampledPhaseProbabilityMeasure_mFourier_integral,
    charFun_gammaHeightClockProbabilityMeasure]

/-- Exact finite-support coefficient under countable Gamma-height time sampling. -/
theorem countableGammaHeightClockSample_fourier_integral
    {I : Type*} [Countable I] (r : PositiveGammaHeightShape)
    (omega : I → ℝ) (m : I →₀ ℤ) :
    ∫ x, infiniteTorusFourier m x
        ∂(countableClockSampledPhaseProbabilityMeasure
          (gammaHeightClockProbabilityMeasure r) omega : Measure (I → UnitAddCircle)) =
      ((Real.cosh (infiniteTorusCharacterDetuning m omega / 2) ^ (-r.1) : ℝ) : ℂ) := by
  rw [countableClockSampledPhaseProbabilityMeasure_fourier_integral,
    charFun_gammaHeightClockProbabilityMeasure]

/-- Positive-shape Gamma-height sampling is Rajchman on every finite nonresonant ray. -/
theorem finiteGammaHeightClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (r : PositiveGammaHeightShape)
    (energy : d → ℝ) (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        (gammaHeightClockProbabilityMeasure r) energy : Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (gammaHeightRajchmanClockLaw r) energy m

/-- Positive-shape Gamma-height sampling is Rajchman on every countable nonresonant ray. -/
theorem countableGammaHeightClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (r : PositiveGammaHeightShape)
    (omega : I → ℝ) (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (gammaHeightClockProbabilityMeasure r) omega : Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (gammaHeightRajchmanClockLaw r) omega m

/-- Positive-shape Gamma-height observation suppresses every nonzero prime-log character ray. -/
theorem primeLogGammaHeightClockSample_isInfiniteTorusRayRajchman
    (r : PositiveGammaHeightShape) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (gammaHeightClockProbabilityMeasure r)
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (gammaHeightRajchmanClockLaw r) m

/-- Sonin semilocal Archimedean Gamma density as normalized nonnegative `L¹` data. -/
def semilocalArchimedeanGammaDensityData : RealProbabilityDensityData :=
  ⟨RHTower.semilocalArchimedeanGammaDensity,
    RHTower.integrable_semilocalArchimedeanGammaDensity,
    RHTower.semilocalArchimedeanGammaDensity_nonneg,
    RHTower.integral_semilocalArchimedeanGammaDensity_eq_one⟩

/-- Probability clock generated by the Sonin semilocal Archimedean Gamma density. -/
def semilocalArchimedeanGammaClockProbabilityMeasure : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock semilocalArchimedeanGammaDensityData

/-- Exact characteristic function of the Sonin semilocal Archimedean Gamma clock. -/
theorem charFun_semilocalArchimedeanGammaClockProbabilityMeasure (t : ℝ) :
    charFun (semilocalArchimedeanGammaClockProbabilityMeasure : Measure ℝ) t =
      (RHTower.semilocalArchimedeanCharacteristic t : ℂ) := by
  rw [semilocalArchimedeanGammaClockProbabilityMeasure,
    charFun_realProbabilityDensityClock]
  convert RHTower.integral_cexp_mul_semilocalArchimedeanGammaDensity t using 1
  apply integral_congr_ae
  filter_upwards [] with s
  congr 2
  push_cast
  ring

/-- Sonin semilocal Archimedean Gamma clock is Rajchman. -/
def semilocalArchimedeanGammaRajchmanClockLaw : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw semilocalArchimedeanGammaDensityData

/-- Exact finite-spectrum coefficient under Sonin semilocal Gamma time sampling. -/
theorem finiteSemilocalGammaClockSample_fourier_integral
    {d : Type*} [Fintype d] (energy : d → ℝ) (m : d → ℤ) :
    ∫ x, UnitAddTorus.mFourier m x
        ∂(finiteClockSampledPhaseProbabilityMeasure
          semilocalArchimedeanGammaClockProbabilityMeasure energy : Measure (UnitAddTorus d)) =
      (RHTower.semilocalArchimedeanCharacteristic
        (finiteTorusCharacterDetuning m energy) : ℂ) := by
  rw [finiteClockSampledPhaseProbabilityMeasure_mFourier_integral,
    charFun_semilocalArchimedeanGammaClockProbabilityMeasure]

/-- Exact countable finite-support coefficient under Sonin semilocal Gamma time sampling. -/
theorem countableSemilocalGammaClockSample_fourier_integral
    {I : Type*} [Countable I] (omega : I → ℝ) (m : I →₀ ℤ) :
    ∫ x, infiniteTorusFourier m x
        ∂(countableClockSampledPhaseProbabilityMeasure
          semilocalArchimedeanGammaClockProbabilityMeasure omega :
            Measure (I → UnitAddCircle)) =
      (RHTower.semilocalArchimedeanCharacteristic
        (infiniteTorusCharacterDetuning m omega) : ℂ) := by
  rw [countableClockSampledPhaseProbabilityMeasure_fourier_integral,
    charFun_semilocalArchimedeanGammaClockProbabilityMeasure]

/-- Sonin semilocal Gamma sampling is Rajchman on every finite nonresonant ray. -/
theorem finiteSemilocalGammaClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        semilocalArchimedeanGammaClockProbabilityMeasure energy :
          Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    semilocalArchimedeanGammaRajchmanClockLaw energy m

/-- Sonin semilocal Gamma sampling is Rajchman on every countable nonresonant ray. -/
theorem countableSemilocalGammaClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        semilocalArchimedeanGammaClockProbabilityMeasure omega :
          Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    semilocalArchimedeanGammaRajchmanClockLaw omega m

/-- Sonin semilocal Gamma observation suppresses every nonzero prime-log character ray. -/
theorem primeLogSemilocalGammaClockSample_isInfiniteTorusRayRajchman
    (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        semilocalArchimedeanGammaClockProbabilityMeasure
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    semilocalArchimedeanGammaRajchmanClockLaw m

/-- Logistic cutoff-derivative kernel as normalized nonnegative `L¹` data. -/
def logisticKernelDensityData : RealProbabilityDensityData :=
  ⟨RHTower.logisticKernel,
    RHTower.integrable_logisticKernel,
    fun t => (RHTower.logisticKernel_pos t).le,
    RHTower.integral_logisticKernel⟩

/-- Probability clock generated by the logistic cutoff-derivative kernel. -/
def logisticKernelClockProbabilityMeasure : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock logisticKernelDensityData

/-- Logistic cutoff-derivative clock is Rajchman. -/
def logisticKernelRajchmanClockLaw : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw logisticKernelDensityData

/-- Logistic cutoff sampling is Rajchman on every finite nonresonant ray. -/
theorem finiteLogisticKernelClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        logisticKernelClockProbabilityMeasure energy : Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    logisticKernelRajchmanClockLaw energy m

/-- Logistic cutoff sampling is Rajchman on every countable nonresonant ray. -/
theorem countableLogisticKernelClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        logisticKernelClockProbabilityMeasure omega : Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    logisticKernelRajchmanClockLaw omega m

/-- Logistic cutoff observation suppresses every nonzero prime-log character ray. -/
theorem primeLogLogisticKernelClockSample_isInfiniteTorusRayRajchman
    (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure logisticKernelClockProbabilityMeasure
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    logisticKernelRajchmanClockLaw m

/-- Off-axis point whose Connes harmonic measure has a genuine Poisson density. -/
def OffImaginaryAxisPoint := {ρ : ℂ // ρ.re ≠ 0}

/-- Connes off-axis harmonic density packaged as normalized nonnegative `L¹` data. -/
def connesHarmonicDensityData (ρ : OffImaginaryAxisPoint) :
    RealProbabilityDensityData :=
  ⟨RHTower.connesHarmonicDensity ρ.1,
    RHTower.connes_harmonicDensity_integrable ρ.2,
    RHTower.connesHarmonicDensity_nonneg ρ.2,
    RHTower.connes_harmonicDensity_integral ρ.2⟩

/-- Probability clock generated by Connes harmonic measure off the imaginary axis. -/
def connesHarmonicClockProbabilityMeasure
    (ρ : OffImaginaryAxisPoint) : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock (connesHarmonicDensityData ρ)

/-- Every off-axis Connes harmonic-measure clock is Rajchman. -/
def connesHarmonicRajchmanClockLaw
    (ρ : OffImaginaryAxisPoint) : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw (connesHarmonicDensityData ρ)

/-- Connes harmonic timing is Rajchman on every finite nonresonant ray. -/
theorem finiteConnesHarmonicClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (ρ : OffImaginaryAxisPoint)
    (energy : d → ℝ) (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        (connesHarmonicClockProbabilityMeasure ρ) energy : Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (connesHarmonicRajchmanClockLaw ρ) energy m

/-- Connes harmonic timing is Rajchman on every countable nonresonant ray. -/
theorem countableConnesHarmonicClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (ρ : OffImaginaryAxisPoint)
    (omega : I → ℝ) (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (connesHarmonicClockProbabilityMeasure ρ) omega :
          Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (connesHarmonicRajchmanClockLaw ρ) omega m

/-- Connes harmonic timing suppresses every nonzero prime-log character ray. -/
theorem primeLogConnesHarmonicClockSample_isInfiniteTorusRayRajchman
    (ρ : OffImaginaryAxisPoint) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (connesHarmonicClockProbabilityMeasure ρ)
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (connesHarmonicRajchmanClockLaw ρ) m

/-- Every compact Wigner--Smith resolution packet is normalized nonnegative `L¹` data. -/
def compactPacketDensityData (ε : ℝ) : RealProbabilityDensityData :=
  ⟨compactPacketDensity ε,
    integrable_compactPacketDensity ε,
    compactPacketDensity_nonneg ε,
    integral_compactPacketDensity ε⟩

/-- Probability clock generated by a compact Wigner--Smith resolution packet. -/
def compactPacketClockProbabilityMeasure (ε : ℝ) : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock (compactPacketDensityData ε)

/-- Every compact Wigner--Smith resolution packet is a Rajchman clock. -/
def compactPacketRajchmanClockLaw (ε : ℝ) : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw (compactPacketDensityData ε)

/-- Compact Wigner--Smith packet timing is Rajchman on every finite nonresonant ray. -/
theorem finiteCompactPacketClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (ε : ℝ) (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        (compactPacketClockProbabilityMeasure ε) energy : Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (compactPacketRajchmanClockLaw ε) energy m

/-- Compact Wigner--Smith packet timing is Rajchman on every countable nonresonant ray. -/
theorem countableCompactPacketClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (ε : ℝ) (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (compactPacketClockProbabilityMeasure ε) omega : Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (compactPacketRajchmanClockLaw ε) omega m

/-- Compact Wigner--Smith packet timing suppresses every nonzero prime-log character ray. -/
theorem primeLogCompactPacketClockSample_isInfiniteTorusRayRajchman
    (ε : ℝ) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (compactPacketClockProbabilityMeasure ε)
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (compactPacketRajchmanClockLaw ε) m

/-- Julia-compression Lévy jump density as normalized nonnegative `L¹` data. -/
def juliaCompressionJumpDensityData : RealProbabilityDensityData :=
  ⟨_root_.HTGeometry.juliaCompressionJumpDensity,
    _root_.HTGeometry.integrable_juliaCompressionJumpDensity,
    _root_.HTGeometry.juliaCompressionJumpDensity_nonneg,
    _root_.HTGeometry.integral_juliaCompressionJumpDensity⟩

/-- Probability clock generated by the Julia-compression jump density. -/
def juliaCompressionJumpClockProbabilityMeasure : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock juliaCompressionJumpDensityData

/-- Julia-compression jump clock is Rajchman. -/
def juliaCompressionJumpRajchmanClockLaw : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw juliaCompressionJumpDensityData

/-- Julia-compression jump timing is Rajchman on every finite nonresonant ray. -/
theorem finiteJuliaCompressionJumpClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        juliaCompressionJumpClockProbabilityMeasure energy : Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    juliaCompressionJumpRajchmanClockLaw energy m

/-- Julia-compression jump timing is Rajchman on every countable nonresonant ray. -/
theorem countableJuliaCompressionJumpClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        juliaCompressionJumpClockProbabilityMeasure omega : Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    juliaCompressionJumpRajchmanClockLaw omega m

/-- Julia-compression jump timing suppresses every nonzero prime-log character ray. -/
theorem primeLogJuliaCompressionJumpClockSample_isInfiniteTorusRayRajchman
    (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        juliaCompressionJumpClockProbabilityMeasure
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    juliaCompressionJumpRajchmanClockLaw m

/-- Probability-density data carried on the positive half-line. -/
def PositiveHalfLineProbabilityDensityData :=
  {f : ℝ → ℝ // IntegrableOn f (Ioi (0 : ℝ)) ∧
    (∀ x, 0 < x → 0 ≤ f x) ∧ ∫ x in Ioi (0 : ℝ), f x = 1}

/-- Extend positive-half-line density data by zero to the whole real line. -/
def positiveHalfLineDensityExtension
    (f : PositiveHalfLineProbabilityDensityData) : ℝ → ℝ :=
  (Ioi (0 : ℝ)).indicator f.1

/-- Zero extension turns positive-half-line probability-density data into whole-line data. -/
def positiveHalfLineProbabilityDensityData
    (f : PositiveHalfLineProbabilityDensityData) : RealProbabilityDensityData := by
  refine ⟨positiveHalfLineDensityExtension f, ?_, ?_, ?_⟩
  · exact f.2.1.integrable_indicator measurableSet_Ioi
  · intro x
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · simp only [positiveHalfLineDensityExtension, indicator_of_mem hx]
      exact f.2.2.1 x hx
    · simp [positiveHalfLineDensityExtension, hx]
  · rw [positiveHalfLineDensityExtension, integral_indicator measurableSet_Ioi]
    exact f.2.2.2

/-- Theta-cusp second-tail curvature density packaged on its natural positive half-line. -/
def thetaCuspTailSecondHalfLineDensityData :
    PositiveHalfLineProbabilityDensityData := by
  refine ⟨RHTower.thetaCuspTailSecondDensity, ?_, ?_,
    RHTower.integral_thetaCuspTailSecondDensity⟩
  · have h := RHTower.integrableOn_thetaCuspTailSecondDensity_complex.re
    change Integrable RHTower.thetaCuspTailSecondDensity
      (volume.restrict (Ioi (0 : ℝ)))
    simpa using h
  · intro x hx
    exact (RHTower.thetaCuspTailSecondDensity_pos hx).le

/-- Whole-line zero extension of the normalized theta-cusp second-tail density. -/
def thetaCuspTailSecondDensityData : RealProbabilityDensityData :=
  positiveHalfLineProbabilityDensityData thetaCuspTailSecondHalfLineDensityData

/-- Probability clock generated by the normalized theta-cusp second-tail density. -/
def thetaCuspTailSecondClockProbabilityMeasure : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock thetaCuspTailSecondDensityData

/-- Theta-cusp second-tail clock is Rajchman. -/
def thetaCuspTailSecondRajchmanClockLaw : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw thetaCuspTailSecondDensityData

/-- Theta-cusp second-tail timing is Rajchman on every finite nonresonant ray. -/
theorem finiteThetaCuspTailSecondClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        thetaCuspTailSecondClockProbabilityMeasure energy : Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    thetaCuspTailSecondRajchmanClockLaw energy m

/-- Theta-cusp second-tail timing is Rajchman on every countable nonresonant ray. -/
theorem countableThetaCuspTailSecondClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        thetaCuspTailSecondClockProbabilityMeasure omega : Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    thetaCuspTailSecondRajchmanClockLaw omega m

/-- Theta-cusp second-tail timing suppresses every nonzero prime-log character ray. -/
theorem primeLogThetaCuspTailSecondClockSample_isInfiniteTorusRayRajchman
    (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        thetaCuspTailSecondClockProbabilityMeasure
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    thetaCuspTailSecondRajchmanClockLaw m

/-- Whole-line extension of the connected Suzuki third-multiplier mixing density on `(0,1]`. -/
def connectedThirdMixingDensity (t : ℝ) : ℝ :=
  (Ioc (0 : ℝ) 1).indicator (fun s => 3 * (1 - s) ^ 2) t

/-- Connected Suzuki third-multiplier mixture as normalized nonnegative `L¹` data. -/
def connectedThirdMixingDensityData : RealProbabilityDensityData := by
  refine ⟨connectedThirdMixingDensity, ?_, ?_, ?_⟩
  · have hcont : Continuous (fun t : ℝ => 3 * (1 - t) ^ 2) := by fun_prop
    have hIcc : IntegrableOn (fun t : ℝ => 3 * (1 - t) ^ 2)
        (Icc (0 : ℝ) 1) volume := hcont.integrableOn_Icc
    exact (hIcc.mono_set Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc
  · intro t
    by_cases ht : t ∈ Ioc (0 : ℝ) 1
    · simp only [connectedThirdMixingDensity, indicator_of_mem ht]
      positivity
    · simp [connectedThirdMixingDensity, ht]
  · unfold connectedThirdMixingDensity
    rw [integral_indicator measurableSet_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact RHTower.integral_shiftedEulerLogConnectedThirdMultiplier_mixingDensity

/-- Probability clock generated by the connected Suzuki third-multiplier mixture. -/
def connectedThirdMixingClockProbabilityMeasure : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock connectedThirdMixingDensityData

/-- Connected Suzuki third-multiplier mixing clock is Rajchman. -/
def connectedThirdMixingRajchmanClockLaw : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw connectedThirdMixingDensityData

/-- Connected-third-multiplier timing is Rajchman on every finite nonresonant ray. -/
theorem finiteConnectedThirdMixingClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure connectedThirdMixingClockProbabilityMeasure
        energy : Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    connectedThirdMixingRajchmanClockLaw energy m

/-- Connected-third-multiplier timing is Rajchman on every countable nonresonant ray. -/
theorem countableConnectedThirdMixingClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure connectedThirdMixingClockProbabilityMeasure
        omega : Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    connectedThirdMixingRajchmanClockLaw omega m

/-- Connected-third-multiplier timing suppresses every nonzero prime-log character ray. -/
theorem primeLogConnectedThirdMixingClockSample_isInfiniteTorusRayRajchman
    (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure connectedThirdMixingClockProbabilityMeasure
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    connectedThirdMixingRajchmanClockLaw m

/-- Normalized whole-line extension of twice the CCM exterior radial profile density. -/
def normalizedRadialProfileDensity (x : ℝ) : ℝ :=
  (Ioi (1 : ℝ)).indicator (fun y => 2 * RHTower.profileDensity y) x

/-- Twice the CCM exterior radial profile as normalized nonnegative `L¹` data. -/
def normalizedRadialProfileDensityData : RealProbabilityDensityData := by
  refine ⟨normalizedRadialProfileDensity, ?_, ?_, ?_⟩
  · have h : IntegrableOn (fun y : ℝ => 2 * RHTower.profileDensity y)
        (Ioi (1 : ℝ)) volume := RHTower.integrableOn_profileDensity.const_mul 2
    exact h.integrable_indicator measurableSet_Ioi
  · intro x
    by_cases hx : x ∈ Ioi (1 : ℝ)
    · simp only [normalizedRadialProfileDensity, indicator_of_mem hx]
      exact mul_nonneg (by norm_num) (RHTower.profileDensity_nonneg hx.le)
    · simp [normalizedRadialProfileDensity, hx]
  · unfold normalizedRadialProfileDensity
    rw [integral_indicator measurableSet_Ioi, integral_const_mul,
      RHTower.integral_Ioi_profileDensity]
    norm_num

/-- Probability clock generated by the normalized CCM exterior radial profile. -/
def normalizedRadialProfileClockProbabilityMeasure : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock normalizedRadialProfileDensityData

/-- Normalized CCM exterior radial-profile clock is Rajchman. -/
def normalizedRadialProfileRajchmanClockLaw : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw normalizedRadialProfileDensityData

/-- Normalized radial-profile timing is Rajchman on every finite nonresonant ray. -/
theorem finiteNormalizedRadialProfileClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure normalizedRadialProfileClockProbabilityMeasure
        energy : Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    normalizedRadialProfileRajchmanClockLaw energy m

/-- Normalized radial-profile timing is Rajchman on every countable nonresonant ray. -/
theorem countableNormalizedRadialProfileClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure normalizedRadialProfileClockProbabilityMeasure
        omega : Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    normalizedRadialProfileRajchmanClockLaw omega m

/-- Normalized radial-profile timing suppresses every nonzero prime-log character ray. -/
theorem primeLogNormalizedRadialProfileClockSample_isInfiniteTorusRayRajchman
    (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure normalizedRadialProfileClockProbabilityMeasure
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    normalizedRadialProfileRajchmanClockLaw m

/-- Normalized Cauchy density centered at a Suzuki real spectral node. -/
def suzukiShiftedCauchyDensity (a x : ℝ) : ℝ :=
  Real.pi⁻¹ * (1 + (x - a) ^ 2)⁻¹

/-- Every shifted Suzuki Cauchy density is normalized nonnegative `L¹` data. -/
def suzukiShiftedCauchyDensityData (a : ℝ) : RealProbabilityDensityData := by
  refine ⟨suzukiShiftedCauchyDensity a, ?_, ?_, ?_⟩
  · exact (RiemannGaussian.integrable_suzukiShiftedCauchyDensity a).const_mul Real.pi⁻¹
  · intro x
    unfold suzukiShiftedCauchyDensity
    positivity
  · unfold suzukiShiftedCauchyDensity
    rw [integral_const_mul, RiemannGaussian.integral_suzukiShiftedCauchyDensity]
    exact inv_mul_cancel₀ Real.pi_ne_zero

/-- Probability clock generated by a shifted Suzuki Cauchy density. -/
def suzukiShiftedCauchyClockProbabilityMeasure (a : ℝ) : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock (suzukiShiftedCauchyDensityData a)

/-- Every shifted Suzuki Cauchy clock is Rajchman. -/
def suzukiShiftedCauchyRajchmanClockLaw (a : ℝ) : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw (suzukiShiftedCauchyDensityData a)

/-- Shifted Suzuki Cauchy timing is Rajchman on every finite nonresonant ray. -/
theorem finiteSuzukiShiftedCauchyClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (a : ℝ) (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        (suzukiShiftedCauchyClockProbabilityMeasure a) energy :
          Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (suzukiShiftedCauchyRajchmanClockLaw a) energy m

/-- Shifted Suzuki Cauchy timing is Rajchman on every countable nonresonant ray. -/
theorem countableSuzukiShiftedCauchyClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (a : ℝ) (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (suzukiShiftedCauchyClockProbabilityMeasure a) omega :
          Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (suzukiShiftedCauchyRajchmanClockLaw a) omega m

/-- Shifted Suzuki Cauchy timing suppresses every nonzero prime-log character ray. -/
theorem primeLogSuzukiShiftedCauchyClockSample_isInfiniteTorusRayRajchman
    (a : ℝ) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (suzukiShiftedCauchyClockProbabilityMeasure a)
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (suzukiShiftedCauchyRajchmanClockLaw a) m

/-! ## Gamma--Meixner seam clocks -/

/-- Positive convolution time for the Gamma--Meixner seam law.  Packaging positivity rules out
the time-zero Dirac law, whose Fourier transform does not decay. -/
def PositiveMeixnerConvolutionTime := {theta : ℝ // 0 < theta}

/-- Gamma--Meixner seam density packaged as normalized nonnegative `L¹` data. -/
def meixnerDensityData (theta : PositiveMeixnerConvolutionTime) :
    RealProbabilityDensityData :=
  ⟨RHTower.meixnerDensity theta.1,
    RHTower.integrable_meixnerDensity theta.2,
    RHTower.meixnerDensity_nonneg theta.2,
    RHTower.integral_meixnerDensity_eq_one theta.2⟩

/-- Probability clock generated by the positive-time Gamma--Meixner seam density. -/
def meixnerClockProbabilityMeasure
    (theta : PositiveMeixnerConvolutionTime) : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock (meixnerDensityData theta)

/-- Exact characteristic function of the Gamma--Meixner seam clock. -/
theorem charFun_meixnerClockProbabilityMeasure
    (theta : PositiveMeixnerConvolutionTime) (t : ℝ) :
    charFun (meixnerClockProbabilityMeasure theta : Measure ℝ) t =
      (RHTower.meixnerChar theta.1 t : ℂ) := by
  rw [meixnerClockProbabilityMeasure, charFun_realProbabilityDensityClock]
  convert RHTower.integral_cexp_mul_meixnerDensity theta.2 t using 1
  apply integral_congr_ae
  filter_upwards [] with s
  congr 2
  push_cast
  ring

/-- Every positive-time Gamma--Meixner seam clock is Rajchman. -/
def meixnerRajchmanClockLaw
    (theta : PositiveMeixnerConvolutionTime) : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw (meixnerDensityData theta)

/-- Exact finite-spectrum coefficient under Gamma--Meixner time sampling. -/
theorem finiteMeixnerClockSample_fourier_integral
    {d : Type*} [Fintype d] (theta : PositiveMeixnerConvolutionTime)
    (energy : d → ℝ) (m : d → ℤ) :
    ∫ x, UnitAddTorus.mFourier m x
        ∂(finiteClockSampledPhaseProbabilityMeasure
          (meixnerClockProbabilityMeasure theta) energy : Measure (UnitAddTorus d)) =
      (RHTower.meixnerChar theta.1 (finiteTorusCharacterDetuning m energy) : ℂ) := by
  rw [finiteClockSampledPhaseProbabilityMeasure_mFourier_integral,
    charFun_meixnerClockProbabilityMeasure]

/-- Exact finite-support coefficient under countable Gamma--Meixner time sampling. -/
theorem countableMeixnerClockSample_fourier_integral
    {I : Type*} [Countable I] (theta : PositiveMeixnerConvolutionTime)
    (omega : I → ℝ) (m : I →₀ ℤ) :
    ∫ x, infiniteTorusFourier m x
        ∂(countableClockSampledPhaseProbabilityMeasure
          (meixnerClockProbabilityMeasure theta) omega : Measure (I → UnitAddCircle)) =
      (RHTower.meixnerChar theta.1 (infiniteTorusCharacterDetuning m omega) : ℂ) := by
  rw [countableClockSampledPhaseProbabilityMeasure_fourier_integral,
    charFun_meixnerClockProbabilityMeasure]

/-- Any Rajchman clock makes every nonzero-frequency coordinate of a sampled countable spectrum
Rajchman. -/
theorem countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (clockLaw : RajchmanClockLaw)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure clockLaw.1
        (fun j => (omega j).1) : Measure (I → UnitAddCircle)) i := by
  classical
  refine ⟨inferInstance, ?_, ?_⟩
  · apply (clockLaw.2 (omega i)).1.congr'
    filter_upwards [] with n
    rw [countableClockSampledPhaseProbabilityMeasure_fourier_integral]
    simp [infiniteTorusCharacterDetuning]
  · apply (clockLaw.2 (omega i)).2.congr'
    filter_upwards [] with n
    rw [countableClockSampledPhaseProbabilityMeasure_fourier_integral]
    simp [infiniteTorusCharacterDetuning]

/-- Every whole-line probability density makes every nonzero-frequency sampled coordinate
Rajchman. -/
theorem countableRealDensityClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (f : RealProbabilityDensityData)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure (realProbabilityDensityClock f)
        (fun j => (omega j).1) : Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (realProbabilityDensityRajchmanClockLaw f) omega i

/-- Prime logarithms packaged as a coordinatewise-nonzero countable spectrum. -/
def primeLogCoordinatewiseNonzeroSpectrum :
    CoordinatewiseNonzeroCountableSpectrum Nat.Primes :=
  fun p => ⟨Real.log (p : ℝ), ne_of_gt (Real.log_pos (by
    exact_mod_cast p.2.one_lt))⟩

/-- Every Rajchman clock makes each individual prime-log coordinate Rajchman. -/
theorem primeLogRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (clockLaw : RajchmanClockLaw) (p : Nat.Primes) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure clockLaw.1
        (fun q : Nat.Primes => Real.log (q : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) p :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    clockLaw primeLogCoordinatewiseNonzeroSpectrum p

/-- Gamma-height timing makes every nonzero-frequency sampled coordinate Rajchman. -/
theorem countableGammaHeightClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (r : PositiveGammaHeightShape)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (gammaHeightClockProbabilityMeasure r) (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (gammaHeightRajchmanClockLaw r) omega i

/-- Sonin semilocal Gamma timing makes every nonzero-frequency sampled coordinate Rajchman. -/
theorem countableSemilocalGammaClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I]
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        semilocalArchimedeanGammaClockProbabilityMeasure (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    semilocalArchimedeanGammaRajchmanClockLaw omega i

/-- Logistic cutoff timing makes every nonzero-frequency sampled coordinate Rajchman. -/
theorem countableLogisticKernelClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I]
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        logisticKernelClockProbabilityMeasure (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    logisticKernelRajchmanClockLaw omega i

/-- Connes harmonic timing makes every nonzero-frequency sampled coordinate Rajchman. -/
theorem countableConnesHarmonicClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (ρ : OffImaginaryAxisPoint)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (connesHarmonicClockProbabilityMeasure ρ) (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (connesHarmonicRajchmanClockLaw ρ) omega i

/-- Compact Wigner--Smith timing makes every nonzero-frequency sampled coordinate Rajchman. -/
theorem countableCompactPacketClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (ε : ℝ)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (compactPacketClockProbabilityMeasure ε) (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (compactPacketRajchmanClockLaw ε) omega i

/-- Julia-compression jump timing makes every nonzero-frequency sampled coordinate Rajchman. -/
theorem countableJuliaCompressionJumpClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I]
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        juliaCompressionJumpClockProbabilityMeasure (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    juliaCompressionJumpRajchmanClockLaw omega i

/-- Theta-cusp second-tail timing makes every nonzero-frequency sampled coordinate Rajchman. -/
theorem countableThetaCuspTailSecondClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I]
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        thetaCuspTailSecondClockProbabilityMeasure (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    thetaCuspTailSecondRajchmanClockLaw omega i

/-- Triangular timing makes every nonzero-frequency sampled coordinate Rajchman. -/
theorem countableTriangularClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I]
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure triangularClockProbabilityMeasure
        (fun j => (omega j).1) : Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    triangularRajchmanClockLaw omega i

/-- Difference-of-uniforms timing makes every nonzero-frequency sampled coordinate Rajchman. -/
theorem countableUniformDifferenceClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I]
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        centeredUniformDifferenceProbabilityMeasure (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    centeredUniformDifferenceRajchmanClockLaw omega i

/-- Möbius critical Laplace-gap timing makes every nonzero-frequency coordinate Rajchman. -/
theorem countableMobiusLaplaceGapClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I]
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        RHTower.mobiusCriticalLaplaceGapProbabilityMeasure (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    mobiusCriticalLaplaceGapRajchmanClockLaw omega i

/-- Independent-exponential-gap timing makes every nonzero-frequency coordinate Rajchman. -/
theorem countableMobiusExponentialGapClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I]
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        RHTower.mobiusCriticalExponentialGapProbabilityMeasure (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    mobiusCriticalExponentialGapRajchmanClockLaw omega i

/-- Connected-third-multiplier timing makes every nonzero-frequency coordinate Rajchman. -/
theorem countableConnectedThirdMixingClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I]
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure connectedThirdMixingClockProbabilityMeasure
        (fun j => (omega j).1) : Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    connectedThirdMixingRajchmanClockLaw omega i

/-- Normalized radial-profile timing makes every nonzero-frequency coordinate Rajchman. -/
theorem countableNormalizedRadialProfileClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I]
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure normalizedRadialProfileClockProbabilityMeasure
        (fun j => (omega j).1) : Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    normalizedRadialProfileRajchmanClockLaw omega i

/-- Shifted Suzuki Cauchy timing makes every nonzero-frequency coordinate Rajchman. -/
theorem countableSuzukiShiftedCauchyClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (a : ℝ)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (suzukiShiftedCauchyClockProbabilityMeasure a) (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (suzukiShiftedCauchyRajchmanClockLaw a) omega i

/-! ### Atomlessness inherited from density representation -/

/-- Gamma-height clocks have no atoms. -/
theorem gammaHeightClockProbabilityMeasure_nullSingletonClass
    (r : PositiveGammaHeightShape) :
    NullSingletonClass (gammaHeightClockProbabilityMeasure r : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass (gammaHeightDensityData r)

/-- Sonin semilocal Gamma clock has no atoms. -/
theorem semilocalArchimedeanGammaClockProbabilityMeasure_nullSingletonClass :
    NullSingletonClass
      (semilocalArchimedeanGammaClockProbabilityMeasure : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass
    semilocalArchimedeanGammaDensityData

/-- Logistic cutoff-derivative clock has no atoms. -/
theorem logisticKernelClockProbabilityMeasure_nullSingletonClass :
    NullSingletonClass (logisticKernelClockProbabilityMeasure : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass logisticKernelDensityData

/-- Every off-axis Connes harmonic clock has no atoms. -/
theorem connesHarmonicClockProbabilityMeasure_nullSingletonClass
    (ρ : OffImaginaryAxisPoint) :
    NullSingletonClass (connesHarmonicClockProbabilityMeasure ρ : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass (connesHarmonicDensityData ρ)

/-- Every compact Wigner--Smith resolution clock has no atoms. -/
theorem compactPacketClockProbabilityMeasure_nullSingletonClass (ε : ℝ) :
    NullSingletonClass (compactPacketClockProbabilityMeasure ε : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass (compactPacketDensityData ε)

/-- Julia-compression jump clock has no atoms. -/
theorem juliaCompressionJumpClockProbabilityMeasure_nullSingletonClass :
    NullSingletonClass (juliaCompressionJumpClockProbabilityMeasure : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass juliaCompressionJumpDensityData

/-- Theta-cusp second-tail clock has no atoms. -/
theorem thetaCuspTailSecondClockProbabilityMeasure_nullSingletonClass :
    NullSingletonClass (thetaCuspTailSecondClockProbabilityMeasure : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass thetaCuspTailSecondDensityData

/-- Every positive-time Gamma--Meixner seam clock has no atoms. -/
theorem meixnerClockProbabilityMeasure_nullSingletonClass
    (theta : PositiveMeixnerConvolutionTime) :
    NullSingletonClass (meixnerClockProbabilityMeasure theta : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass (meixnerDensityData theta)

/-- Connected Suzuki third-multiplier mixing clock has no atoms. -/
theorem connectedThirdMixingClockProbabilityMeasure_nullSingletonClass :
    NullSingletonClass (connectedThirdMixingClockProbabilityMeasure : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass connectedThirdMixingDensityData

/-- Normalized CCM radial-profile clock has no atoms. -/
theorem normalizedRadialProfileClockProbabilityMeasure_nullSingletonClass :
    NullSingletonClass (normalizedRadialProfileClockProbabilityMeasure : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass normalizedRadialProfileDensityData

/-- Every shifted Suzuki Cauchy clock has no atoms. -/
theorem suzukiShiftedCauchyClockProbabilityMeasure_nullSingletonClass (a : ℝ) :
    NullSingletonClass (suzukiShiftedCauchyClockProbabilityMeasure a : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass (suzukiShiftedCauchyDensityData a)

/-- Corpus Möbius critical Laplace-gap clock has no atoms. -/
theorem mobiusCriticalLaplaceGapProbabilityMeasure_nullSingletonClass :
    NullSingletonClass
      (RHTower.mobiusCriticalLaplaceGapProbabilityMeasure : Measure ℝ) := by
  rw [← realDensityClock_mobiusCriticalLaplaceGap_eq]
  exact realProbabilityDensityClock_nullSingletonClass
    mobiusCriticalLaplaceGapDensityData

/-- Independent-exponential-gap critical clock has no atoms. -/
theorem mobiusCriticalExponentialGapProbabilityMeasure_nullSingletonClass :
    NullSingletonClass
      (RHTower.mobiusCriticalExponentialGapProbabilityMeasure : Measure ℝ) := by
  rw [RHTower.mobiusCriticalExponentialGapProbabilityMeasure_eq_laplace]
  exact mobiusCriticalLaplaceGapProbabilityMeasure_nullSingletonClass

/-! ### Julia equilibrium-defect inverse-square decay -/

/-- Julia square-defect numerator is bounded by one. -/
theorem juliaDefectSquareProfile_le_one (y : ℝ) :
    _root_.HTGeometry.juliaDefectSquareProfile y ≤ 1 := by
  rw [_root_.HTGeometry.juliaDefectSquareProfile]
  exact sub_le_self 1 (inv_nonneg.mpr (Real.sqrt_nonneg _))

/-- Quantitative inverse-square bound for the Julia equilibrium-defect characteristic function. -/
theorem norm_juliaDefectAttenuationKernel_le_invSq
    {y : ℝ} (hy : y ≠ 0) :
    ‖((_root_.HTGeometry.juliaDefectAttenuationKernel y : ℝ) : ℂ)‖ ≤
      (4 / 3 : ℝ) / y ^ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (_root_.HTGeometry.juliaDefectAttenuationKernel_pos y),
    _root_.HTGeometry.juliaDefectAttenuationKernel_eq_profile hy,
    _root_.HTGeometry.juliaDefectAttenuationProfile]
  apply div_le_div_of_nonneg_right _ (sq_nonneg y)
  simpa only [mul_one] using
    (mul_le_mul_of_nonneg_left (juliaDefectSquareProfile_le_one y)
      (by norm_num : (0 : ℝ) ≤ 4 / 3))

/-- Julia equilibrium-defect attenuation vanishes along every nonzero positive integer ray. -/
theorem tendsto_juliaDefectAttenuationKernel_nat_mul
    (d : {x : ℝ // x ≠ 0}) :
    Tendsto (fun n : ℕ =>
      ((_root_.HTGeometry.juliaDefectAttenuationKernel ((n : ℝ) * d.1) : ℝ) : ℂ))
      atTop (nhds 0) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) atTop (nhds 0) := by
    have hbase : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (nhds 0) :=
      tendsto_natCast_atTop_atTop.inv_tendsto_atTop
    simpa using hbase.pow 2
  have hmajor : Tendsto (fun n : ℕ =>
      (4 / 3 : ℝ) / (((n : ℝ) * d.1) ^ 2)) atTop (nhds 0) := by
    have h : Tendsto (fun n : ℕ =>
        ((4 / 3 : ℝ) / d.1 ^ 2) * ((n : ℝ)⁻¹) ^ 2) atTop (nhds 0) := by
      simpa using hinv.const_mul ((4 / 3 : ℝ) / d.1 ^ 2)
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    field_simp [hn0, d.2]
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact norm_juliaDefectAttenuationKernel_le_invSq
    (mul_ne_zero (by exact_mod_cast (Nat.ne_of_gt hn)) d.2)

/-- Julia equilibrium-defect clock is Rajchman, quantitatively by inverse-square attenuation. -/
def juliaDefectEquilibriumRajchmanClockLaw : RajchmanClockLaw :=
  ⟨_root_.HTGeometry.juliaDefectEquilibriumClockProbabilityMeasure, fun d => by
    constructor
    · apply (tendsto_juliaDefectAttenuationKernel_nat_mul d).congr'
      filter_upwards [] with n
      rw [_root_.HTGeometry.charFun_juliaDefectEquilibriumClockProbabilityMeasure]
    · have h := (tendsto_juliaDefectAttenuationKernel_nat_mul d).comp
        (tendsto_add_atTop_nat 1)
      apply h.congr'
      filter_upwards [] with n
      rw [_root_.HTGeometry.charFun_juliaDefectEquilibriumClockProbabilityMeasure]
      simp only [Function.comp_apply]
      rw [show -(n + 1 : ℝ) * d.1 = -(((n + 1 : ℕ) : ℝ) * d.1) by
        push_cast
        ring,
        _root_.HTGeometry.juliaDefectAttenuationKernel_neg]⟩

/-- Exact finite-spectrum coefficient under Julia equilibrium-defect timing. -/
theorem finiteJuliaDefectEquilibriumClockSample_fourier_integral
    {d : Type*} [Fintype d] (energy : d → ℝ) (m : d → ℤ) :
    ∫ x, UnitAddTorus.mFourier m x
        ∂(finiteClockSampledPhaseProbabilityMeasure
          _root_.HTGeometry.juliaDefectEquilibriumClockProbabilityMeasure energy :
            Measure (UnitAddTorus d)) =
      (_root_.HTGeometry.juliaDefectAttenuationKernel
        (finiteTorusCharacterDetuning m energy) : ℂ) := by
  rw [finiteClockSampledPhaseProbabilityMeasure_mFourier_integral,
    _root_.HTGeometry.charFun_juliaDefectEquilibriumClockProbabilityMeasure]

/-- Exact finite-support coefficient under countable Julia equilibrium-defect timing. -/
theorem countableJuliaDefectEquilibriumClockSample_fourier_integral
    {I : Type*} [Countable I] (omega : I → ℝ) (m : I →₀ ℤ) :
    ∫ x, infiniteTorusFourier m x
        ∂(countableClockSampledPhaseProbabilityMeasure
          _root_.HTGeometry.juliaDefectEquilibriumClockProbabilityMeasure omega :
            Measure (I → UnitAddCircle)) =
      (_root_.HTGeometry.juliaDefectAttenuationKernel
        (infiniteTorusCharacterDetuning m omega) : ℂ) := by
  rw [countableClockSampledPhaseProbabilityMeasure_fourier_integral,
    _root_.HTGeometry.charFun_juliaDefectEquilibriumClockProbabilityMeasure]

/-- Julia equilibrium-defect timing is Rajchman on every finite nonresonant ray. -/
theorem finiteJuliaDefectEquilibriumClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        _root_.HTGeometry.juliaDefectEquilibriumClockProbabilityMeasure energy :
          Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    juliaDefectEquilibriumRajchmanClockLaw energy m

/-- Julia equilibrium-defect timing is Rajchman on every countable nonresonant ray. -/
theorem countableJuliaDefectEquilibriumClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        _root_.HTGeometry.juliaDefectEquilibriumClockProbabilityMeasure omega :
          Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    juliaDefectEquilibriumRajchmanClockLaw omega m

/-- Julia equilibrium-defect timing makes every nonzero-frequency coordinate Rajchman. -/
theorem countableJuliaDefectEquilibriumClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I]
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        _root_.HTGeometry.juliaDefectEquilibriumClockProbabilityMeasure
        (fun j => (omega j).1) : Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    juliaDefectEquilibriumRajchmanClockLaw omega i

/-- Julia equilibrium-defect timing suppresses every nonzero prime-log character ray. -/
theorem primeLogJuliaDefectEquilibriumClockSample_isInfiniteTorusRayRajchman
    (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        _root_.HTGeometry.juliaDefectEquilibriumClockProbabilityMeasure
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    juliaDefectEquilibriumRajchmanClockLaw m

/-- Positive-time Gamma--Meixner sampling of every finite spectrum is Rajchman on each
nonresonant character ray. -/
theorem finiteMeixnerClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (theta : PositiveMeixnerConvolutionTime)
    (energy : d → ℝ) (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        (meixnerClockProbabilityMeasure theta) energy : Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (meixnerRajchmanClockLaw theta) energy m

/-- Positive-time Gamma--Meixner sampling of every countable spectrum is Rajchman on each
nonresonant finite-support character ray. -/
theorem countableMeixnerClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (theta : PositiveMeixnerConvolutionTime)
    (omega : I → ℝ) (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (meixnerClockProbabilityMeasure theta) omega : Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (meixnerRajchmanClockLaw theta) omega m

/-- Every nonzero-frequency coordinate is Rajchman under positive-time Gamma--Meixner sampling. -/
theorem countableMeixnerClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (theta : PositiveMeixnerConvolutionTime)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (meixnerClockProbabilityMeasure theta) (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (meixnerRajchmanClockLaw theta) omega i

/-- Positive-time Gamma--Meixner observation suppresses every nonzero finite prime-log
character ray. -/
theorem primeLogMeixnerClockSample_isInfiniteTorusRayRajchman
    (theta : PositiveMeixnerConvolutionTime)
    (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (meixnerClockProbabilityMeasure theta)
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (meixnerRajchmanClockLaw theta) m

/-! ## Further corpus clocks exposed by the Rajchman transfer -/

/-! ### Archimedean Gamma cyclic spectral measure -/

/-- Corpus Gamma cyclic spectral measure bundled as a probability clock. -/
def gammaCyclicClockProbabilityMeasure : ProbabilityMeasure ℝ :=
  ⟨_root_.HTGeometry.gammaCyclicMeasure, inferInstance⟩

/-- Exact characteristic function of the corpus Gamma cyclic spectral measure. -/
theorem charFun_gammaCyclicClockProbabilityMeasure (t : ℝ) :
    charFun (gammaCyclicClockProbabilityMeasure : Measure ℝ) t =
      (RHTower.semilocalArchimedeanCharacteristic t : ℂ) := by
  change charFun _root_.HTGeometry.gammaCyclicMeasure t = _
  exact _root_.RHTower.charFun_gammaCyclicMeasure t

/-- The corpus Gamma cyclic spectral law and the independently normalized Sonin semilocal
Gamma-density law are the same measure. -/
theorem gammaCyclicClockProbabilityMeasure_eq_semilocalArchimedeanGammaClock :
    (gammaCyclicClockProbabilityMeasure : Measure ℝ) =
      (semilocalArchimedeanGammaClockProbabilityMeasure : Measure ℝ) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_gammaCyclicClockProbabilityMeasure,
    charFun_semilocalArchimedeanGammaClockProbabilityMeasure]

/-- Corpus Gamma cyclic spectral measure is Rajchman. -/
def gammaCyclicRajchmanClockLaw : RajchmanClockLaw :=
  ⟨gammaCyclicClockProbabilityMeasure, fun d => by
    have h := semilocalArchimedeanGammaRajchmanClockLaw.2
    change IsRajchmanClockLaw semilocalArchimedeanGammaClockProbabilityMeasure at h
    have hd := h d
    simpa only [gammaCyclicClockProbabilityMeasure_eq_semilocalArchimedeanGammaClock] using hd⟩

/-- Exact finite-spectrum coefficient under Gamma cyclic time sampling. -/
theorem finiteGammaCyclicClockSample_fourier_integral
    {d : Type*} [Fintype d] (energy : d → ℝ) (m : d → ℤ) :
    ∫ x, UnitAddTorus.mFourier m x
        ∂(finiteClockSampledPhaseProbabilityMeasure
          gammaCyclicClockProbabilityMeasure energy : Measure (UnitAddTorus d)) =
      (RHTower.semilocalArchimedeanCharacteristic
        (finiteTorusCharacterDetuning m energy) : ℂ) := by
  rw [finiteClockSampledPhaseProbabilityMeasure_mFourier_integral,
    charFun_gammaCyclicClockProbabilityMeasure]

/-- Exact finite-support coefficient under countable Gamma cyclic time sampling. -/
theorem countableGammaCyclicClockSample_fourier_integral
    {I : Type*} [Countable I] (omega : I → ℝ) (m : I →₀ ℤ) :
    ∫ x, infiniteTorusFourier m x
        ∂(countableClockSampledPhaseProbabilityMeasure
          gammaCyclicClockProbabilityMeasure omega : Measure (I → UnitAddCircle)) =
      (RHTower.semilocalArchimedeanCharacteristic
        (infiniteTorusCharacterDetuning m omega) : ℂ) := by
  rw [countableClockSampledPhaseProbabilityMeasure_fourier_integral,
    charFun_gammaCyclicClockProbabilityMeasure]

/-- Gamma cyclic timing is Rajchman on every finite nonresonant ray. -/
theorem finiteGammaCyclicClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure gammaCyclicClockProbabilityMeasure energy :
        Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    gammaCyclicRajchmanClockLaw energy m

/-- Gamma cyclic timing is Rajchman on every countable nonresonant ray. -/
theorem countableGammaCyclicClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure gammaCyclicClockProbabilityMeasure omega :
        Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    gammaCyclicRajchmanClockLaw omega m

/-- Gamma cyclic timing makes every nonzero-frequency sampled coordinate Rajchman. -/
theorem countableGammaCyclicClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I]
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure gammaCyclicClockProbabilityMeasure
        (fun j => (omega j).1) : Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    gammaCyclicRajchmanClockLaw omega i

/-- Gamma cyclic timing suppresses every nonzero prime-log character ray. -/
theorem primeLogGammaCyclicClockSample_isInfiniteTorusRayRajchman
    (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure gammaCyclicClockProbabilityMeasure
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    gammaCyclicRajchmanClockLaw m

/-- Corpus Gamma cyclic spectral measure is atomless. -/
theorem gammaCyclicClockProbabilityMeasure_nullSingletonClass :
    NullSingletonClass (gammaCyclicClockProbabilityMeasure : Measure ℝ) := by
  rw [gammaCyclicClockProbabilityMeasure_eq_semilocalArchimedeanGammaClock]
  exact semilocalArchimedeanGammaClockProbabilityMeasure_nullSingletonClass

/-! ### Absolute Poisson--Hilbert detector envelope -/

/-- Positive bandwidth of the Poisson--Hilbert detector. -/
def PositiveXiPoissonHilbertScale := {T : ℝ // 0 < T}

/-- Absolute Poisson--Hilbert detector envelope as normalized nonnegative `L¹` data. -/
def xiPoissonHilbertAbsoluteDensityData
    (T : PositiveXiPoissonHilbertScale) : RealProbabilityDensityData :=
  ⟨fun x => |_root_.RHTower.xiPoissonHilbertKernel T.1 x|,
    by
      simpa only [Real.norm_eq_abs] using
        (_root_.RHTower.integrable_xiPoissonHilbertKernel T.2).norm,
    fun x => abs_nonneg _,
    _root_.RHTower.integral_abs_xiPoissonHilbertKernel_eq_one T.2⟩

/-- Probability clock generated by the absolute Poisson--Hilbert detector envelope. -/
def xiPoissonHilbertAbsoluteClockProbabilityMeasure
    (T : PositiveXiPoissonHilbertScale) : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock (xiPoissonHilbertAbsoluteDensityData T)

/-- Every positive-bandwidth absolute Poisson--Hilbert detector clock is Rajchman. -/
def xiPoissonHilbertAbsoluteRajchmanClockLaw
    (T : PositiveXiPoissonHilbertScale) : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw (xiPoissonHilbertAbsoluteDensityData T)

/-- Absolute Poisson--Hilbert timing is Rajchman on every finite nonresonant ray. -/
theorem finiteXiPoissonHilbertAbsoluteClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (T : PositiveXiPoissonHilbertScale) (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        (xiPoissonHilbertAbsoluteClockProbabilityMeasure T) energy :
          Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (xiPoissonHilbertAbsoluteRajchmanClockLaw T) energy m

/-- Absolute Poisson--Hilbert timing is Rajchman on every countable nonresonant ray. -/
theorem countableXiPoissonHilbertAbsoluteClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (T : PositiveXiPoissonHilbertScale) (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (xiPoissonHilbertAbsoluteClockProbabilityMeasure T) omega :
          Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (xiPoissonHilbertAbsoluteRajchmanClockLaw T) omega m

/-- Absolute Poisson--Hilbert timing makes every nonzero-frequency coordinate Rajchman. -/
theorem countableXiPoissonHilbertAbsoluteClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (T : PositiveXiPoissonHilbertScale)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (xiPoissonHilbertAbsoluteClockProbabilityMeasure T) (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (xiPoissonHilbertAbsoluteRajchmanClockLaw T) omega i

/-- Absolute Poisson--Hilbert timing suppresses every nonzero prime-log character ray. -/
theorem primeLogXiPoissonHilbertAbsoluteClockSample_isInfiniteTorusRayRajchman
    (T : PositiveXiPoissonHilbertScale) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (xiPoissonHilbertAbsoluteClockProbabilityMeasure T)
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (xiPoissonHilbertAbsoluteRajchmanClockLaw T) m

/-- Every positive-bandwidth absolute Poisson--Hilbert detector clock is atomless. -/
theorem xiPoissonHilbertAbsoluteClockProbabilityMeasure_nullSingletonClass
    (T : PositiveXiPoissonHilbertScale) :
    NullSingletonClass (xiPoissonHilbertAbsoluteClockProbabilityMeasure T : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass (xiPoissonHilbertAbsoluteDensityData T)

/-! ### Unit-Riesz layer-cake law -/

/-- Unit-Riesz layer-cake weight extended by zero outside `(0, 1]`. -/
def unitRieszLayerDensity (v : ℝ) : ℝ :=
  (Ioc (0 : ℝ) 1).indicator RHTower.layerWeight v

/-- Unit-Riesz layer-cake law as normalized nonnegative `L¹` data. -/
def unitRieszLayerDensityData : RealProbabilityDensityData :=
  ⟨unitRieszLayerDensity,
    by
      change Integrable ((Ioc (0 : ℝ) 1).indicator RHTower.layerWeight)
      exact ((RHTower.intervalIntegrable_layerWeight
        (a := (0 : ℝ)) (b := 1) le_rfl zero_le_one).1).integrable_indicator
          measurableSet_Ioc,
    by
      intro v
      exact Set.indicator_nonneg (fun x _ => RHTower.layerWeight_nonneg x) v,
    by
      unfold unitRieszLayerDensity
      rw [integral_indicator measurableSet_Ioc,
        ← intervalIntegral.integral_of_le zero_le_one,
        RHTower.integral_layerWeight_unit]⟩

/-- Probability clock generated by the unit-Riesz layer-cake law. -/
def unitRieszLayerClockProbabilityMeasure : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock unitRieszLayerDensityData

/-- Unit-Riesz layer-cake timing is Rajchman. -/
def unitRieszLayerRajchmanClockLaw : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw unitRieszLayerDensityData

/-- Unit-Riesz layer timing is Rajchman on every finite nonresonant ray. -/
theorem finiteUnitRieszLayerClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure unitRieszLayerClockProbabilityMeasure energy :
        Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    unitRieszLayerRajchmanClockLaw energy m

/-- Unit-Riesz layer timing is Rajchman on every countable nonresonant ray. -/
theorem countableUnitRieszLayerClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure unitRieszLayerClockProbabilityMeasure omega :
        Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    unitRieszLayerRajchmanClockLaw omega m

/-- Unit-Riesz layer timing makes every nonzero-frequency coordinate Rajchman. -/
theorem countableUnitRieszLayerClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I]
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure unitRieszLayerClockProbabilityMeasure
        (fun j => (omega j).1) : Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    unitRieszLayerRajchmanClockLaw omega i

/-- Unit-Riesz layer timing suppresses every nonzero prime-log character ray. -/
theorem primeLogUnitRieszLayerClockSample_isInfiniteTorusRayRajchman
    (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure unitRieszLayerClockProbabilityMeasure
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    unitRieszLayerRajchmanClockLaw m

/-- Unit-Riesz layer-cake clock is atomless. -/
theorem unitRieszLayerClockProbabilityMeasure_nullSingletonClass :
    NullSingletonClass (unitRieszLayerClockProbabilityMeasure : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass unitRieszLayerDensityData

/-! ### Arbitrary-rate positive exponential clocks -/

/-- Positive rate of a one-sided exponential clock. -/
def PositiveExponentialRate := {b : ℝ // 0 < b}

/-- Arbitrary-rate exponential probability density on the positive half-line. -/
def positiveExponentialHalfLineDensityData
    (b : PositiveExponentialRate) : PositiveHalfLineProbabilityDensityData := by
  refine ⟨fun x => b.1 * Real.exp (-(b.1 * x)), ?_, ?_, ?_⟩
  · change Integrable (fun x : ℝ => b.1 * Real.exp (-(b.1 * x)))
      (volume.restrict (Ioi (0 : ℝ)))
    simpa only [neg_mul] using
      (exp_neg_integrableOn_Ioi 0 b.2).const_mul b.1
  · intro x _
    exact mul_nonneg b.2.le (Real.exp_pos _).le
  · rw [integral_const_mul,
      RHTower.integral_Ioi_rexp_neg_mul_shift b.2 0]
    simp only [mul_zero, neg_zero, Real.exp_zero]
    field_simp [b.2.ne']

/-- Whole-line zero extension of an arbitrary-rate exponential density. -/
def positiveExponentialDensityData
    (b : PositiveExponentialRate) : RealProbabilityDensityData :=
  positiveHalfLineProbabilityDensityData (positiveExponentialHalfLineDensityData b)

/-- Probability clock generated by an arbitrary positive exponential rate. -/
def positiveExponentialClockProbabilityMeasure
    (b : PositiveExponentialRate) : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock (positiveExponentialDensityData b)

/-- Exact characteristic function of every positive-rate exponential clock. -/
theorem charFun_positiveExponentialClockProbabilityMeasure
    (b : PositiveExponentialRate) (t : ℝ) :
    charFun (positiveExponentialClockProbabilityMeasure b : Measure ℝ) t =
      (b.1 : ℂ) / ((b.1 : ℂ) - (t : ℂ) * Complex.I) := by
  rw [positiveExponentialClockProbabilityMeasure,
    charFun_realProbabilityDensityClock]
  change (∫ x : ℝ,
      Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
        (((Ioi (0 : ℝ)).indicator
          (fun y : ℝ => b.1 * Real.exp (-(b.1 * y))) x : ℝ) : ℂ)) = _
  have hpoint : (fun x : ℝ =>
      Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
        (((Ioi (0 : ℝ)).indicator
          (fun y : ℝ => b.1 * Real.exp (-(b.1 * y))) x : ℝ) : ℂ)) =
      (Ioi (0 : ℝ)).indicator (fun x : ℝ =>
        (b.1 : ℂ) * Complex.exp
          (-(((b.1 : ℂ) - (t : ℂ) * Complex.I) * (x : ℂ)))) := by
    funext x
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hx, indicator_of_mem hx,
        Complex.ofReal_mul, Complex.ofReal_exp]
      rw [show Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
            ((b.1 : ℂ) * Complex.exp ((-(b.1 * x) : ℝ) : ℂ)) =
          (b.1 : ℂ) * (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
            Complex.exp ((-(b.1 * x) : ℝ) : ℂ)) by ring,
        ← Complex.exp_add]
      congr 2
      push_cast
      ring
    · simp [hx]
  rw [hpoint, integral_indicator measurableSet_Ioi, integral_const_mul]
  have hb : 0 < (((b.1 : ℂ) - (t : ℂ) * Complex.I)).re := by
    simpa [Complex.mul_re] using b.2
  rw [RHTower.integral_Ioi_cexp_neg_mul_shift hb 0]
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_div]
  rw [div_eq_mul_inv]

/-- Every arbitrary positive-rate exponential clock is Rajchman. -/
def positiveExponentialRajchmanClockLaw
    (b : PositiveExponentialRate) : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw (positiveExponentialDensityData b)

/-- Exact finite-spectrum coefficient under arbitrary-rate exponential timing. -/
theorem finitePositiveExponentialClockSample_fourier_integral
    {d : Type*} [Fintype d] (b : PositiveExponentialRate)
    (energy : d → ℝ) (m : d → ℤ) :
    ∫ x, UnitAddTorus.mFourier m x
        ∂(finiteClockSampledPhaseProbabilityMeasure
          (positiveExponentialClockProbabilityMeasure b) energy :
            Measure (UnitAddTorus d)) =
      (b.1 : ℂ) /
        ((b.1 : ℂ) - (finiteTorusCharacterDetuning m energy : ℂ) * Complex.I) := by
  rw [finiteClockSampledPhaseProbabilityMeasure_mFourier_integral,
    charFun_positiveExponentialClockProbabilityMeasure]

/-- Exact finite-support coefficient under countable arbitrary-rate exponential timing. -/
theorem countablePositiveExponentialClockSample_fourier_integral
    {I : Type*} [Countable I] (b : PositiveExponentialRate)
    (omega : I → ℝ) (m : I →₀ ℤ) :
    ∫ x, infiniteTorusFourier m x
        ∂(countableClockSampledPhaseProbabilityMeasure
          (positiveExponentialClockProbabilityMeasure b) omega :
            Measure (I → UnitAddCircle)) =
      (b.1 : ℂ) /
        ((b.1 : ℂ) - (infiniteTorusCharacterDetuning m omega : ℂ) * Complex.I) := by
  rw [countableClockSampledPhaseProbabilityMeasure_fourier_integral,
    charFun_positiveExponentialClockProbabilityMeasure]

/-- Arbitrary-rate exponential timing is Rajchman on every finite nonresonant ray. -/
theorem finitePositiveExponentialClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (b : PositiveExponentialRate) (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        (positiveExponentialClockProbabilityMeasure b) energy :
          Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (positiveExponentialRajchmanClockLaw b) energy m

/-- Arbitrary-rate exponential timing is Rajchman on every countable nonresonant ray. -/
theorem countablePositiveExponentialClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (b : PositiveExponentialRate) (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (positiveExponentialClockProbabilityMeasure b) omega :
          Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (positiveExponentialRajchmanClockLaw b) omega m

/-- Arbitrary-rate exponential timing makes every nonzero-frequency coordinate Rajchman. -/
theorem countablePositiveExponentialClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (b : PositiveExponentialRate)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (positiveExponentialClockProbabilityMeasure b) (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (positiveExponentialRajchmanClockLaw b) omega i

/-- Arbitrary-rate exponential timing suppresses every nonzero prime-log character ray. -/
theorem primeLogPositiveExponentialClockSample_isInfiniteTorusRayRajchman
    (b : PositiveExponentialRate) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (positiveExponentialClockProbabilityMeasure b)
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (positiveExponentialRajchmanClockLaw b) m

/-- Every arbitrary positive-rate exponential clock is atomless. -/
theorem positiveExponentialClockProbabilityMeasure_nullSingletonClass
    (b : PositiveExponentialRate) :
    NullSingletonClass (positiveExponentialClockProbabilityMeasure b : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass (positiveExponentialDensityData b)

/-! ### Unit-Riesz Cesaro leak clocks -/

/-- The normalized fast unit-Riesz Cesaro leak is the unit-rate exponential density. -/
theorem normalized_unitRieszCesaroFastLeakDensity (u : ℝ) :
    (32 / 3 : ℝ) * RHTower.unitRieszCesaroFastLeakDensity u = Real.exp (-u) := by
  rw [RHTower.unitRieszCesaroFastLeakDensity]
  ring

/-- The normalized slow unit-Riesz Cesaro leak is the rate-`1/2` exponential density. -/
theorem normalized_unitRieszCesaroSlowLeakDensity (u : ℝ) :
    (64 / 3 : ℝ) * RHTower.unitRieszCesaroSlowLeakDensity u =
      (1 / 2 : ℝ) * Real.exp (-(1 / 2 : ℝ) * u) := by
  rw [RHTower.unitRieszCesaroSlowLeakDensity]
  ring_nf

/-- Probability clock of the normalized fast unit-Riesz Cesaro leak channel. -/
def unitRieszCesaroFastLeakClockProbabilityMeasure : ProbabilityMeasure ℝ :=
  positiveExponentialClockProbabilityMeasure ⟨1, zero_lt_one⟩

/-- Probability clock of the normalized slow unit-Riesz Cesaro leak channel. -/
def unitRieszCesaroSlowLeakClockProbabilityMeasure : ProbabilityMeasure ℝ :=
  positiveExponentialClockProbabilityMeasure ⟨1 / 2, by norm_num⟩

/-- Normalized fast unit-Riesz Cesaro leak timing is Rajchman. -/
def unitRieszCesaroFastLeakRajchmanClockLaw : RajchmanClockLaw :=
  positiveExponentialRajchmanClockLaw ⟨1, zero_lt_one⟩

/-- Normalized slow unit-Riesz Cesaro leak timing is Rajchman. -/
def unitRieszCesaroSlowLeakRajchmanClockLaw : RajchmanClockLaw :=
  positiveExponentialRajchmanClockLaw ⟨1 / 2, by norm_num⟩

/-- Exact characteristic function of the normalized fast unit-Riesz Cesaro leak clock. -/
theorem charFun_unitRieszCesaroFastLeakClockProbabilityMeasure (t : ℝ) :
    charFun (unitRieszCesaroFastLeakClockProbabilityMeasure : Measure ℝ) t =
      (1 - (t : ℂ) * Complex.I)⁻¹ := by
  rw [unitRieszCesaroFastLeakClockProbabilityMeasure,
    charFun_positiveExponentialClockProbabilityMeasure]
  norm_num [div_eq_mul_inv]

/-- Exact characteristic function of the normalized slow unit-Riesz Cesaro leak clock. -/
theorem charFun_unitRieszCesaroSlowLeakClockProbabilityMeasure (t : ℝ) :
    charFun (unitRieszCesaroSlowLeakClockProbabilityMeasure : Measure ℝ) t =
      (1 / 2 : ℂ) / ((1 / 2 : ℂ) - (t : ℂ) * Complex.I) := by
  rw [unitRieszCesaroSlowLeakClockProbabilityMeasure,
    charFun_positiveExponentialClockProbabilityMeasure]
  change (((1 / 2 : ℝ) : ℂ) / (((1 / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I)) = _
  norm_num

/-- Fast unit-Riesz Cesaro leak timing is Rajchman on every finite nonresonant ray. -/
theorem finiteUnitRieszCesaroFastLeakClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        unitRieszCesaroFastLeakClockProbabilityMeasure energy :
          Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    unitRieszCesaroFastLeakRajchmanClockLaw energy m

/-- Slow unit-Riesz Cesaro leak timing is Rajchman on every finite nonresonant ray. -/
theorem finiteUnitRieszCesaroSlowLeakClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        unitRieszCesaroSlowLeakClockProbabilityMeasure energy :
          Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    unitRieszCesaroSlowLeakRajchmanClockLaw energy m

/-- Fast unit-Riesz Cesaro leak timing is Rajchman on every countable nonresonant ray. -/
theorem countableUnitRieszCesaroFastLeakClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        unitRieszCesaroFastLeakClockProbabilityMeasure omega :
          Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    unitRieszCesaroFastLeakRajchmanClockLaw omega m

/-- Slow unit-Riesz Cesaro leak timing is Rajchman on every countable nonresonant ray. -/
theorem countableUnitRieszCesaroSlowLeakClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        unitRieszCesaroSlowLeakClockProbabilityMeasure omega :
          Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    unitRieszCesaroSlowLeakRajchmanClockLaw omega m

/-- Fast unit-Riesz Cesaro leak timing makes every nonzero-frequency coordinate Rajchman. -/
theorem countableUnitRieszCesaroFastLeakClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I]
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        unitRieszCesaroFastLeakClockProbabilityMeasure (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    unitRieszCesaroFastLeakRajchmanClockLaw omega i

/-- Slow unit-Riesz Cesaro leak timing makes every nonzero-frequency coordinate Rajchman. -/
theorem countableUnitRieszCesaroSlowLeakClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I]
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        unitRieszCesaroSlowLeakClockProbabilityMeasure (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    unitRieszCesaroSlowLeakRajchmanClockLaw omega i

/-- Fast unit-Riesz Cesaro leak timing suppresses every nonzero prime-log character ray. -/
theorem primeLogUnitRieszCesaroFastLeakClockSample_isInfiniteTorusRayRajchman
    (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        unitRieszCesaroFastLeakClockProbabilityMeasure
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    unitRieszCesaroFastLeakRajchmanClockLaw m

/-- Slow unit-Riesz Cesaro leak timing suppresses every nonzero prime-log character ray. -/
theorem primeLogUnitRieszCesaroSlowLeakClockSample_isInfiniteTorusRayRajchman
    (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        unitRieszCesaroSlowLeakClockProbabilityMeasure
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    unitRieszCesaroSlowLeakRajchmanClockLaw m

/-- Normalized fast unit-Riesz Cesaro leak clock is atomless. -/
theorem unitRieszCesaroFastLeakClockProbabilityMeasure_nullSingletonClass :
    NullSingletonClass (unitRieszCesaroFastLeakClockProbabilityMeasure : Measure ℝ) :=
  positiveExponentialClockProbabilityMeasure_nullSingletonClass ⟨1, zero_lt_one⟩

/-- Normalized slow unit-Riesz Cesaro leak clock is atomless. -/
theorem unitRieszCesaroSlowLeakClockProbabilityMeasure_nullSingletonClass :
    NullSingletonClass (unitRieszCesaroSlowLeakClockProbabilityMeasure : Measure ℝ) :=
  positiveExponentialClockProbabilityMeasure_nullSingletonClass ⟨1 / 2, by norm_num⟩

/-! ### Arbitrary-rate centered Laplace clocks -/

/-- Centered Laplace density with arbitrary positive rate. -/
def centeredLaplaceDensityData
    (b : PositiveExponentialRate) : RealProbabilityDensityData := by
  refine ⟨fun x => (b.1 / 2) * Real.exp (-(b.1 * |x|)), ?_, ?_, ?_⟩
  · have h := (_root_.HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 b.2).const_mul
      (b.1 / 2)
    simpa only [pow_zero, one_mul, neg_mul] using h
  · intro x
    exact mul_nonneg (div_nonneg b.2.le zero_le_two) (Real.exp_pos _).le
  · have hmass := _root_.HTGeometry.integral_abs_evenPow_mul_exp_neg_abs 0 b.2
    norm_num at hmass
    rw [integral_const_mul, hmass]
    field_simp [b.2.ne']

/-- Probability clock generated by an arbitrary-rate centered Laplace density. -/
def centeredLaplaceClockProbabilityMeasure
    (b : PositiveExponentialRate) : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock (centeredLaplaceDensityData b)

/-- Exact characteristic function of an arbitrary-rate centered Laplace clock. -/
theorem charFun_centeredLaplaceClockProbabilityMeasure
    (b : PositiveExponentialRate) (t : ℝ) :
    charFun (centeredLaplaceClockProbabilityMeasure b : Measure ℝ) t =
      (b.1 : ℂ) ^ 2 / ((b.1 : ℂ) ^ 2 + (t : ℂ) ^ 2) := by
  let ξ : ℝ := -t / (2 * Real.pi)
  have hrel :
      charFun (centeredLaplaceClockProbabilityMeasure b : Measure ℝ) t =
        (b.1 / 2 : ℂ) *
          𝓕 (fun x : ℝ => (Real.exp (-(b.1 * |x|)) : ℂ)) ξ := by
    rw [centeredLaplaceClockProbabilityMeasure,
      charFun_realProbabilityDensityClock]
    change (∫ x : ℝ,
        Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
          (((b.1 / 2) * Real.exp (-(b.1 * |x|)) : ℝ) : ℂ)) = _
    rw [Real.fourier_eq, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [Circle.smul_def, smul_eq_mul]
    dsimp only [ξ]
    rw [show inner ℝ x (-t / (2 * Real.pi)) = x * (-t / (2 * Real.pi)) by
      simp [RCLike.inner_apply, mul_comm]]
    have hphase := fourierChar_density_eq_charFun_integrand
      x t (Real.exp (-(b.1 * |x|)) : ℂ)
    rw [hphase]
    push_cast
    ring
  have hpi : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hfreq :
      4 * (Real.pi : ℂ) ^ 2 * (ξ : ℂ) ^ 2 = (t : ℂ) ^ 2 := by
    dsimp only [ξ]
    push_cast
    field_simp [hpi]
    ring
  rw [hrel, fourierIntegral_exp_neg_mul_abs b.2, hfreq]
  ring

/-- Every arbitrary-rate centered Laplace clock is Rajchman. -/
def centeredLaplaceRajchmanClockLaw
    (b : PositiveExponentialRate) : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw (centeredLaplaceDensityData b)

/-- Exact finite-spectrum coefficient under arbitrary-rate centered Laplace timing. -/
theorem finiteCenteredLaplaceClockSample_fourier_integral
    {d : Type*} [Fintype d] (b : PositiveExponentialRate)
    (energy : d → ℝ) (m : d → ℤ) :
    ∫ x, UnitAddTorus.mFourier m x
        ∂(finiteClockSampledPhaseProbabilityMeasure
          (centeredLaplaceClockProbabilityMeasure b) energy :
            Measure (UnitAddTorus d)) =
      (b.1 : ℂ) ^ 2 /
        ((b.1 : ℂ) ^ 2 + (finiteTorusCharacterDetuning m energy : ℂ) ^ 2) := by
  rw [finiteClockSampledPhaseProbabilityMeasure_mFourier_integral,
    charFun_centeredLaplaceClockProbabilityMeasure]

/-- Exact finite-support coefficient under countable arbitrary-rate centered Laplace timing. -/
theorem countableCenteredLaplaceClockSample_fourier_integral
    {I : Type*} [Countable I] (b : PositiveExponentialRate)
    (omega : I → ℝ) (m : I →₀ ℤ) :
    ∫ x, infiniteTorusFourier m x
        ∂(countableClockSampledPhaseProbabilityMeasure
          (centeredLaplaceClockProbabilityMeasure b) omega :
            Measure (I → UnitAddCircle)) =
      (b.1 : ℂ) ^ 2 /
        ((b.1 : ℂ) ^ 2 + (infiniteTorusCharacterDetuning m omega : ℂ) ^ 2) := by
  rw [countableClockSampledPhaseProbabilityMeasure_fourier_integral,
    charFun_centeredLaplaceClockProbabilityMeasure]

/-- Arbitrary-rate centered Laplace timing is Rajchman on every finite nonresonant ray. -/
theorem finiteCenteredLaplaceClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (b : PositiveExponentialRate) (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        (centeredLaplaceClockProbabilityMeasure b) energy :
          Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (centeredLaplaceRajchmanClockLaw b) energy m

/-- Arbitrary-rate centered Laplace timing is Rajchman on every countable nonresonant ray. -/
theorem countableCenteredLaplaceClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (b : PositiveExponentialRate) (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (centeredLaplaceClockProbabilityMeasure b) omega :
          Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (centeredLaplaceRajchmanClockLaw b) omega m

/-- Arbitrary-rate centered Laplace timing makes every nonzero-frequency coordinate Rajchman. -/
theorem countableCenteredLaplaceClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (b : PositiveExponentialRate)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (centeredLaplaceClockProbabilityMeasure b) (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (centeredLaplaceRajchmanClockLaw b) omega i

/-- Arbitrary-rate centered Laplace timing suppresses every nonzero prime-log character ray. -/
theorem primeLogCenteredLaplaceClockSample_isInfiniteTorusRayRajchman
    (b : PositiveExponentialRate) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (centeredLaplaceClockProbabilityMeasure b)
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (centeredLaplaceRajchmanClockLaw b) m

/-- Every arbitrary-rate centered Laplace clock is atomless. -/
theorem centeredLaplaceClockProbabilityMeasure_nullSingletonClass
    (b : PositiveExponentialRate) :
    NullSingletonClass (centeredLaplaceClockProbabilityMeasure b : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass (centeredLaplaceDensityData b)

/-- Absolute Poisson--Hilbert detector density is exactly centered Laplace at the detector rate. -/
theorem xiPoissonHilbertAbsoluteDensityData_eq_centeredLaplaceDensityData
    (T : PositiveXiPoissonHilbertScale) :
    xiPoissonHilbertAbsoluteDensityData T =
      centeredLaplaceDensityData ⟨T.1, T.2⟩ := by
  apply Subtype.ext
  funext x
  exact _root_.RHTower.abs_xiPoissonHilbertKernel T.2 x

/-- Exact rational attenuation of the absolute Poisson--Hilbert detector clock. -/
theorem charFun_xiPoissonHilbertAbsoluteClockProbabilityMeasure
    (T : PositiveXiPoissonHilbertScale) (t : ℝ) :
    charFun (xiPoissonHilbertAbsoluteClockProbabilityMeasure T : Measure ℝ) t =
      (T.1 : ℂ) ^ 2 / ((T.1 : ℂ) ^ 2 + (t : ℂ) ^ 2) := by
  rw [xiPoissonHilbertAbsoluteClockProbabilityMeasure,
    xiPoissonHilbertAbsoluteDensityData_eq_centeredLaplaceDensityData]
  exact charFun_centeredLaplaceClockProbabilityMeasure ⟨T.1, T.2⟩ t

/-- Exact finite-spectrum coefficient under absolute Poisson--Hilbert timing. -/
theorem finiteXiPoissonHilbertAbsoluteClockSample_fourier_integral
    {d : Type*} [Fintype d] (T : PositiveXiPoissonHilbertScale)
    (energy : d → ℝ) (m : d → ℤ) :
    ∫ x, UnitAddTorus.mFourier m x
        ∂(finiteClockSampledPhaseProbabilityMeasure
          (xiPoissonHilbertAbsoluteClockProbabilityMeasure T) energy :
            Measure (UnitAddTorus d)) =
      (T.1 : ℂ) ^ 2 /
        ((T.1 : ℂ) ^ 2 + (finiteTorusCharacterDetuning m energy : ℂ) ^ 2) := by
  rw [finiteClockSampledPhaseProbabilityMeasure_mFourier_integral,
    charFun_xiPoissonHilbertAbsoluteClockProbabilityMeasure]

/-- Exact finite-support coefficient under countable absolute Poisson--Hilbert timing. -/
theorem countableXiPoissonHilbertAbsoluteClockSample_fourier_integral
    {I : Type*} [Countable I] (T : PositiveXiPoissonHilbertScale)
    (omega : I → ℝ) (m : I →₀ ℤ) :
    ∫ x, infiniteTorusFourier m x
        ∂(countableClockSampledPhaseProbabilityMeasure
          (xiPoissonHilbertAbsoluteClockProbabilityMeasure T) omega :
            Measure (I → UnitAddCircle)) =
      (T.1 : ℂ) ^ 2 /
        ((T.1 : ℂ) ^ 2 + (infiniteTorusCharacterDetuning m omega : ℂ) ^ 2) := by
  rw [countableClockSampledPhaseProbabilityMeasure_fourier_integral,
    charFun_xiPoissonHilbertAbsoluteClockProbabilityMeasure]

/-! ### Probability densities on arbitrary right rays -/

/-- Probability-density data carried on a right ray `(a, ∞)`. -/
def RightRayProbabilityDensityData (a : ℝ) :=
  {f : ℝ → ℝ // IntegrableOn f (Ioi a) ∧
    (∀ x, a < x → 0 ≤ f x) ∧ ∫ x in Ioi a, f x = 1}

/-- Extend right-ray density data by zero to the whole real line. -/
def rightRayDensityExtension {a : ℝ}
    (f : RightRayProbabilityDensityData a) : ℝ → ℝ :=
  (Ioi a).indicator f.1

/-- Zero extension turns arbitrary right-ray density data into whole-line probability data. -/
def rightRayProbabilityDensityData {a : ℝ}
    (f : RightRayProbabilityDensityData a) : RealProbabilityDensityData := by
  refine ⟨rightRayDensityExtension f, ?_, ?_, ?_⟩
  · exact f.2.1.integrable_indicator measurableSet_Ioi
  · intro x
    exact Set.indicator_nonneg (fun y hy => f.2.2.1 y hy) x
  · rw [rightRayDensityExtension, integral_indicator measurableSet_Ioi]
    exact f.2.2.2

/-! ### Pareto inverse-square clocks -/

/-- Positive lower threshold of an inverse-square Pareto clock. -/
def PositiveParetoThreshold := {lam : ℝ // 0 < lam}

/-- Normalized inverse-square Pareto density on `(lam, ∞)`. -/
def paretoInverseSquareRightRayDensityData
    (lam : PositiveParetoThreshold) : RightRayProbabilityDensityData lam.1 := by
  refine ⟨fun x => lam.1 * (1 / x ^ 2), ?_, ?_, ?_⟩
  · exact (RHTower.integrableOn_Ioi_inv_pow lam.2 (k := 2) (by norm_num)).const_mul lam.1
  · intro x hx
    exact mul_nonneg lam.2.le (by positivity)
  · rw [integral_const_mul, RHTower.integral_Ioi_inv_sq lam.2]
    field_simp [lam.2.ne']

/-- Whole-line zero extension of the inverse-square Pareto density. -/
def paretoInverseSquareDensityData
    (lam : PositiveParetoThreshold) : RealProbabilityDensityData :=
  rightRayProbabilityDensityData (paretoInverseSquareRightRayDensityData lam)

/-- Probability clock generated by the inverse-square Pareto law. -/
def paretoInverseSquareClockProbabilityMeasure
    (lam : PositiveParetoThreshold) : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock (paretoInverseSquareDensityData lam)

/-- Every inverse-square Pareto clock is Rajchman. -/
def paretoInverseSquareRajchmanClockLaw
    (lam : PositiveParetoThreshold) : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw (paretoInverseSquareDensityData lam)

/-- Inverse-square Pareto timing is Rajchman on every finite nonresonant ray. -/
theorem finiteParetoInverseSquareClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (lam : PositiveParetoThreshold) (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        (paretoInverseSquareClockProbabilityMeasure lam) energy :
          Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (paretoInverseSquareRajchmanClockLaw lam) energy m

/-- Inverse-square Pareto timing is Rajchman on every countable nonresonant ray. -/
theorem countableParetoInverseSquareClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (lam : PositiveParetoThreshold) (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (paretoInverseSquareClockProbabilityMeasure lam) omega :
          Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (paretoInverseSquareRajchmanClockLaw lam) omega m

/-- Inverse-square Pareto timing makes every nonzero-frequency coordinate Rajchman. -/
theorem countableParetoInverseSquareClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (lam : PositiveParetoThreshold)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (paretoInverseSquareClockProbabilityMeasure lam) (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (paretoInverseSquareRajchmanClockLaw lam) omega i

/-- Inverse-square Pareto timing suppresses every nonzero prime-log character ray. -/
theorem primeLogParetoInverseSquareClockSample_isInfiniteTorusRayRajchman
    (lam : PositiveParetoThreshold) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (paretoInverseSquareClockProbabilityMeasure lam)
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (paretoInverseSquareRajchmanClockLaw lam) m

/-- Every inverse-square Pareto clock is atomless. -/
theorem paretoInverseSquareClockProbabilityMeasure_nullSingletonClass
    (lam : PositiveParetoThreshold) :
    NullSingletonClass (paretoInverseSquareClockProbabilityMeasure lam : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass (paretoInverseSquareDensityData lam)

/-! ### Radial leakage arcsine clock -/

/-- Exterior radial leakage density, normalized from mass `pi/2` to one on `(1, ∞)`. -/
def radialLeakageRightRayDensityData : RightRayProbabilityDensityData 1 := by
  refine ⟨fun x => (2 / Real.pi) * RHTower.radialLeakageDensity x, ?_, ?_, ?_⟩
  · exact (RHTower.integrableOn_Ioi_radialLeakageDensity le_rfl).const_mul (2 / Real.pi)
  · intro x hx
    exact mul_nonneg (by positivity)
      (RHTower.radialLeakageDensity_nonneg (zero_le_one.trans hx.le))
  · rw [integral_const_mul, RHTower.integral_Ioi_one_radialLeakageDensity]
    field_simp [Real.pi_ne_zero]

/-- Whole-line zero extension of the normalized radial leakage density. -/
def radialLeakageDensityData : RealProbabilityDensityData :=
  rightRayProbabilityDensityData radialLeakageRightRayDensityData

/-- Probability clock generated by normalized radial leakage. -/
def radialLeakageClockProbabilityMeasure : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock radialLeakageDensityData

/-- Normalized radial leakage timing is Rajchman. -/
def radialLeakageRajchmanClockLaw : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw radialLeakageDensityData

/-- Radial leakage timing is Rajchman on every finite nonresonant ray. -/
theorem finiteRadialLeakageClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure radialLeakageClockProbabilityMeasure energy :
        Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    radialLeakageRajchmanClockLaw energy m

/-- Radial leakage timing is Rajchman on every countable nonresonant ray. -/
theorem countableRadialLeakageClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure radialLeakageClockProbabilityMeasure omega :
        Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    radialLeakageRajchmanClockLaw omega m

/-- Radial leakage timing makes every nonzero-frequency coordinate Rajchman. -/
theorem countableRadialLeakageClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I]
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure radialLeakageClockProbabilityMeasure
        (fun j => (omega j).1) : Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    radialLeakageRajchmanClockLaw omega i

/-- Radial leakage timing suppresses every nonzero prime-log character ray. -/
theorem primeLogRadialLeakageClockSample_isInfiniteTorusRayRajchman
    (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure radialLeakageClockProbabilityMeasure
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    radialLeakageRajchmanClockLaw m

/-- Normalized radial leakage clock is atomless. -/
theorem radialLeakageClockProbabilityMeasure_nullSingletonClass :
    NullSingletonClass (radialLeakageClockProbabilityMeasure : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass radialLeakageDensityData

/-! ### Poisson--digamma clocks -/

/-- Unit-mass Poisson kernel at arbitrary positive height as probability-density data. -/
def poissonDigammaDensityData
    (a : PositiveExponentialRate) : RealProbabilityDensityData :=
  ⟨RHTower.poissonWeight a.1,
    RHTower.integrable_poissonWeight a.2,
    RHTower.poissonWeight_nonneg a.2,
    RHTower.integral_poissonWeight a.2⟩

/-- Probability clock generated by the Poisson kernel used in digamma reproduction. -/
def poissonDigammaClockProbabilityMeasure
    (a : PositiveExponentialRate) : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock (poissonDigammaDensityData a)

/-- Every positive-height Poisson--digamma clock is Rajchman. -/
def poissonDigammaRajchmanClockLaw
    (a : PositiveExponentialRate) : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw (poissonDigammaDensityData a)

/-- Poisson--digamma timing is Rajchman on every finite nonresonant ray. -/
theorem finitePoissonDigammaClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (a : PositiveExponentialRate) (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        (poissonDigammaClockProbabilityMeasure a) energy :
          Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (poissonDigammaRajchmanClockLaw a) energy m

/-- Poisson--digamma timing is Rajchman on every countable nonresonant ray. -/
theorem countablePoissonDigammaClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (a : PositiveExponentialRate) (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (poissonDigammaClockProbabilityMeasure a) omega :
          Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (poissonDigammaRajchmanClockLaw a) omega m

/-- Poisson--digamma timing makes every nonzero-frequency coordinate Rajchman. -/
theorem countablePoissonDigammaClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (a : PositiveExponentialRate)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (poissonDigammaClockProbabilityMeasure a) (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (poissonDigammaRajchmanClockLaw a) omega i

/-- Poisson--digamma timing suppresses every nonzero prime-log character ray. -/
theorem primeLogPoissonDigammaClockSample_isInfiniteTorusRayRajchman
    (a : PositiveExponentialRate) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (poissonDigammaClockProbabilityMeasure a)
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (poissonDigammaRajchmanClockLaw a) m

/-- Every positive-height Poisson--digamma clock is atomless. -/
theorem poissonDigammaClockProbabilityMeasure_nullSingletonClass
    (a : PositiveExponentialRate) :
    NullSingletonClass (poissonDigammaClockProbabilityMeasure a : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass (poissonDigammaDensityData a)

/-! ### Erlang-3 Wigner--Smith clocks -/

/-- Third-order Erlang packet on its natural positive half-line. -/
def erlangThreeHalfLineDensityData
    (eps : PositiveExponentialRate) : PositiveHalfLineProbabilityDensityData :=
  ⟨erlangThreeKernel eps.1,
    integrableOn_erlangThreeKernel eps.2,
    fun x _ => erlangThreeKernel_nonneg eps.2 x,
    integral_Ioi_erlangThreeKernel_eq_one eps.2⟩

/-- Whole-line zero extension of the normalized Erlang-3 packet. -/
def erlangThreeDensityData
    (eps : PositiveExponentialRate) : RealProbabilityDensityData :=
  positiveHalfLineProbabilityDensityData (erlangThreeHalfLineDensityData eps)

/-- Probability clock generated by the Erlang-3 Wigner--Smith packet. -/
def erlangThreeClockProbabilityMeasure
    (eps : PositiveExponentialRate) : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock (erlangThreeDensityData eps)

/-- Every positive-scale Erlang-3 Wigner--Smith clock is Rajchman. -/
def erlangThreeRajchmanClockLaw
    (eps : PositiveExponentialRate) : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw (erlangThreeDensityData eps)

/-- Erlang-3 timing is Rajchman on every finite nonresonant ray. -/
theorem finiteErlangThreeClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (eps : PositiveExponentialRate) (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        (erlangThreeClockProbabilityMeasure eps) energy :
          Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (erlangThreeRajchmanClockLaw eps) energy m

/-- Erlang-3 timing is Rajchman on every countable nonresonant ray. -/
theorem countableErlangThreeClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (eps : PositiveExponentialRate) (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (erlangThreeClockProbabilityMeasure eps) omega :
          Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (erlangThreeRajchmanClockLaw eps) omega m

/-- Erlang-3 timing makes every nonzero-frequency coordinate Rajchman. -/
theorem countableErlangThreeClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (eps : PositiveExponentialRate)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (erlangThreeClockProbabilityMeasure eps) (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (erlangThreeRajchmanClockLaw eps) omega i

/-- Erlang-3 timing suppresses every nonzero prime-log character ray. -/
theorem primeLogErlangThreeClockSample_isInfiniteTorusRayRajchman
    (eps : PositiveExponentialRate) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (erlangThreeClockProbabilityMeasure eps)
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (erlangThreeRajchmanClockLaw eps) m

/-- Every positive-scale Erlang-3 Wigner--Smith clock is atomless. -/
theorem erlangThreeClockProbabilityMeasure_nullSingletonClass
    (eps : PositiveExponentialRate) :
    NullSingletonClass (erlangThreeClockProbabilityMeasure eps : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass (erlangThreeDensityData eps)

/-! ### Compact bump and Suzuki mollifier clocks -/

/-- Normalized compact bump of arbitrary positive width as probability-density data. -/
def bumpMollifierDensityData
    (eps : PositiveExponentialRate) : RealProbabilityDensityData :=
  ⟨bumpMollifier eps.2,
    integrable_bumpMollifier eps.2,
    nonneg_bumpMollifier eps.2,
    integral_bumpMollifier eps.2⟩

/-- Probability clock generated by the normalized compact bump. -/
def bumpMollifierClockProbabilityMeasure
    (eps : PositiveExponentialRate) : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock (bumpMollifierDensityData eps)

/-- Every positive-width compact bump clock is Rajchman. -/
def bumpMollifierRajchmanClockLaw
    (eps : PositiveExponentialRate) : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw (bumpMollifierDensityData eps)

/-- Compact bump timing is Rajchman on every finite nonresonant ray. -/
theorem finiteBumpMollifierClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (eps : PositiveExponentialRate) (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        (bumpMollifierClockProbabilityMeasure eps) energy :
          Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (bumpMollifierRajchmanClockLaw eps) energy m

/-- Compact bump timing is Rajchman on every countable nonresonant ray. -/
theorem countableBumpMollifierClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (eps : PositiveExponentialRate) (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (bumpMollifierClockProbabilityMeasure eps) omega :
          Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (bumpMollifierRajchmanClockLaw eps) omega m

/-- Compact bump timing makes every nonzero-frequency coordinate Rajchman. -/
theorem countableBumpMollifierClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (eps : PositiveExponentialRate)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (bumpMollifierClockProbabilityMeasure eps) (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (bumpMollifierRajchmanClockLaw eps) omega i

/-- Compact bump timing suppresses every nonzero prime-log character ray. -/
theorem primeLogBumpMollifierClockSample_isInfiniteTorusRayRajchman
    (eps : PositiveExponentialRate) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (bumpMollifierClockProbabilityMeasure eps)
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (bumpMollifierRajchmanClockLaw eps) m

/-- Every positive-width compact bump clock is atomless. -/
theorem bumpMollifierClockProbabilityMeasure_nullSingletonClass
    (eps : PositiveExponentialRate) :
    NullSingletonClass (bumpMollifierClockProbabilityMeasure eps : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass (bumpMollifierDensityData eps)

/-- Suzuki's scaled mollifier as normalized probability-density data. -/
def suzukiMollifierDensityData
    (eps : PositiveExponentialRate) : RealProbabilityDensityData :=
  ⟨RHTower.suzukiMollifier eps.1,
    RHTower.integrable_suzukiMollifier eps.2,
    RHTower.suzukiMollifier_nonneg eps.2,
    RHTower.integral_suzukiMollifier eps.2⟩

/-- Probability clock generated by Suzuki's scaled mollifier. -/
def suzukiMollifierClockProbabilityMeasure
    (eps : PositiveExponentialRate) : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock (suzukiMollifierDensityData eps)

/-- Every positive-width Suzuki mollifier clock is Rajchman. -/
def suzukiMollifierRajchmanClockLaw
    (eps : PositiveExponentialRate) : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw (suzukiMollifierDensityData eps)

/-- Suzuki mollifier timing is Rajchman on every finite nonresonant ray. -/
theorem finiteSuzukiMollifierClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (eps : PositiveExponentialRate) (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        (suzukiMollifierClockProbabilityMeasure eps) energy :
          Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (suzukiMollifierRajchmanClockLaw eps) energy m

/-- Suzuki mollifier timing is Rajchman on every countable nonresonant ray. -/
theorem countableSuzukiMollifierClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (eps : PositiveExponentialRate) (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (suzukiMollifierClockProbabilityMeasure eps) omega :
          Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (suzukiMollifierRajchmanClockLaw eps) omega m

/-- Suzuki mollifier timing makes every nonzero-frequency coordinate Rajchman. -/
theorem countableSuzukiMollifierClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (eps : PositiveExponentialRate)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (suzukiMollifierClockProbabilityMeasure eps) (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (suzukiMollifierRajchmanClockLaw eps) omega i

/-- Suzuki mollifier timing suppresses every nonzero prime-log character ray. -/
theorem primeLogSuzukiMollifierClockSample_isInfiniteTorusRayRajchman
    (eps : PositiveExponentialRate) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (suzukiMollifierClockProbabilityMeasure eps)
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (suzukiMollifierRajchmanClockLaw eps) m

/-- Every positive-width Suzuki mollifier clock is atomless. -/
theorem suzukiMollifierClockProbabilityMeasure_nullSingletonClass
    (eps : PositiveExponentialRate) :
    NullSingletonClass (suzukiMollifierClockProbabilityMeasure eps : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass (suzukiMollifierDensityData eps)

/-! ### Standard Gaussian coefficient clocks -/

/-- The standard real Gaussian density as normalized whole-line density data. -/
def standardGaussianDensityData : RealProbabilityDensityData :=
  ⟨ProbabilityTheory.gaussianPDFReal 0 1,
    ProbabilityTheory.integrable_gaussianPDFReal 0 1,
    ProbabilityTheory.gaussianPDFReal_nonneg 0 1,
    ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 one_ne_zero⟩

/-- Probability clock generated by the standard Gaussian coefficient law. -/
def standardGaussianClockProbabilityMeasure : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock standardGaussianDensityData

/-- The density clock is exactly mathlib's standard real Gaussian measure. -/
theorem standardGaussianClockProbabilityMeasure_eq_gaussianReal :
    (standardGaussianClockProbabilityMeasure : Measure ℝ) =
      ProbabilityTheory.gaussianReal 0 1 := by
  change realProbabilityDensityMeasure standardGaussianDensityData =
    ProbabilityTheory.gaussianReal 0 1
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero _ one_ne_zero]
  rfl

/-- Exact Gaussian characteristic function of the corpus coefficient clock. -/
theorem charFun_standardGaussianClockProbabilityMeasure (t : ℝ) :
    charFun (standardGaussianClockProbabilityMeasure : Measure ℝ) t =
      Complex.exp (-((t : ℂ) ^ 2) / 2) := by
  rw [standardGaussianClockProbabilityMeasure_eq_gaussianReal,
    ProbabilityTheory.charFun_gaussianReal]
  norm_num
  congr 1
  ring

/-- The standard Gaussian coefficient clock is Rajchman. -/
def standardGaussianRajchmanClockLaw : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw standardGaussianDensityData

/-- Exact finite-spectrum coefficient under standard Gaussian timing. -/
theorem finiteStandardGaussianClockSample_fourier_integral
    {d : Type*} [Fintype d] (energy : d → ℝ) (m : d → ℤ) :
    ∫ x, UnitAddTorus.mFourier m x
        ∂(finiteClockSampledPhaseProbabilityMeasure
          standardGaussianClockProbabilityMeasure energy : Measure (UnitAddTorus d)) =
      Complex.exp (-((finiteTorusCharacterDetuning m energy : ℂ) ^ 2) / 2) := by
  rw [finiteClockSampledPhaseProbabilityMeasure_mFourier_integral,
    charFun_standardGaussianClockProbabilityMeasure]

/-- Exact countable finite-support coefficient under standard Gaussian timing. -/
theorem countableStandardGaussianClockSample_fourier_integral
    {I : Type*} [Countable I] (omega : I → ℝ) (m : I →₀ ℤ) :
    ∫ x, infiniteTorusFourier m x
        ∂(countableClockSampledPhaseProbabilityMeasure
          standardGaussianClockProbabilityMeasure omega : Measure (I → UnitAddCircle)) =
      Complex.exp (-((infiniteTorusCharacterDetuning m omega : ℂ) ^ 2) / 2) := by
  rw [countableClockSampledPhaseProbabilityMeasure_fourier_integral,
    charFun_standardGaussianClockProbabilityMeasure]

/-- Standard Gaussian timing is Rajchman on every finite nonresonant ray. -/
theorem finiteStandardGaussianClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        standardGaussianClockProbabilityMeasure energy : Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    standardGaussianRajchmanClockLaw energy m

/-- Standard Gaussian timing is Rajchman on every countable nonresonant ray. -/
theorem countableStandardGaussianClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        standardGaussianClockProbabilityMeasure omega : Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    standardGaussianRajchmanClockLaw omega m

/-- Standard Gaussian timing makes every nonzero-frequency coordinate Rajchman. -/
theorem countableStandardGaussianClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I]
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure standardGaussianClockProbabilityMeasure
        (fun j => (omega j).1) : Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    standardGaussianRajchmanClockLaw omega i

/-- Standard Gaussian timing suppresses every nonzero prime-log character ray. -/
theorem primeLogStandardGaussianClockSample_isInfiniteTorusRayRajchman
    (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure standardGaussianClockProbabilityMeasure
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    standardGaussianRajchmanClockLaw m

/-- The standard Gaussian coefficient clock is atomless. -/
theorem standardGaussianClockProbabilityMeasure_nullSingletonClass :
    NullSingletonClass (standardGaussianClockProbabilityMeasure : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass standardGaussianDensityData

/-! ### Finite-time golden-rule resonance clocks -/

/-- Strictly positive observation time for a normalized golden-rule kernel. -/
def PositiveGoldenRuleTime := {T : ℝ // 0 < T}

/-- The golden-rule resonance kernel, divided by its exact mass `2πT`. -/
def goldenRuleDensityData (T : PositiveGoldenRuleTime) : RealProbabilityDensityData := by
  refine ⟨fun x => goldenRuleKernel T.1 x / (2 * Real.pi * T.1), ?_, ?_, ?_⟩
  · exact (integrable_goldenRuleKernel T.1).div_const (2 * Real.pi * T.1)
  · intro x
    exact div_nonneg (goldenRuleKernel_nonneg T.1 x)
      (mul_nonneg (mul_nonneg zero_le_two Real.pi_pos.le) T.2.le)
  · rw [integral_div, integral_goldenRuleKernel T.2.le]
    exact div_self (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) T.2.ne')

/-- Probability clock generated by a normalized finite-time golden-rule resonance window. -/
def goldenRuleClockProbabilityMeasure
    (T : PositiveGoldenRuleTime) : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock (goldenRuleDensityData T)

/-- Every finite positive-time golden-rule resonance clock is Rajchman. -/
def goldenRuleRajchmanClockLaw (T : PositiveGoldenRuleTime) : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw (goldenRuleDensityData T)

/-- Golden-rule timing is Rajchman on every finite nonresonant ray. -/
theorem finiteGoldenRuleClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (T : PositiveGoldenRuleTime) (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        (goldenRuleClockProbabilityMeasure T) energy : Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (goldenRuleRajchmanClockLaw T) energy m

/-- Golden-rule timing is Rajchman on every countable nonresonant ray. -/
theorem countableGoldenRuleClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (T : PositiveGoldenRuleTime) (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (goldenRuleClockProbabilityMeasure T) omega : Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (goldenRuleRajchmanClockLaw T) omega m

/-- Golden-rule timing makes every nonzero-frequency coordinate Rajchman. -/
theorem countableGoldenRuleClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (T : PositiveGoldenRuleTime)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (goldenRuleClockProbabilityMeasure T) (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (goldenRuleRajchmanClockLaw T) omega i

/-- Golden-rule timing suppresses every nonzero prime-log character ray. -/
theorem primeLogGoldenRuleClockSample_isInfiniteTorusRayRajchman
    (T : PositiveGoldenRuleTime) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (goldenRuleClockProbabilityMeasure T)
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (goldenRuleRajchmanClockLaw T) m

/-- Every finite positive-time golden-rule resonance clock is atomless. -/
theorem goldenRuleClockProbabilityMeasure_nullSingletonClass
    (T : PositiveGoldenRuleTime) :
    NullSingletonClass (goldenRuleClockProbabilityMeasure T : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass (goldenRuleDensityData T)

/-! ### Fermi--Mellin observer clocks -/

/-- Positive Mellin shape for the normalized Fermi observer law. -/
def PositiveFermiMellinShape := {sigma : ℝ // 0 < sigma}

/-- The normalized Fermi--Mellin density on its natural positive half-line. -/
def fermiMellinHalfLineDensityData
    (sigma : PositiveFermiMellinShape) : PositiveHalfLineProbabilityDensityData := by
  refine ⟨fun t => RHTower.fermiMellinDensity sigma.1 t /
      RHTower.fermiMellinNormalizer sigma.1, ?_, ?_, ?_⟩
  · exact (RHTower.integrableOn_fermiMellinDensity sigma.2).div_const
      (RHTower.fermiMellinNormalizer sigma.1)
  · intro t ht
    exact div_nonneg (RHTower.fermiMellinDensity_pos (σ := sigma.1) ht).le
      (RHTower.fermiMellinNormalizer_pos sigma.2).le
  · rw [integral_div]
    change RHTower.fermiMellinNormalizer sigma.1 /
      RHTower.fermiMellinNormalizer sigma.1 = 1
    exact div_self (RHTower.fermiMellinNormalizer_pos sigma.2).ne'

/-- Whole-line zero extension of the normalized Fermi--Mellin observer density. -/
def fermiMellinDensityData
    (sigma : PositiveFermiMellinShape) : RealProbabilityDensityData :=
  positiveHalfLineProbabilityDensityData (fermiMellinHalfLineDensityData sigma)

/-- Probability clock generated by the Fermi--Mellin observer law. -/
def fermiMellinClockProbabilityMeasure
    (sigma : PositiveFermiMellinShape) : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock (fermiMellinDensityData sigma)

/-- The zero-extended density clock is exactly the corpus Fermi--Mellin measure. -/
theorem fermiMellinClockProbabilityMeasure_eq_corpus
    (sigma : PositiveFermiMellinShape) :
    (fermiMellinClockProbabilityMeasure sigma : Measure ℝ) =
      RHTower.fermiMellinMeasure sigma.1 := by
  change (volume : Measure ℝ).withDensity
      (fun t => ENNReal.ofReal
        ((Ioi (0 : ℝ)).indicator
          (fun u => RHTower.fermiMellinDensity sigma.1 u /
            RHTower.fermiMellinNormalizer sigma.1) t)) = _
  rw [RHTower.fermiMellinMeasure, ← withDensity_indicator measurableSet_Ioi]
  congr 1
  funext t
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · simp [ht]
  · simp [ht]

/-- Every positive-shape Fermi--Mellin observer clock is Rajchman. -/
def fermiMellinRajchmanClockLaw
    (sigma : PositiveFermiMellinShape) : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw (fermiMellinDensityData sigma)

/-- Fermi--Mellin observer timing is Rajchman on every finite nonresonant ray. -/
theorem finiteFermiMellinClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (sigma : PositiveFermiMellinShape) (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        (fermiMellinClockProbabilityMeasure sigma) energy : Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (fermiMellinRajchmanClockLaw sigma) energy m

/-- Fermi--Mellin observer timing is Rajchman on every countable nonresonant ray. -/
theorem countableFermiMellinClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (sigma : PositiveFermiMellinShape) (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (fermiMellinClockProbabilityMeasure sigma) omega : Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (fermiMellinRajchmanClockLaw sigma) omega m

/-- Fermi--Mellin observer timing makes every nonzero-frequency coordinate Rajchman. -/
theorem countableFermiMellinClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (sigma : PositiveFermiMellinShape)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (fermiMellinClockProbabilityMeasure sigma) (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (fermiMellinRajchmanClockLaw sigma) omega i

/-- Fermi--Mellin observer timing suppresses every nonzero prime-log character ray. -/
theorem primeLogFermiMellinClockSample_isInfiniteTorusRayRajchman
    (sigma : PositiveFermiMellinShape) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (fermiMellinClockProbabilityMeasure sigma)
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (fermiMellinRajchmanClockLaw sigma) m

/-- Every positive-shape Fermi--Mellin observer clock is atomless. -/
theorem fermiMellinClockProbabilityMeasure_nullSingletonClass
    (sigma : PositiveFermiMellinShape) :
    NullSingletonClass (fermiMellinClockProbabilityMeasure sigma : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass (fermiMellinDensityData sigma)

/-! ### Unit-interval density infrastructure and binomial beta clocks -/

/-- Probability-density data carried by the unit interval `(0,1]`. -/
def UnitIntervalProbabilityDensityData :=
  {f : ℝ → ℝ // IntervalIntegrable f volume 0 1 ∧
    (∀ x, x ∈ Ioc (0 : ℝ) 1 → 0 ≤ f x) ∧ (∫ x in (0 : ℝ)..1, f x) = 1}

/-- Extend unit-interval density data by zero to the whole real line. -/
def unitIntervalDensityExtension
    (f : UnitIntervalProbabilityDensityData) : ℝ → ℝ :=
  (Ioc (0 : ℝ) 1).indicator f.1

/-- Zero extension turns unit-interval density data into whole-line density data. -/
def unitIntervalProbabilityDensityData
    (f : UnitIntervalProbabilityDensityData) : RealProbabilityDensityData := by
  refine ⟨unitIntervalDensityExtension f, ?_, ?_, ?_⟩
  · exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp f.2.1).integrable_indicator
      measurableSet_Ioc
  · intro x
    by_cases hx : x ∈ Ioc (0 : ℝ) 1
    · rw [unitIntervalDensityExtension, indicator_of_mem hx]
      exact f.2.2.1 x hx
    · simp [unitIntervalDensityExtension, hx]
  · rw [unitIntervalDensityExtension, integral_indicator measurableSet_Ioc,
      ← intervalIntegral.integral_of_le zero_le_one]
    exact f.2.2.2

/-- Admissible integer parameters of a binomial-tail beta density. -/
structure AdmissibleBetaParameters where
  r : ℕ
  k : ℕ
  one_le_k : 1 ≤ k
  k_le_r : k ≤ r

/-- Corpus beta kernel packaged as normalized unit-interval density data. -/
def betaKernelUnitIntervalDensityData
    (p : AdmissibleBetaParameters) : UnitIntervalProbabilityDensityData :=
  ⟨betaKernel p.r p.k,
    (continuous_betaKernel p.r p.k).intervalIntegrable 0 1,
    fun x hx => betaKernel_nonneg (u := x) hx.1.le hx.2 p.r p.k,
    intervalIntegral_betaKernel_eq_one p.r p.k p.one_le_k p.k_le_r⟩

/-- Whole-line zero extension of an admissible binomial beta density. -/
def betaKernelDensityData
    (p : AdmissibleBetaParameters) : RealProbabilityDensityData :=
  unitIntervalProbabilityDensityData (betaKernelUnitIntervalDensityData p)

/-- Probability clock generated by an admissible binomial beta kernel. -/
def betaKernelClockProbabilityMeasure
    (p : AdmissibleBetaParameters) : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock (betaKernelDensityData p)

/-- Every admissible binomial beta clock is Rajchman. -/
def betaKernelRajchmanClockLaw
    (p : AdmissibleBetaParameters) : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw (betaKernelDensityData p)

/-- Beta-kernel timing is Rajchman on every finite nonresonant ray. -/
theorem finiteBetaKernelClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (p : AdmissibleBetaParameters) (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        (betaKernelClockProbabilityMeasure p) energy : Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (betaKernelRajchmanClockLaw p) energy m

/-- Beta-kernel timing is Rajchman on every countable nonresonant ray. -/
theorem countableBetaKernelClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (p : AdmissibleBetaParameters) (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (betaKernelClockProbabilityMeasure p) omega : Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (betaKernelRajchmanClockLaw p) omega m

/-- Beta-kernel timing makes every nonzero-frequency coordinate Rajchman. -/
theorem countableBetaKernelClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (p : AdmissibleBetaParameters)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (betaKernelClockProbabilityMeasure p) (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (betaKernelRajchmanClockLaw p) omega i

/-- Beta-kernel timing suppresses every nonzero prime-log character ray. -/
theorem primeLogBetaKernelClockSample_isInfiniteTorusRayRajchman
    (p : AdmissibleBetaParameters) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (betaKernelClockProbabilityMeasure p)
        (fun q : Nat.Primes => Real.log (q : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (betaKernelRajchmanClockLaw p) m

/-- Every admissible binomial beta clock is atomless. -/
theorem betaKernelClockProbabilityMeasure_nullSingletonClass
    (p : AdmissibleBetaParameters) :
    NullSingletonClass (betaKernelClockProbabilityMeasure p : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass (betaKernelDensityData p)

/-! ### Massive half-wave subordination clocks -/

/-- Positive mass and propagation time for the massive half-wave subordination law. -/
structure PositiveMassSubordinationParameters where
  mass : ℝ
  time : ℝ
  mass_pos : 0 < mass
  time_pos : 0 < time

/-- Massive half-wave subordination kernel as normalized positive-half-line density data. -/
def massSubordinationHalfLineDensityData
    (p : PositiveMassSubordinationParameters) : PositiveHalfLineProbabilityDensityData := by
  refine ⟨RHTower.massSubordinationKernel p.mass p.time, ?_, ?_, ?_⟩
  · by_contra h
    have hz := integral_undef h
    rw [RHTower.massSubordinationKernel_integral_one p.mass_pos p.time_pos] at hz
    norm_num at hz
  · intro s hs
    exact RHTower.massSubordinationKernel_nonneg p.mass_pos.le p.time_pos.le hs
  · exact RHTower.massSubordinationKernel_integral_one p.mass_pos p.time_pos

/-- Whole-line zero extension of the massive half-wave subordination density. -/
def massSubordinationDensityData
    (p : PositiveMassSubordinationParameters) : RealProbabilityDensityData :=
  positiveHalfLineProbabilityDensityData (massSubordinationHalfLineDensityData p)

/-- Probability clock generated by massive half-wave subordination. -/
def massSubordinationClockProbabilityMeasure
    (p : PositiveMassSubordinationParameters) : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock (massSubordinationDensityData p)

/-- Every positive-parameter massive half-wave subordination clock is Rajchman. -/
def massSubordinationRajchmanClockLaw
    (p : PositiveMassSubordinationParameters) : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw (massSubordinationDensityData p)

/-- Massive subordination timing is Rajchman on every finite nonresonant ray. -/
theorem finiteMassSubordinationClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (p : PositiveMassSubordinationParameters) (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        (massSubordinationClockProbabilityMeasure p) energy : Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (massSubordinationRajchmanClockLaw p) energy m

/-- Massive subordination timing is Rajchman on every countable nonresonant ray. -/
theorem countableMassSubordinationClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (p : PositiveMassSubordinationParameters) (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (massSubordinationClockProbabilityMeasure p) omega : Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (massSubordinationRajchmanClockLaw p) omega m

/-- Massive subordination timing makes every nonzero-frequency coordinate Rajchman. -/
theorem countableMassSubordinationClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (p : PositiveMassSubordinationParameters)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (massSubordinationClockProbabilityMeasure p) (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (massSubordinationRajchmanClockLaw p) omega i

/-- Massive subordination timing suppresses every nonzero prime-log character ray. -/
theorem primeLogMassSubordinationClockSample_isInfiniteTorusRayRajchman
    (p : PositiveMassSubordinationParameters) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (massSubordinationClockProbabilityMeasure p)
        (fun q : Nat.Primes => Real.log (q : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (massSubordinationRajchmanClockLaw p) m

/-- Every massive half-wave subordination clock is atomless. -/
theorem massSubordinationClockProbabilityMeasure_nullSingletonClass
    (p : PositiveMassSubordinationParameters) :
    NullSingletonClass (massSubordinationClockProbabilityMeasure p : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass (massSubordinationDensityData p)

/-! ### Infinite-local continuous recurrence clocks -/

/-- Corpus continuous recurrence spectral density as normalized whole-line density data. -/
def infiniteLocalContinuousDensityData : RealProbabilityDensityData :=
  ⟨RHTower.InfiniteLocal.continuousDensity,
    RHTower.InfiniteLocal.continuousDensity_integrable,
    RHTower.InfiniteLocal.continuousDensity_nonneg,
    RHTower.InfiniteLocal.continuousDensity_integral_eq_one⟩

/-- Probability clock generated by the infinite-local continuous spectral density. -/
def infiniteLocalContinuousClockProbabilityMeasure : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock infiniteLocalContinuousDensityData

/-- Its characteristic function is the corpus survival amplitude with Fourier scaling `1/(2π)`. -/
theorem charFun_infiniteLocalContinuousClockProbabilityMeasure (t : ℝ) :
    charFun (infiniteLocalContinuousClockProbabilityMeasure : Measure ℝ) t =
      RHTower.InfiniteLocal.continuousAmplitude (t / (2 * Real.pi)) := by
  rw [infiniteLocalContinuousClockProbabilityMeasure,
    charFun_realProbabilityDensityClock,
    RHTower.InfiniteLocal.continuousAmplitude_eq_spectralIntegral]
  apply integral_congr_ae
  filter_upwards with x
  have hphase : Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) =
      Complex.exp
        (((2 * Real.pi * (x * (t / (2 * Real.pi))) : ℝ) : ℂ) * Complex.I) := by
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [hphase]
  rfl

/-- The infinite-local continuous recurrence clock is Rajchman. -/
def infiniteLocalContinuousRajchmanClockLaw : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw infiniteLocalContinuousDensityData

/-- Exact finite-spectrum coefficient as the corpus continuous survival amplitude. -/
theorem finiteInfiniteLocalContinuousClockSample_fourier_integral
    {d : Type*} [Fintype d] (energy : d → ℝ) (m : d → ℤ) :
    ∫ x, UnitAddTorus.mFourier m x
        ∂(finiteClockSampledPhaseProbabilityMeasure
          infiniteLocalContinuousClockProbabilityMeasure energy : Measure (UnitAddTorus d)) =
      RHTower.InfiniteLocal.continuousAmplitude
        (finiteTorusCharacterDetuning m energy / (2 * Real.pi)) := by
  rw [finiteClockSampledPhaseProbabilityMeasure_mFourier_integral,
    charFun_infiniteLocalContinuousClockProbabilityMeasure]

/-- Exact countable finite-support coefficient as the corpus continuous survival amplitude. -/
theorem countableInfiniteLocalContinuousClockSample_fourier_integral
    {I : Type*} [Countable I] (omega : I → ℝ) (m : I →₀ ℤ) :
    ∫ x, infiniteTorusFourier m x
        ∂(countableClockSampledPhaseProbabilityMeasure
          infiniteLocalContinuousClockProbabilityMeasure omega : Measure (I → UnitAddCircle)) =
      RHTower.InfiniteLocal.continuousAmplitude
        (infiniteTorusCharacterDetuning m omega / (2 * Real.pi)) := by
  rw [countableClockSampledPhaseProbabilityMeasure_fourier_integral,
    charFun_infiniteLocalContinuousClockProbabilityMeasure]

/-- Infinite-local continuous timing is Rajchman on every finite nonresonant ray. -/
theorem finiteInfiniteLocalContinuousClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        infiniteLocalContinuousClockProbabilityMeasure energy : Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    infiniteLocalContinuousRajchmanClockLaw energy m

/-- Infinite-local continuous timing is Rajchman on every countable nonresonant ray. -/
theorem countableInfiniteLocalContinuousClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        infiniteLocalContinuousClockProbabilityMeasure omega : Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    infiniteLocalContinuousRajchmanClockLaw omega m

/-- Infinite-local continuous timing makes every nonzero-frequency coordinate Rajchman. -/
theorem countableInfiniteLocalContinuousClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I]
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure infiniteLocalContinuousClockProbabilityMeasure
        (fun j => (omega j).1) : Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    infiniteLocalContinuousRajchmanClockLaw omega i

/-- Infinite-local continuous timing suppresses every nonzero prime-log character ray. -/
theorem primeLogInfiniteLocalContinuousClockSample_isInfiniteTorusRayRajchman
    (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure infiniteLocalContinuousClockProbabilityMeasure
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    infiniteLocalContinuousRajchmanClockLaw m

/-- Infinite-local continuous recurrence clock is atomless. -/
theorem infiniteLocalContinuousClockProbabilityMeasure_nullSingletonClass :
    NullSingletonClass (infiniteLocalContinuousClockProbabilityMeasure : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass infiniteLocalContinuousDensityData

/-! ### Möbius incidence universal-gap clocks -/

private theorem integrable_mobiusIncidenceUniversalGapDensity :
    Integrable RHTower.mobiusIncidenceUniversalGapDensity := by
  by_contra h
  have hz := integral_undef h
  rw [RHTower.integral_mobiusIncidenceUniversalGapDensity] at hz
  norm_num at hz

/-- Universal incidence gap density divided by its exact mass four. -/
def mobiusIncidenceUniversalGapDensityData : RealProbabilityDensityData := by
  refine ⟨fun x => RHTower.mobiusIncidenceUniversalGapDensity x / 4, ?_, ?_, ?_⟩
  · exact integrable_mobiusIncidenceUniversalGapDensity.div_const 4
  · intro x
    exact div_nonneg (RHTower.mobiusIncidenceUniversalGapDensity_nonneg x) (by norm_num)
  · rw [integral_div, RHTower.integral_mobiusIncidenceUniversalGapDensity]
    norm_num

/-- Probability clock generated by the normalized Möbius incidence universal gap. -/
def mobiusIncidenceUniversalGapClockProbabilityMeasure : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock mobiusIncidenceUniversalGapDensityData

/-- The normalized Möbius incidence universal-gap clock is Rajchman. -/
def mobiusIncidenceUniversalGapRajchmanClockLaw : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw mobiusIncidenceUniversalGapDensityData

/-- Möbius incidence universal-gap timing is Rajchman on every finite nonresonant ray. -/
theorem finiteMobiusIncidenceUniversalGapClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        mobiusIncidenceUniversalGapClockProbabilityMeasure energy :
          Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    mobiusIncidenceUniversalGapRajchmanClockLaw energy m

/-- Möbius incidence universal-gap timing is Rajchman on every countable nonresonant ray. -/
theorem countableMobiusIncidenceUniversalGapClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        mobiusIncidenceUniversalGapClockProbabilityMeasure omega :
          Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    mobiusIncidenceUniversalGapRajchmanClockLaw omega m

/-- Möbius incidence universal-gap timing makes every nonzero-frequency coordinate Rajchman. -/
theorem countableMobiusIncidenceUniversalGapClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I]
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        mobiusIncidenceUniversalGapClockProbabilityMeasure (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    mobiusIncidenceUniversalGapRajchmanClockLaw omega i

/-- Möbius incidence universal-gap timing suppresses every nonzero prime-log character ray. -/
theorem primeLogMobiusIncidenceUniversalGapClockSample_isInfiniteTorusRayRajchman
    (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        mobiusIncidenceUniversalGapClockProbabilityMeasure
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    mobiusIncidenceUniversalGapRajchmanClockLaw m

/-- Normalized Möbius incidence universal-gap clock is atomless. -/
theorem mobiusIncidenceUniversalGapClockProbabilityMeasure_nullSingletonClass :
    NullSingletonClass (mobiusIncidenceUniversalGapClockProbabilityMeasure : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass mobiusIncidenceUniversalGapDensityData

/-! ### Hyperbolic sech-square spectral clocks -/

/-- The hyperbolic sech-square spectral density is pointwise nonnegative. -/
theorem sechSqDensity_nonneg (x : ℝ) : 0 ≤ HTGeometry.sechSqDensity x := by
  unfold HTGeometry.sechSqDensity
  by_cases hx : x = 0
  · simp [hx]
  · rw [if_neg hx]
    positivity

/-- The hyperbolic sech-square spectral density has unit mass. -/
theorem integral_sechSqDensity_eq_one : (∫ x : ℝ, HTGeometry.sechSqDensity x) = 1 := by
  have h := HTGeometry.integral_cos_mul_sechSqDensity 0
  simpa using h

/-- Hyperbolic sech-square spectral density as normalized whole-line density data. -/
def sechSqDensityData : RealProbabilityDensityData :=
  ⟨HTGeometry.sechSqDensity, HTGeometry.integrable_sechSqDensity, sechSqDensity_nonneg,
    integral_sechSqDensity_eq_one⟩

/-- Probability clock generated by the hyperbolic sech-square spectral density. -/
def sechSqClockProbabilityMeasure : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock sechSqDensityData

/-- Exact hyperbolic characteristic function. -/
theorem charFun_sechSqClockProbabilityMeasure (t : ℝ) :
    charFun (sechSqClockProbabilityMeasure : Measure ℝ) t =
      ((Real.cosh (t / (2 * Real.pi)) ^ (-2 : ℝ) : ℝ) : ℂ) := by
  rw [sechSqClockProbabilityMeasure, charFun_realProbabilityDensityClock,
    ← HTGeometry.integral_exp_mul_sechSqDensity (t / (2 * Real.pi))]
  apply integral_congr_ae
  filter_upwards with x
  have hphase : Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) =
      Complex.exp
        (((2 * Real.pi * (x * (t / (2 * Real.pi))) : ℝ) : ℂ) * Complex.I) := by
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [hphase]
  rfl

/-- Hyperbolic sech-square spectral clock is Rajchman. -/
def sechSqRajchmanClockLaw : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw sechSqDensityData

/-- Exact finite-spectrum coefficient under hyperbolic sech-square timing. -/
theorem finiteSechSqClockSample_fourier_integral
    {d : Type*} [Fintype d] (energy : d → ℝ) (m : d → ℤ) :
    ∫ x, UnitAddTorus.mFourier m x
        ∂(finiteClockSampledPhaseProbabilityMeasure
          sechSqClockProbabilityMeasure energy : Measure (UnitAddTorus d)) =
      ((Real.cosh (finiteTorusCharacterDetuning m energy / (2 * Real.pi)) ^
        (-2 : ℝ) : ℝ) : ℂ) := by
  rw [finiteClockSampledPhaseProbabilityMeasure_mFourier_integral,
    charFun_sechSqClockProbabilityMeasure]

/-- Exact countable finite-support coefficient under hyperbolic sech-square timing. -/
theorem countableSechSqClockSample_fourier_integral
    {I : Type*} [Countable I] (omega : I → ℝ) (m : I →₀ ℤ) :
    ∫ x, infiniteTorusFourier m x
        ∂(countableClockSampledPhaseProbabilityMeasure
          sechSqClockProbabilityMeasure omega : Measure (I → UnitAddCircle)) =
      ((Real.cosh (infiniteTorusCharacterDetuning m omega / (2 * Real.pi)) ^
        (-2 : ℝ) : ℝ) : ℂ) := by
  rw [countableClockSampledPhaseProbabilityMeasure_fourier_integral,
    charFun_sechSqClockProbabilityMeasure]

/-- Hyperbolic sech-square timing is Rajchman on every finite nonresonant ray. -/
theorem finiteSechSqClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        sechSqClockProbabilityMeasure energy : Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman sechSqRajchmanClockLaw energy m

/-- Hyperbolic sech-square timing is Rajchman on every countable nonresonant ray. -/
theorem countableSechSqClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        sechSqClockProbabilityMeasure omega : Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    sechSqRajchmanClockLaw omega m

/-- Hyperbolic sech-square timing makes every nonzero-frequency coordinate Rajchman. -/
theorem countableSechSqClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I]
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure sechSqClockProbabilityMeasure
        (fun j => (omega j).1) : Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    sechSqRajchmanClockLaw omega i

/-- Hyperbolic sech-square timing suppresses every nonzero prime-log character ray. -/
theorem primeLogSechSqClockSample_isInfiniteTorusRayRajchman
    (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure sechSqClockProbabilityMeasure
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman sechSqRajchmanClockLaw m

/-- Hyperbolic sech-square spectral clock is atomless. -/
theorem sechSqClockProbabilityMeasure_nullSingletonClass :
    NullSingletonClass (sechSqClockProbabilityMeasure : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass sechSqDensityData

/-! ### Reverse-Bessel radial Gamma-mixture clocks -/

/-- Order and positive spectral shape of a reverse-Bessel radial mixture. -/
structure RadialMixtureParameters where
  order : ℕ
  shape : ℝ
  one_lt_shape : 1 < shape

/-- Exact total mass of a reverse-Bessel radial mixture. -/
def radialMixtureNormalizer (p : RadialMixtureParameters) : ℝ :=
  (p.shape - 1)⁻¹ *
    ∑ j ∈ Finset.range (p.order + 1), RHTower.radialMixtureWeight p.order p.shape j

/-- Every reverse-Bessel radial mixture has strictly positive total mass. -/
theorem radialMixtureNormalizer_pos (p : RadialMixtureParameters) :
    0 < radialMixtureNormalizer p := by
  have hsum : 0 < ∑ j ∈ Finset.range (p.order + 1),
      RHTower.radialMixtureWeight p.order p.shape j :=
    lt_of_lt_of_le
      (RHTower.radialMixtureWeight_pos (Nat.zero_le p.order) p.one_lt_shape)
      (RHTower.radialMixtureWeight_le_total p.one_lt_shape (Nat.zero_le p.order))
  exact mul_pos (inv_pos.mpr (sub_pos.mpr p.one_lt_shape)) hsum

/-- Normalized reverse-Bessel radial mixture on the positive half-line. -/
def radialMixtureHalfLineDensityData
    (p : RadialMixtureParameters) : PositiveHalfLineProbabilityDensityData := by
  refine ⟨fun t => RHTower.radialMixtureDensity p.order p.shape t /
      radialMixtureNormalizer p, ?_, ?_, ?_⟩
  · exact (RHTower.integrableOn_radialMixtureDensity p.one_lt_shape).div_const
      (radialMixtureNormalizer p)
  · intro t ht
    exact div_nonneg
      (RHTower.radialMixtureDensity_nonneg p.one_lt_shape ht.le)
      (radialMixtureNormalizer_pos p).le
  · rw [integral_div, RHTower.integral_radialMixtureDensity_Ioi p.one_lt_shape]
    change radialMixtureNormalizer p / radialMixtureNormalizer p = 1
    exact div_self (radialMixtureNormalizer_pos p).ne'

/-- Whole-line zero extension of a normalized reverse-Bessel radial mixture. -/
def radialMixtureDensityData
    (p : RadialMixtureParameters) : RealProbabilityDensityData :=
  positiveHalfLineProbabilityDensityData (radialMixtureHalfLineDensityData p)

/-- Probability clock generated by a normalized reverse-Bessel radial mixture. -/
def radialMixtureClockProbabilityMeasure
    (p : RadialMixtureParameters) : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock (radialMixtureDensityData p)

/-- Every reverse-Bessel radial mixture clock is Rajchman. -/
def radialMixtureRajchmanClockLaw
    (p : RadialMixtureParameters) : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw (radialMixtureDensityData p)

/-- Radial-mixture timing is Rajchman on every finite nonresonant ray. -/
theorem finiteRadialMixtureClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (p : RadialMixtureParameters) (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        (radialMixtureClockProbabilityMeasure p) energy : Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (radialMixtureRajchmanClockLaw p) energy m

/-- Radial-mixture timing is Rajchman on every countable nonresonant ray. -/
theorem countableRadialMixtureClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (p : RadialMixtureParameters) (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (radialMixtureClockProbabilityMeasure p) omega : Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (radialMixtureRajchmanClockLaw p) omega m

/-- Radial-mixture timing makes every nonzero-frequency coordinate Rajchman. -/
theorem countableRadialMixtureClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (p : RadialMixtureParameters)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (radialMixtureClockProbabilityMeasure p) (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (radialMixtureRajchmanClockLaw p) omega i

/-- Radial-mixture timing suppresses every nonzero prime-log character ray. -/
theorem primeLogRadialMixtureClockSample_isInfiniteTorusRayRajchman
    (p : RadialMixtureParameters) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (radialMixtureClockProbabilityMeasure p)
        (fun q : Nat.Primes => Real.log (q : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (radialMixtureRajchmanClockLaw p) m

/-- Every normalized reverse-Bessel radial mixture clock is atomless. -/
theorem radialMixtureClockProbabilityMeasure_nullSingletonClass
    (p : RadialMixtureParameters) :
    NullSingletonClass (radialMixtureClockProbabilityMeasure p : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass (radialMixtureDensityData p)

/-! ### Shifted-factorial representing clocks -/

/-- Compact probability reservoir whose positive first moment is normalized to one. -/
structure ShiftedFactorialProbabilitySource where
  reservoir : ProbabilityMeasure ℝ
  supportBound : ℝ
  compactSupport : ∀ᵐ y ∂(reservoir : Measure ℝ), y ∈ Icc 0 supportBound
  positiveFirstMoment : ∫ y in Ioi (0 : ℝ), y ∂(reservoir : Measure ℝ) = 1

/-- Shifted-factorial representing density on its natural positive half-line. -/
def shiftedFactorialHalfLineDensityData
    (S : ShiftedFactorialProbabilitySource) : PositiveHalfLineProbabilityDensityData := by
  refine ⟨factorialMomentDensity (S.reservoir : Measure ℝ), ?_, ?_, ?_⟩
  · exact integrableOn_factorialMomentDensity S.compactSupport
  · intro x _
    exact factorialMomentDensity_nonneg (S.reservoir : Measure ℝ) x
  · have h := integral_pow_mul_factorialMomentDensity S.compactSupport 0
    simpa [S.positiveFirstMoment] using h

/-- Whole-line zero extension of a shifted-factorial representing density. -/
def shiftedFactorialDensityData
    (S : ShiftedFactorialProbabilitySource) : RealProbabilityDensityData :=
  positiveHalfLineProbabilityDensityData (shiftedFactorialHalfLineDensityData S)

/-- Probability clock generated by a shifted-factorial representing density. -/
def shiftedFactorialClockProbabilityMeasure
    (S : ShiftedFactorialProbabilitySource) : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock (shiftedFactorialDensityData S)

/-- Every normalized shifted-factorial representing clock is Rajchman. -/
def shiftedFactorialRajchmanClockLaw
    (S : ShiftedFactorialProbabilitySource) : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw (shiftedFactorialDensityData S)

/-- Shifted-factorial timing is Rajchman on every finite nonresonant ray. -/
theorem finiteShiftedFactorialClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (S : ShiftedFactorialProbabilitySource) (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        (shiftedFactorialClockProbabilityMeasure S) energy : Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (shiftedFactorialRajchmanClockLaw S) energy m

/-- Shifted-factorial timing is Rajchman on every countable nonresonant ray. -/
theorem countableShiftedFactorialClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (S : ShiftedFactorialProbabilitySource) (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (shiftedFactorialClockProbabilityMeasure S) omega : Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (shiftedFactorialRajchmanClockLaw S) omega m

/-- Shifted-factorial timing makes every nonzero-frequency coordinate Rajchman. -/
theorem countableShiftedFactorialClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (S : ShiftedFactorialProbabilitySource)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (shiftedFactorialClockProbabilityMeasure S) (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (shiftedFactorialRajchmanClockLaw S) omega i

/-- Shifted-factorial timing suppresses every nonzero prime-log character ray. -/
theorem primeLogShiftedFactorialClockSample_isInfiniteTorusRayRajchman
    (S : ShiftedFactorialProbabilitySource) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (shiftedFactorialClockProbabilityMeasure S)
        (fun q : Nat.Primes => Real.log (q : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (shiftedFactorialRajchmanClockLaw S) m

/-- Every normalized shifted-factorial representing clock is atomless. -/
theorem shiftedFactorialClockProbabilityMeasure_nullSingletonClass
    (S : ShiftedFactorialProbabilitySource) :
    NullSingletonClass (shiftedFactorialClockProbabilityMeasure S : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass (shiftedFactorialDensityData S)

/-! ### Global unit-Riesz Markov clock -/

/-- Global unit-Riesz Markov density, indexed by the half-open logarithmic cells
`(log m, log (m+1)]`. -/
def unitRieszGlobalMarkovDensity (v : ℝ) : ℝ :=
  if 0 < v then
    RHTower.unitRieszCellMarkovDensity (⌈Real.exp v⌉₊ - 1) v
  else 0

private theorem unitRieszLogCell_lt (m : ℕ) (hm : 1 ≤ m) :
    Real.log (m : ℝ) < Real.log ((m : ℝ) + 1) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hm1pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  exact Real.strictMonoOn_log hmpos hm1pos (by norm_num)

/-- On `(log m, log (m+1)]`, the global density is the derivative of cell `m`. -/
theorem unitRieszGlobalMarkovDensity_eq_cell
    {m : ℕ} (hm : 1 ≤ m) {v : ℝ}
    (hv : v ∈ Ioc (Real.log (m : ℝ)) (Real.log ((m : ℝ) + 1))) :
    unitRieszGlobalMarkovDensity v = RHTower.unitRieszCellMarkovDensity m v := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hm1pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hlow : (m : ℝ) < Real.exp v := by
    rw [← Real.exp_log hmpos]
    exact Real.exp_lt_exp.mpr hv.1
  have hhigh : Real.exp v ≤ (m : ℝ) + 1 := by
    rw [← Real.exp_log hm1pos]
    exact Real.exp_le_exp.mpr hv.2
  have hceil : ⌈Real.exp v⌉₊ = m + 1 := by
    apply (Nat.ceil_eq_iff (Nat.succ_ne_zero m)).2
    simpa [Nat.cast_add, Nat.cast_one] using And.intro hlow hhigh
  have hvpos : 0 < v :=
    (Real.log_natCast_nonneg m).trans_lt hv.1
  simp [unitRieszGlobalMarkovDensity, hvpos, hceil]

/-- Global unit-Riesz density is nonnegative everywhere. -/
theorem unitRieszGlobalMarkovDensity_nonneg (v : ℝ) :
    0 ≤ unitRieszGlobalMarkovDensity v := by
  by_cases hv : 0 < v
  · have hexp : (1 : ℝ) < Real.exp v := by simpa using Real.exp_lt_exp.mpr hv
    have hceil2 : 2 ≤ ⌈Real.exp v⌉₊ := by
      rw [Nat.add_one_le_ceil_iff]
      simpa using hexp
    have hceil1 : 1 ≤ ⌈Real.exp v⌉₊ := hceil2.trans' (by omega)
    have hupper : Real.exp v ≤ (⌈Real.exp v⌉₊ : ℝ) := Nat.le_ceil _
    have hsqrt : Real.exp (v / 2) ≤ Real.sqrt ((⌈Real.exp v⌉₊ - 1 : ℕ) + 1) := by
      rw [← GaloisForLFunctions.RHTower.sqrtExpSelf]
      have hcast : (((⌈Real.exp v⌉₊ - 1 : ℕ) : ℝ) + 1) =
          (⌈Real.exp v⌉₊ : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel hceil1
      rw [hcast]
      exact Real.sqrt_le_sqrt hupper
    simp only [unitRieszGlobalMarkovDensity, if_pos hv]
    exact RHTower.unitRieszCellMarkovDensity_nonneg _ _ hsqrt
  · simp [unitRieszGlobalMarkovDensity, hv]

private theorem unitRieszCellDensity_continuous (m : ℕ) :
    Continuous (RHTower.unitRieszCellMarkovDensity m) := by
  unfold RHTower.unitRieszCellMarkovDensity
  fun_prop

/-- Global density is interval-integrable on each complete logarithmic cell. -/
theorem unitRieszGlobalMarkovDensity_intervalIntegrable_cell
    (m : ℕ) (hm : 1 ≤ m) :
    IntervalIntegrable unitRieszGlobalMarkovDensity volume
      (Real.log (m : ℝ)) (Real.log ((m : ℝ) + 1)) := by
  have hlog := (unitRieszLogCell_lt m hm).le
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hlog]
  have hcell : IntegrableOn (RHTower.unitRieszCellMarkovDensity m)
      (Ioc (Real.log (m : ℝ)) (Real.log ((m : ℝ) + 1))) := by
    have := (unitRieszCellDensity_continuous m).intervalIntegrable (μ := volume)
      (Real.log (m : ℝ)) (Real.log ((m : ℝ) + 1))
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hlog] at this
  exact hcell.congr_fun
    (fun _ hx => (unitRieszGlobalMarkovDensity_eq_cell hm hx).symm) measurableSet_Ioc

/-- Exact mass of one complete logarithmic cell. -/
theorem intervalIntegral_unitRieszGlobalMarkovDensity_cell
    (m : ℕ) (hm : 1 ≤ m) :
    ∫ v in Real.log (m : ℝ)..Real.log ((m : ℝ) + 1),
        unitRieszGlobalMarkovDensity v =
      RHTower.unitRieszCellProfile m (Real.log ((m : ℝ) + 1)) -
        RHTower.unitRieszCellProfile m (Real.log (m : ℝ)) := by
  have hlog := (unitRieszLogCell_lt m hm).le
  calc
    ∫ v in Real.log (m : ℝ)..Real.log ((m : ℝ) + 1),
        unitRieszGlobalMarkovDensity v =
        ∫ v in Real.log (m : ℝ)..Real.log ((m : ℝ) + 1),
          RHTower.unitRieszCellMarkovDensity m v := by
            rw [intervalIntegral.integral_of_le hlog,
              intervalIntegral.integral_of_le hlog]
            exact setIntegral_congr_fun measurableSet_Ioc
              (fun _ hx => unitRieszGlobalMarkovDensity_eq_cell hm hx)
    _ = RHTower.unitRieszCellProfile m (Real.log ((m : ℝ) + 1)) -
        RHTower.unitRieszCellProfile m (Real.log (m : ℝ)) := by
          exact intervalIntegral.integral_eq_sub_of_hasDerivAt
            (fun v _ => RHTower.hasDerivAt_unitRieszCellProfile m v)
            ((unitRieszCellDensity_continuous m).intervalIntegrable (μ := volume) _ _)

/-- Adjacent cell profiles glue at every positive integral logarithmic boundary. -/
theorem unitRieszCellProfile_glue_log (m : ℕ) :
    RHTower.unitRieszCellProfile (m + 1) (Real.log ((m : ℝ) + 1)) =
      RHTower.unitRieszCellProfile m (Real.log ((m : ℝ) + 1)) := by
  apply RHTower.unitRieszCellProfile_succ_eq_at_boundary
  rw [← GaloisForLFunctions.RHTower.sqrtExpSelf]
  rw [Real.exp_log (by positivity : (0 : ℝ) < (m : ℝ) + 1)]

/-- At an integral logarithmic boundary, the floor-indexed global profile selects that cell. -/
theorem unitRieszLogProfile_log_nat (m : ℕ) (hm : 1 ≤ m) :
    RHTower.unitRieszLogProfile (Real.log (m : ℝ)) =
      RHTower.unitRieszCellProfile m (Real.log (m : ℝ)) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.zero_lt_of_lt hm
  apply RHTower.unitRieszLogProfile_eq_cell
  · rw [Real.exp_log hmpos]
  · rw [Real.exp_log hmpos]
    norm_num

/-- Global unit-Riesz density is interval-integrable on every finite cell prefix. -/
theorem unitRieszGlobalMarkovDensity_intervalIntegrable_prefix (n : ℕ) :
    IntervalIntegrable unitRieszGlobalMarkovDensity volume 0
      (Real.log ((n : ℝ) + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hcell := unitRieszGlobalMarkovDensity_intervalIntegrable_cell
        (n + 1) (by omega)
      have hcell' : IntervalIntegrable unitRieszGlobalMarkovDensity volume
          (Real.log ((n : ℝ) + 1))
          (Real.log (((n + 1 : ℕ) : ℝ) + 1)) := by
        simpa [Nat.cast_add, Nat.cast_one] using hcell
      simpa [Nat.cast_add, Nat.cast_one] using ih.trans hcell'

/-- Exact finite-prefix mass: accumulated density equals the corpus global profile. -/
theorem intervalIntegral_unitRieszGlobalMarkovDensity_prefix (n : ℕ) :
    ∫ v in (0 : ℝ)..Real.log ((n : ℝ) + 1), unitRieszGlobalMarkovDensity v =
      RHTower.unitRieszLogProfile (Real.log ((n : ℝ) + 1)) := by
  induction n with
  | zero =>
      simpa using RHTower.unitRieszLogProfile_zero.symm
  | succ n ih =>
      have hprev := unitRieszGlobalMarkovDensity_intervalIntegrable_prefix n
      have hcell := unitRieszGlobalMarkovDensity_intervalIntegrable_cell
        (n + 1) (by omega)
      have hcell' : IntervalIntegrable unitRieszGlobalMarkovDensity volume
          (Real.log ((n : ℝ) + 1))
          (Real.log (((n + 1 : ℕ) : ℝ) + 1)) := by
        simpa [Nat.cast_add, Nat.cast_one] using hcell
      have hadd := intervalIntegral.integral_add_adjacent_intervals hprev hcell'
      have hcellMass := intervalIntegral_unitRieszGlobalMarkovDensity_cell
        (n + 1) (by omega)
      have hprevProfile := unitRieszLogProfile_log_nat (n + 1) (by omega)
      have hnextProfile :
          RHTower.unitRieszLogProfile (Real.log ((n : ℝ) + 1 + 1)) =
            RHTower.unitRieszCellProfile (n + 1 + 1)
              (Real.log ((n : ℝ) + 1 + 1)) := by
        rw [show ((n : ℝ) + 1 + 1) = ((n + 2 : ℕ) : ℝ) by push_cast; ring]
        rw [show n + 1 + 1 = n + 2 by omega]
        exact unitRieszLogProfile_log_nat (n + 2) (by omega)
      have hglue := unitRieszCellProfile_glue_log (n + 1)
      norm_num [Nat.cast_add, Nat.cast_one] at hadd hcellMass hprevProfile hglue ⊢
      rw [← hadd, ih, hcellMass, hprevProfile, hnextProfile]
      linarith

/-- Natural logarithmic cell boundaries escape to infinity. -/
theorem tendsto_unitRieszLogNatBoundary_atTop :
    Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) atTop atTop := by
  exact Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

/-- Global unit-Riesz density is integrable on its positive support. -/
theorem integrableOn_unitRieszGlobalMarkovDensity_Ioi :
    IntegrableOn unitRieszGlobalMarkovDensity (Ioi (0 : ℝ)) := by
  apply integrableOn_Ioi_of_intervalIntegral_norm_tendsto
    (f := unitRieszGlobalMarkovDensity)
    (μ := volume) (l := atTop)
    (b := fun n : ℕ => Real.log ((n : ℝ) + 1)) 1 0
  · intro n
    have hnonneg : 0 ≤ Real.log ((n : ℝ) + 1) := by
      rw [← Nat.cast_add_one]
      exact Real.log_natCast_nonneg (n + 1)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hnonneg).1
      (unitRieszGlobalMarkovDensity_intervalIntegrable_prefix n)
  · exact tendsto_unitRieszLogNatBoundary_atTop
  · have hprofile :=
      GaloisForLFunctions.RHTower.tendsto_unitRieszLogProfile_atTop.comp
        tendsto_unitRieszLogNatBoundary_atTop
    apply hprofile.congr'
    filter_upwards [] with n
    simp only [Function.comp_apply]
    rw [← intervalIntegral_unitRieszGlobalMarkovDensity_prefix n]
    apply intervalIntegral.integral_congr
    intro v _
    exact (Real.norm_of_nonneg (unitRieszGlobalMarkovDensity_nonneg v)).symm

/-- Total positive-half-line mass of the global unit-Riesz density is exactly one. -/
theorem integral_unitRieszGlobalMarkovDensity_Ioi :
    ∫ v in Ioi (0 : ℝ), unitRieszGlobalMarkovDensity v = 1 := by
  have himproper := intervalIntegral_tendsto_integral_Ioi
    (f := unitRieszGlobalMarkovDensity)
    (μ := volume) (l := atTop)
    (b := fun n : ℕ => Real.log ((n : ℝ) + 1)) 0
    integrableOn_unitRieszGlobalMarkovDensity_Ioi
    tendsto_unitRieszLogNatBoundary_atTop
  have hprofile :=
    GaloisForLFunctions.RHTower.tendsto_unitRieszLogProfile_atTop.comp
      tendsto_unitRieszLogNatBoundary_atTop
  have hfinite : Tendsto
      (fun n : ℕ => ∫ v in (0 : ℝ)..Real.log ((n : ℝ) + 1),
        unitRieszGlobalMarkovDensity v) atTop (𝓝 1) := by
    apply hprofile.congr'
    filter_upwards [] with n
    simp only [Function.comp_apply]
    exact (intervalIntegral_unitRieszGlobalMarkovDensity_prefix n).symm
  exact tendsto_nhds_unique himproper hfinite

/-- Unit-Riesz Markov density packaged on its natural positive half-line. -/
def unitRieszGlobalHalfLineDensityData : PositiveHalfLineProbabilityDensityData :=
  ⟨unitRieszGlobalMarkovDensity,
    integrableOn_unitRieszGlobalMarkovDensity_Ioi,
    fun v _ => unitRieszGlobalMarkovDensity_nonneg v,
    integral_unitRieszGlobalMarkovDensity_Ioi⟩

/-- Whole-line zero extension of the global unit-Riesz Markov density. -/
def unitRieszGlobalDensityData : RealProbabilityDensityData :=
  positiveHalfLineProbabilityDensityData unitRieszGlobalHalfLineDensityData

/-- Probability clock whose CDF on the positive half-line is the unit-Riesz log profile. -/
def unitRieszGlobalClockProbabilityMeasure : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock unitRieszGlobalDensityData

/-- Global unit-Riesz Markov timing is Rajchman. -/
def unitRieszGlobalRajchmanClockLaw : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw unitRieszGlobalDensityData

/-- Global unit-Riesz timing is Rajchman on every finite nonresonant ray. -/
theorem finiteUnitRieszGlobalClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        unitRieszGlobalClockProbabilityMeasure energy : Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    unitRieszGlobalRajchmanClockLaw energy m

/-- Global unit-Riesz timing is Rajchman on every countable nonresonant ray. -/
theorem countableUnitRieszGlobalClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        unitRieszGlobalClockProbabilityMeasure omega : Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    unitRieszGlobalRajchmanClockLaw omega m

/-- Global unit-Riesz timing makes every nonzero-frequency coordinate Rajchman. -/
theorem countableUnitRieszGlobalClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I]
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure unitRieszGlobalClockProbabilityMeasure
        (fun j => (omega j).1) : Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    unitRieszGlobalRajchmanClockLaw omega i

/-- Global unit-Riesz timing suppresses every nonzero prime-log character ray. -/
theorem primeLogUnitRieszGlobalClockSample_isInfiniteTorusRayRajchman
    (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure unitRieszGlobalClockProbabilityMeasure
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    unitRieszGlobalRajchmanClockLaw m

/-- Global unit-Riesz Markov clock is atomless. -/
theorem unitRieszGlobalClockProbabilityMeasure_nullSingletonClass :
    NullSingletonClass (unitRieszGlobalClockProbabilityMeasure : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass unitRieszGlobalDensityData

/-! ### Normalized corpus energy-profile clocks -/

/-- Squared centred-pole profile, normalized by its exact energy `pi`. -/
def criticalPoleEnergyDensityData : RealProbabilityDensityData := by
  refine ⟨fun y => RHTower.criticalPoleProfile y ^ 2 / Real.pi, ?_, ?_, ?_⟩
  · have h : Integrable (fun y : ℝ => RHTower.criticalPoleProfile y ^ 2) := by
      simpa only [RHTower.criticalPoleProfile_eq] using HTGeometry.integrable_poleProfile_sq
    exact h.div_const Real.pi
  · intro y
    exact div_nonneg (sq_nonneg _) Real.pi_pos.le
  · rw [integral_div, RHTower.integral_criticalPoleProfile_sq]
    exact div_self Real.pi_ne_zero

/-- Probability clock generated by centred-pole profile energy. -/
def criticalPoleEnergyClockProbabilityMeasure : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock criticalPoleEnergyDensityData

/-- Centred-pole energy timing is Rajchman. -/
def criticalPoleEnergyRajchmanClockLaw : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw criticalPoleEnergyDensityData

/-- Two-sided band-leakage Cauchy envelope, normalized by its exact mass `8`. -/
def cauchyPairDensityData (c : ℝ) : RealProbabilityDensityData := by
  refine ⟨fun ξ => RHTower.cauchyPair c ξ / 8, ?_, ?_, ?_⟩
  · exact (RHTower.integrable_cauchyPair c).div_const 8
  · intro ξ
    exact div_nonneg (RHTower.cauchyPair_nonneg c ξ) (by norm_num)
  · rw [integral_div, RHTower.integral_cauchyPair]
    norm_num

/-- Probability clock generated by a normalized two-sided band-leakage envelope. -/
def cauchyPairClockProbabilityMeasure (c : ℝ) : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock (cauchyPairDensityData c)

/-- Every two-sided band-leakage Cauchy clock is Rajchman. -/
def cauchyPairRajchmanClockLaw (c : ℝ) : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw (cauchyPairDensityData c)

/-- Exact positive mass of the squared Sonin reference bump. -/
def soninSquareNormalizer : ℝ := ∫ y : ℝ, RHTower.soninUnitBumpSq y

theorem soninSquareNormalizer_pos : 0 < soninSquareNormalizer :=
  RHTower.integral_soninUnitBumpSq_pos

/-- Squared Sonin reference bump normalized by its exact positive mass. -/
def soninSquareDensityData : RealProbabilityDensityData := by
  refine ⟨fun y => RHTower.soninUnitBumpSq y / soninSquareNormalizer, ?_, ?_, ?_⟩
  · exact RHTower.integrable_soninUnitBumpSq.div_const soninSquareNormalizer
  · intro y
    exact div_nonneg (RHTower.soninUnitBumpSq_nonneg y) soninSquareNormalizer_pos.le
  · rw [integral_div]
    exact div_self soninSquareNormalizer_pos.ne'

/-- Probability clock generated by normalized squared Sonin energy. -/
def soninSquareClockProbabilityMeasure : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock soninSquareDensityData

/-- Squared Sonin energy timing is Rajchman. -/
def soninSquareRajchmanClockLaw : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw soninSquareDensityData

/-- Exact positive `L²` mass of the `n`th Hermite function. -/
def hermiteSquareNormalizer (n : ℕ) : ℝ :=
  ∫ x : ℝ, RHTower.hermiteFun n x ^ 2

theorem hermiteSquareNormalizer_pos (n : ℕ) : 0 < hermiteSquareNormalizer n :=
  RHTower.integral_hermiteFun_sq_pos_line n

/-- Normalized square of the `n`th Hermite function. -/
def hermiteSquareDensityData (n : ℕ) : RealProbabilityDensityData := by
  refine ⟨fun x => RHTower.hermiteFun n x ^ 2 / hermiteSquareNormalizer n, ?_, ?_, ?_⟩
  · exact (RHTower.integrable_hermiteFun_sq n).div_const (hermiteSquareNormalizer n)
  · intro x
    exact div_nonneg (sq_nonneg _) (hermiteSquareNormalizer_pos n).le
  · rw [integral_div]
    exact div_self (hermiteSquareNormalizer_pos n).ne'

/-- Probability clock generated by the normalized `n`th Hermite energy profile. -/
def hermiteSquareClockProbabilityMeasure (n : ℕ) : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock (hermiteSquareDensityData n)

/-- Every Hermite-square energy clock is Rajchman. -/
def hermiteSquareRajchmanClockLaw (n : ℕ) : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw (hermiteSquareDensityData n)

/-- Order-`N` Fejer kernel restricted to one real fundamental window and Haar-normalized. -/
def fejerWindowDensity (N : ℕ) : ℝ → ℝ :=
  (Ioc (-Real.pi) Real.pi).indicator (fun x => torusFejer N x / (2 * Real.pi))

/-- Every fundamental-window Fejer kernel is normalized nonnegative `L¹` data. -/
def fejerWindowDensityData (N : ℕ) : RealProbabilityDensityData := by
  refine ⟨fejerWindowDensity N, ?_, ?_, ?_⟩
  · have hcont : Continuous (fun x => torusFejer N x / (2 * Real.pi)) :=
      (continuous_torusFejer N).div_const _
    have hint : IntegrableOn (fun x => torusFejer N x / (2 * Real.pi))
        (Ioc (-Real.pi) Real.pi) := by
      have h := hcont.intervalIntegrable (μ := volume) (-Real.pi) Real.pi
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le
        (by linarith [Real.pi_pos])] at h
    exact hint.integrable_indicator measurableSet_Ioc
  · intro x
    by_cases hx : x ∈ Ioc (-Real.pi) Real.pi
    · simp only [fejerWindowDensity, indicator_of_mem hx]
      exact div_nonneg (torusFejer_nonneg N x) (by positivity)
    · simp [fejerWindowDensity, hx]
  · rw [fejerWindowDensity, integral_indicator measurableSet_Ioc, integral_div,
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_torusFejer]
    field_simp [Real.pi_ne_zero]

/-- Probability clock generated by the order-`N` fundamental-window Fejer kernel. -/
def fejerWindowClockProbabilityMeasure (N : ℕ) : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock (fejerWindowDensityData N)

/-- Every fundamental-window Fejer clock is Rajchman. -/
def fejerWindowRajchmanClockLaw (N : ℕ) : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw (fejerWindowDensityData N)

/-- Positive tent width not exceeding one circular fundamental half-width. -/
structure TorusTentWidth where
  value : ℝ
  pos : 0 < value
  le_pi : value ≤ Real.pi

instance : Coe TorusTentWidth ℝ := ⟨TorusTentWidth.value⟩

/-- Fundamental-window tent kernel normalized by its exact mass `rho`. -/
def tentWindowDensity (ρ : TorusTentWidth) : ℝ → ℝ :=
  (Ioc (-Real.pi) Real.pi).indicator (fun x => torusTent ρ x / ρ)

/-- Every admissible fundamental-window tent is normalized nonnegative `L¹` data. -/
def tentWindowDensityData (ρ : TorusTentWidth) : RealProbabilityDensityData := by
  refine ⟨tentWindowDensity ρ, ?_, ?_, ?_⟩
  · have hcont : Continuous (fun x => torusTent ρ x / ρ) :=
      (continuous_torusTent ρ).div_const _
    have hint : IntegrableOn (fun x => torusTent ρ x / ρ)
        (Ioc (-Real.pi) Real.pi) := by
      have h := hcont.intervalIntegrable (μ := volume) (-Real.pi) Real.pi
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le
        (by linarith [Real.pi_pos])] at h
    exact hint.integrable_indicator measurableSet_Ioc
  · intro x
    by_cases hx : x ∈ Ioc (-Real.pi) Real.pi
    · simp only [tentWindowDensity, indicator_of_mem hx]
      exact div_nonneg (torusTent_nonneg ρ x) ρ.pos.le
    · simp [tentWindowDensity, hx]
  · rw [tentWindowDensity, integral_indicator measurableSet_Ioc, integral_div,
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      integral_torusTent ρ.pos ρ.le_pi]
    exact div_self ρ.pos.ne'

/-- Probability clock generated by a normalized circular tent. -/
def tentWindowClockProbabilityMeasure (ρ : TorusTentWidth) : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock (tentWindowDensityData ρ)

/-- Every normalized circular tent clock is Rajchman. -/
def tentWindowRajchmanClockLaw (ρ : TorusTentWidth) : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw (tentWindowDensityData ρ)

/-- Compact squared rounding-error density with variance normalizer `12`. -/
def roundingVarianceDensity : ℝ → ℝ :=
  (Ioc (-(1 : ℝ) / 2) (1 / 2)).indicator (fun x => 12 * x ^ 2)

/-- Squared rounding error on its centered fundamental cell is probability-density data. -/
def roundingVarianceDensityData : RealProbabilityDensityData := by
  refine ⟨roundingVarianceDensity, ?_, ?_, ?_⟩
  · have hcont : Continuous (fun x : ℝ => 12 * x ^ 2) := by fun_prop
    have hint : IntegrableOn (fun x : ℝ => 12 * x ^ 2)
        (Ioc (-(1 : ℝ) / 2) (1 / 2)) := by
      have h := hcont.intervalIntegrable (μ := volume) (-(1 : ℝ) / 2) (1 / 2)
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at h
    exact hint.integrable_indicator measurableSet_Ioc
  · intro x
    by_cases hx : x ∈ Ioc (-(1 : ℝ) / 2) (1 / 2)
    · simp only [roundingVarianceDensity, indicator_of_mem hx]
      positivity
    · rw [roundingVarianceDensity, indicator_of_notMem hx]
  · rw [roundingVarianceDensity, integral_indicator measurableSet_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_const_mul,
      HTGeometry.integral_sq_rounding_error]
    norm_num

/-- Probability clock generated by squared nearest-integer rounding error. -/
def roundingVarianceClockProbabilityMeasure : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock roundingVarianceDensityData

/-- Squared rounding-error timing is Rajchman. -/
def roundingVarianceRajchmanClockLaw : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw roundingVarianceDensityData

/-- Compact sine-arch probability density on `[0, pi]`. -/
def sineArchDensity : ℝ → ℝ :=
  (Ioc (0 : ℝ) Real.pi).indicator (fun x => Real.sin x / 2)

/-- The sine arch has exact mass one after division by two. -/
def sineArchDensityData : RealProbabilityDensityData := by
  refine ⟨sineArchDensity, ?_, ?_, ?_⟩
  · have hcont : Continuous (fun x : ℝ => Real.sin x / 2) := by fun_prop
    have hint : IntegrableOn (fun x : ℝ => Real.sin x / 2) (Ioc 0 Real.pi) := by
      have h := hcont.intervalIntegrable (μ := volume) 0 Real.pi
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le] at h
    exact hint.integrable_indicator measurableSet_Ioc
  · intro x
    by_cases hx : x ∈ Ioc (0 : ℝ) Real.pi
    · simp only [sineArchDensity, indicator_of_mem hx]
      exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx.1.le hx.2) (by norm_num)
    · simp [sineArchDensity, hx]
  · rw [sineArchDensity, integral_indicator measurableSet_Ioc, integral_div,
      ← intervalIntegral.integral_of_le Real.pi_pos.le, RHTower.integral_sin_zero_pi]
    norm_num

/-- Probability clock generated by the compact sine arch. -/
def sineArchClockProbabilityMeasure : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock sineArchDensityData

/-- Compact sine-arch timing is Rajchman. -/
def sineArchRajchmanClockLaw : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw sineArchDensityData

/-! #### Torus and atomlessness consequences for normalized energy profiles -/

theorem finiteCriticalPoleEnergyClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure criticalPoleEnergyClockProbabilityMeasure energy :
        Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    criticalPoleEnergyRajchmanClockLaw energy m

theorem countableCriticalPoleEnergyClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure criticalPoleEnergyClockProbabilityMeasure omega :
        Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    criticalPoleEnergyRajchmanClockLaw omega m

theorem countableCriticalPoleEnergyClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I]
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure criticalPoleEnergyClockProbabilityMeasure
        (fun j => (omega j).1) : Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    criticalPoleEnergyRajchmanClockLaw omega i

theorem primeLogCriticalPoleEnergyClockSample_isInfiniteTorusRayRajchman
    (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure criticalPoleEnergyClockProbabilityMeasure
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    criticalPoleEnergyRajchmanClockLaw m

theorem criticalPoleEnergyClockProbabilityMeasure_nullSingletonClass :
    NullSingletonClass (criticalPoleEnergyClockProbabilityMeasure : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass criticalPoleEnergyDensityData

theorem finiteCauchyPairClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (c : ℝ) (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure (cauchyPairClockProbabilityMeasure c) energy :
        Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (cauchyPairRajchmanClockLaw c) energy m

theorem countableCauchyPairClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (c : ℝ) (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure (cauchyPairClockProbabilityMeasure c) omega :
        Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (cauchyPairRajchmanClockLaw c) omega m

theorem countableCauchyPairClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (c : ℝ)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure (cauchyPairClockProbabilityMeasure c)
        (fun j => (omega j).1) : Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (cauchyPairRajchmanClockLaw c) omega i

theorem primeLogCauchyPairClockSample_isInfiniteTorusRayRajchman
    (c : ℝ) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure (cauchyPairClockProbabilityMeasure c)
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (cauchyPairRajchmanClockLaw c) m

theorem cauchyPairClockProbabilityMeasure_nullSingletonClass (c : ℝ) :
    NullSingletonClass (cauchyPairClockProbabilityMeasure c : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass (cauchyPairDensityData c)

theorem finiteSoninSquareClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure soninSquareClockProbabilityMeasure energy :
        Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman soninSquareRajchmanClockLaw energy m

theorem countableSoninSquareClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure soninSquareClockProbabilityMeasure omega :
        Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    soninSquareRajchmanClockLaw omega m

theorem countableSoninSquareClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I]
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure soninSquareClockProbabilityMeasure
        (fun j => (omega j).1) : Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    soninSquareRajchmanClockLaw omega i

theorem primeLogSoninSquareClockSample_isInfiniteTorusRayRajchman
    (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure soninSquareClockProbabilityMeasure
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman soninSquareRajchmanClockLaw m

theorem soninSquareClockProbabilityMeasure_nullSingletonClass :
    NullSingletonClass (soninSquareClockProbabilityMeasure : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass soninSquareDensityData

theorem finiteHermiteSquareClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (n : ℕ) (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure (hermiteSquareClockProbabilityMeasure n) energy :
        Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (hermiteSquareRajchmanClockLaw n) energy m

theorem countableHermiteSquareClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (n : ℕ) (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure (hermiteSquareClockProbabilityMeasure n) omega :
        Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (hermiteSquareRajchmanClockLaw n) omega m

theorem countableHermiteSquareClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (n : ℕ)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure (hermiteSquareClockProbabilityMeasure n)
        (fun j => (omega j).1) : Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (hermiteSquareRajchmanClockLaw n) omega i

theorem primeLogHermiteSquareClockSample_isInfiniteTorusRayRajchman
    (n : ℕ) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure (hermiteSquareClockProbabilityMeasure n)
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (hermiteSquareRajchmanClockLaw n) m

theorem hermiteSquareClockProbabilityMeasure_nullSingletonClass (n : ℕ) :
    NullSingletonClass (hermiteSquareClockProbabilityMeasure n : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass (hermiteSquareDensityData n)

theorem finiteFejerWindowClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (N : ℕ) (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure (fejerWindowClockProbabilityMeasure N) energy :
        Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (fejerWindowRajchmanClockLaw N) energy m

theorem countableFejerWindowClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (N : ℕ) (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure (fejerWindowClockProbabilityMeasure N) omega :
        Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (fejerWindowRajchmanClockLaw N) omega m

theorem countableFejerWindowClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (N : ℕ)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure (fejerWindowClockProbabilityMeasure N)
        (fun j => (omega j).1) : Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (fejerWindowRajchmanClockLaw N) omega i

theorem primeLogFejerWindowClockSample_isInfiniteTorusRayRajchman
    (N : ℕ) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure (fejerWindowClockProbabilityMeasure N)
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (fejerWindowRajchmanClockLaw N) m

theorem fejerWindowClockProbabilityMeasure_nullSingletonClass (N : ℕ) :
    NullSingletonClass (fejerWindowClockProbabilityMeasure N : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass (fejerWindowDensityData N)

theorem finiteTentWindowClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (ρ : TorusTentWidth) (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure (tentWindowClockProbabilityMeasure ρ) energy :
        Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (tentWindowRajchmanClockLaw ρ) energy m

theorem countableTentWindowClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (ρ : TorusTentWidth) (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure (tentWindowClockProbabilityMeasure ρ) omega :
        Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (tentWindowRajchmanClockLaw ρ) omega m

theorem countableTentWindowClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (ρ : TorusTentWidth)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure (tentWindowClockProbabilityMeasure ρ)
        (fun j => (omega j).1) : Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (tentWindowRajchmanClockLaw ρ) omega i

theorem primeLogTentWindowClockSample_isInfiniteTorusRayRajchman
    (ρ : TorusTentWidth) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure (tentWindowClockProbabilityMeasure ρ)
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (tentWindowRajchmanClockLaw ρ) m

theorem tentWindowClockProbabilityMeasure_nullSingletonClass (ρ : TorusTentWidth) :
    NullSingletonClass (tentWindowClockProbabilityMeasure ρ : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass (tentWindowDensityData ρ)

theorem finiteRoundingVarianceClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure roundingVarianceClockProbabilityMeasure energy :
        Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    roundingVarianceRajchmanClockLaw energy m

theorem countableRoundingVarianceClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure roundingVarianceClockProbabilityMeasure omega :
        Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    roundingVarianceRajchmanClockLaw omega m

theorem countableRoundingVarianceClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I]
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure roundingVarianceClockProbabilityMeasure
        (fun j => (omega j).1) : Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    roundingVarianceRajchmanClockLaw omega i

theorem primeLogRoundingVarianceClockSample_isInfiniteTorusRayRajchman
    (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure roundingVarianceClockProbabilityMeasure
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    roundingVarianceRajchmanClockLaw m

theorem roundingVarianceClockProbabilityMeasure_nullSingletonClass :
    NullSingletonClass (roundingVarianceClockProbabilityMeasure : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass roundingVarianceDensityData

theorem finiteSineArchClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure sineArchClockProbabilityMeasure energy :
        Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman sineArchRajchmanClockLaw energy m

theorem countableSineArchClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure sineArchClockProbabilityMeasure omega :
        Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman sineArchRajchmanClockLaw omega m

theorem countableSineArchClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I]
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure sineArchClockProbabilityMeasure
        (fun j => (omega j).1) : Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    sineArchRajchmanClockLaw omega i

theorem primeLogSineArchClockSample_isInfiniteTorusRayRajchman
    (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure sineArchClockProbabilityMeasure
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman sineArchRajchmanClockLaw m

theorem sineArchClockProbabilityMeasure_nullSingletonClass :
    NullSingletonClass (sineArchClockProbabilityMeasure : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass sineArchDensityData

/-! ### Further positive-mass corpus clocks -/

/-- Exact positive mass of the unsquared Sonin reference bump. -/
def soninBumpNormalizer : ℝ := ∫ y : ℝ, RHTower.soninUnitBumpData y

theorem soninBumpNormalizer_pos : 0 < soninBumpNormalizer :=
  RHTower.integral_soninUnitBumpData_pos

/-- The Sonin reference bump itself, normalized to a probability density. -/
def soninBumpDensityData : RealProbabilityDensityData := by
  refine ⟨fun y => RHTower.soninUnitBumpData y / soninBumpNormalizer, ?_, ?_, ?_⟩
  · exact RHTower.integrable_soninUnitBumpData.div_const soninBumpNormalizer
  · intro y
    exact div_nonneg RHTower.soninUnitBumpData.nonneg soninBumpNormalizer_pos.le
  · rw [integral_div]
    exact div_self soninBumpNormalizer_pos.ne'

/-- Probability clock generated by the normalized Sonin reference bump. -/
def soninBumpClockProbabilityMeasure : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock soninBumpDensityData

/-- Unsquared Sonin-bump timing is Rajchman. -/
def soninBumpRajchmanClockLaw : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw soninBumpDensityData

/-- Admissible geometry for an off-line conjugate Cauchy pair. -/
structure OffLineCauchyPairParameters where
  transverse : ℝ
  probe : ℝ
  probe_pos : 0 < probe
  probe_lt_transverse : probe < transverse

/-- Exact positive quadratic mass of an admissible off-line conjugate-pair profile. -/
def offLineCauchyPairEnergyNormalizer (p : OffLineCauchyPairParameters) : ℝ :=
  Real.pi * p.probe ^ 2 /
    (p.transverse * (p.transverse ^ 2 - p.probe ^ 2))

theorem offLineCauchyPairEnergyNormalizer_pos (p : OffLineCauchyPairParameters) :
    0 < offLineCauchyPairEnergyNormalizer p := by
  have hb : 0 < p.transverse := p.probe_pos.trans p.probe_lt_transverse
  have hgap : 0 < p.transverse ^ 2 - p.probe ^ 2 := by
    calc
      p.transverse ^ 2 - p.probe ^ 2 =
          (p.transverse - p.probe) * (p.transverse + p.probe) := by ring
      _ > 0 := mul_pos (sub_pos.mpr p.probe_lt_transverse) (add_pos hb p.probe_pos)
  unfold offLineCauchyPairEnergyNormalizer
  exact div_pos (mul_pos Real.pi_pos (pow_pos p.probe_pos 2)) (mul_pos hb hgap)

/-- Squared off-line conjugate-pair concentration, normalized by its exact quadratic mass. -/
def offLineCauchyPairEnergyDensityData
    (p : OffLineCauchyPairParameters) : RealProbabilityDensityData := by
  refine ⟨fun t =>
      RHTower.lineConjugateCauchyConcentrationProfile p.transverse p.probe t ^ 2 /
        offLineCauchyPairEnergyNormalizer p, ?_, ?_, ?_⟩
  · exact (RHTower.integrable_sq_lineConjugateCauchyConcentrationProfile
      p.probe_pos p.probe_lt_transverse).div_const _
  · intro t
    exact div_nonneg (sq_nonneg _) (offLineCauchyPairEnergyNormalizer_pos p).le
  · rw [integral_div,
      RHTower.integral_sq_lineConjugateCauchyConcentrationProfile
        p.probe_pos p.probe_lt_transverse]
    exact div_self (offLineCauchyPairEnergyNormalizer_pos p).ne'

/-- Probability clock generated by normalized off-line conjugate-pair concentration energy. -/
def offLineCauchyPairEnergyClockProbabilityMeasure
    (p : OffLineCauchyPairParameters) : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock (offLineCauchyPairEnergyDensityData p)

/-- Every admissible off-line conjugate-pair energy clock is Rajchman. -/
def offLineCauchyPairEnergyRajchmanClockLaw
    (p : OffLineCauchyPairParameters) : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw (offLineCauchyPairEnergyDensityData p)

/-- Nondegenerate literal Dunster leading profile in the integrable radial regime. -/
structure RadialPSWFClockParameters where
  frequency : ℝ
  sigma : ℝ
  phase : ℝ
  sigma_sq_le : sigma ^ 2 ≤ 3 / 4
  phase_seed_ne : Real.cos phase ≠ 0

/-- Total mass of the literal leading radial-PSWF arclength density. -/
def radialPSWFClockNormalizer (p : RadialPSWFClockParameters) : ℝ :=
  ∫ t : ℝ, RHTower.radialPSWFLeadingArclengthDensity
    p.frequency p.sigma p.phase t

theorem radialPSWFClockNormalizer_pos (p : RadialPSWFClockParameters) :
    0 < radialPSWFClockNormalizer p := by
  have hsigma : p.sigma ^ 2 < 1 :=
    lt_of_le_of_lt p.sigma_sq_le (by norm_num)
  have hint := RHTower.integrable_radialPSWFLeadingArclengthDensity
    (c := p.frequency) (theta := p.phase) p.sigma_sq_le
  rw [radialPSWFClockNormalizer,
    integral_pos_iff_support_of_nonneg
      (fun _ => RHTower.radialPSWFLeadingArclengthDensity_nonneg hsigma) hint]
  have hcont := RHTower.continuous_radialPSWFLeadingArclengthDensity
    (c := p.frequency) (theta := p.phase) hsigma
  have hopen : IsOpen (Function.support
      (RHTower.radialPSWFLeadingArclengthDensity p.frequency p.sigma p.phase)) :=
    isOpen_ne.preimage hcont
  have hzero : (0 : ℝ) ∈ Function.support
      (RHTower.radialPSWFLeadingArclengthDensity p.frequency p.sigma p.phase) := by
    rw [Function.mem_support]
    have hspeed := RHTower.radialPSWFArclengthSpeed_pos
      (sigma := p.sigma) (t := 0) hsigma
    unfold RHTower.radialPSWFLeadingArclengthDensity
    have hbase : 0 < (1 + (0 : ℝ) ^ 2)⁻¹ := by positivity
    have hphase : 0 < Real.cos
        (p.frequency * RHTower.radialPSWFArclengthPhase p.sigma 0 + p.phase) ^ 2 := by
      simpa [RHTower.radialPSWFArclengthPhase] using
        sq_pos_of_ne_zero p.phase_seed_ne
    exact ne_of_gt (mul_pos
      (mul_pos (mul_pos (div_pos (by norm_num) Real.pi_pos) hbase)
        (inv_pos.mpr hspeed)) hphase)
  exact hopen.measure_pos volume ⟨0, hzero⟩

/-- Literal leading radial-PSWF density normalized by its proved positive mass. -/
def radialPSWFClockDensityData
    (p : RadialPSWFClockParameters) : RealProbabilityDensityData := by
  have hsigma : p.sigma ^ 2 < 1 :=
    lt_of_le_of_lt p.sigma_sq_le (by norm_num)
  refine ⟨fun t => RHTower.radialPSWFLeadingArclengthDensity
      p.frequency p.sigma p.phase t / radialPSWFClockNormalizer p, ?_, ?_, ?_⟩
  · exact (RHTower.integrable_radialPSWFLeadingArclengthDensity
      (c := p.frequency) (theta := p.phase) p.sigma_sq_le).div_const _
  · intro t
    exact div_nonneg (RHTower.radialPSWFLeadingArclengthDensity_nonneg hsigma)
      (radialPSWFClockNormalizer_pos p).le
  · rw [integral_div]
    exact div_self (radialPSWFClockNormalizer_pos p).ne'

/-- Probability clock generated by a normalized literal leading radial-PSWF profile. -/
def radialPSWFClockProbabilityMeasure
    (p : RadialPSWFClockParameters) : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock (radialPSWFClockDensityData p)

/-- Every nondegenerate literal leading radial-PSWF clock is Rajchman. -/
def radialPSWFRajchmanClockLaw (p : RadialPSWFClockParameters) : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw (radialPSWFClockDensityData p)

/-- A nonzero compactly supported smooth logarithmic test function. -/
abbrev NonzeroFieldOneCompactSmoothLog :=
  {h : RHTower.FieldOneCompactSmoothLog // h ≠ 0}

/-- Positive real energy density of the field-one additive Schwartz lift. -/
def fieldOneLogSchwartzEnergyDensity
    (h : NonzeroFieldOneCompactSmoothLog) (x : ℝ) : ℝ :=
  ‖RHTower.fieldOnePositiveLogSchwartzRaw h.1 x‖ ^ 2

theorem continuous_fieldOneLogSchwartzEnergyDensity
    (h : NonzeroFieldOneCompactSmoothLog) :
    Continuous (fieldOneLogSchwartzEnergyDensity h) :=
  (RHTower.fieldOnePositiveLogSchwartzRaw_contDiff h.1).continuous.norm.pow 2

theorem hasCompactSupport_fieldOneLogSchwartzEnergyDensity
    (h : NonzeroFieldOneCompactSmoothLog) :
    HasCompactSupport (fieldOneLogSchwartzEnergyDensity h) := by
  refine (RHTower.fieldOnePositiveLogSchwartzRaw_hasCompactSupport h.1).mono ?_
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro hzero
  apply hx
  unfold fieldOneLogSchwartzEnergyDensity
  simp [hzero]

theorem integrable_fieldOneLogSchwartzEnergyDensity
    (h : NonzeroFieldOneCompactSmoothLog) :
    Integrable (fieldOneLogSchwartzEnergyDensity h) :=
  (continuous_fieldOneLogSchwartzEnergyDensity h).integrable_of_hasCompactSupport
    (hasCompactSupport_fieldOneLogSchwartzEnergyDensity h)

theorem exists_fieldOneLogSchwartzEnergyDensity_pos
    (h : NonzeroFieldOneCompactSmoothLog) :
    ∃ x : ℝ, 0 < fieldOneLogSchwartzEnergyDensity h x := by
  have hex : ∃ y : ℝ, h.1 y ≠ 0 := by
    by_contra! hall
    apply h.2
    ext y
    exact hall y
  obtain ⟨y, hy⟩ := hex
  refine ⟨Real.exp y, ?_⟩
  have hraw : RHTower.fieldOnePositiveLogSchwartzRaw h.1 (Real.exp y) ≠ 0 := by
    simp only [RHTower.fieldOnePositiveLogSchwartzRaw,
      if_pos (Real.exp_pos y), Real.log_exp]
    exact mul_ne_zero (ofReal_ne_zero.mpr (Real.exp_ne_zero _)) hy
  exact sq_pos_of_pos (norm_pos_iff.mpr hraw)

/-- Positive total energy of a nonzero field-one additive Schwartz lift. -/
def fieldOneLogSchwartzEnergyNormalizer
    (h : NonzeroFieldOneCompactSmoothLog) : ℝ :=
  ∫ x : ℝ, fieldOneLogSchwartzEnergyDensity h x

theorem fieldOneLogSchwartzEnergyNormalizer_pos
    (h : NonzeroFieldOneCompactSmoothLog) :
    0 < fieldOneLogSchwartzEnergyNormalizer h := by
  rw [fieldOneLogSchwartzEnergyNormalizer]
  apply (integral_pos_iff_support_of_nonneg
    (fun x => show 0 ≤ fieldOneLogSchwartzEnergyDensity h x from by
      unfold fieldOneLogSchwartzEnergyDensity
      exact sq_nonneg _)
    (integrable_fieldOneLogSchwartzEnergyDensity h)).2
  have hopen : IsOpen (Function.support (fieldOneLogSchwartzEnergyDensity h)) :=
    isOpen_ne.preimage (continuous_fieldOneLogSchwartzEnergyDensity h)
  obtain ⟨x, hx⟩ := exists_fieldOneLogSchwartzEnergyDensity_pos h
  exact hopen.measure_pos volume ⟨x, ne_of_gt hx⟩

/-- Normalized energy of a nonzero field-one additive Schwartz lift. -/
def fieldOneLogSchwartzEnergyDensityData
    (h : NonzeroFieldOneCompactSmoothLog) : RealProbabilityDensityData := by
  refine ⟨fun x => fieldOneLogSchwartzEnergyDensity h x /
      fieldOneLogSchwartzEnergyNormalizer h, ?_, ?_, ?_⟩
  · exact (integrable_fieldOneLogSchwartzEnergyDensity h).div_const _
  · intro x
    exact div_nonneg (sq_nonneg _) (fieldOneLogSchwartzEnergyNormalizer_pos h).le
  · rw [integral_div]
    exact div_self (fieldOneLogSchwartzEnergyNormalizer_pos h).ne'

/-- Probability clock generated by field-one additive Schwartz energy. -/
def fieldOneLogSchwartzEnergyClockProbabilityMeasure
    (h : NonzeroFieldOneCompactSmoothLog) : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock (fieldOneLogSchwartzEnergyDensityData h)

/-- Every nonzero field-one additive Schwartz-energy clock is Rajchman. -/
def fieldOneLogSchwartzEnergyRajchmanClockLaw
    (h : NonzeroFieldOneCompactSmoothLog) : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw (fieldOneLogSchwartzEnergyDensityData h)

/-- The first genuine prime cell makes outgoing quantile boundary `2 → 3` strictly grow. -/
theorem ccmOutgoingPrimeQuantileBoundary_two_lt_three :
    RHTower.ccmOutgoingPrimeQuantileBoundary 2 <
      RHTower.ccmOutgoingPrimeQuantileBoundary 3 := by
  have hP := RHTower.ccmOutgoingPrimeCumulative_nonneg 2
  have hw : 0 < RHTower.criticalMellinAtomWeight 2 :=
    RHTower.criticalMellinAtomWeight_pos Nat.prime_two.isPrimePow
  have hsucc : RHTower.ccmOutgoingPrimeCumulative 3 =
      RHTower.ccmOutgoingPrimeCumulative 2 + RHTower.criticalMellinAtomWeight 2 := by
    simpa using RHTower.ccmOutgoingPrimeCumulative_succ 2
  have hcum : RHTower.ccmOutgoingPrimeCumulative 2 <
      RHTower.ccmOutgoingPrimeCumulative 3 := by
    rw [hsucc]
    linarith
  have hleft : 0 < 1 + RHTower.ccmOutgoingPrimeCumulative 2 / 2 := by linarith
  have hright : 0 < 1 + RHTower.ccmOutgoingPrimeCumulative 3 / 2 := by linarith
  have hlog := Real.strictMonoOn_log hleft hright (by linarith)
  unfold RHTower.ccmOutgoingPrimeQuantileBoundary
  exact mul_lt_mul_of_pos_left hlog (by norm_num)

/-- Every finite outgoing arithmetic head containing the first prime cell has positive
reciprocal-Gamma chi-square mass. -/
theorem ccmOutgoingQuantileGammaChiSquare_pos {N : ℕ} (hN : 3 ≤ N) :
    0 < RHTower.ccmOutgoingQuantileGammaChiSquare N := by
  let a := RHTower.ccmOutgoingPrimeQuantileBoundary 2 - Real.log 2
  let b := RHTower.ccmOutgoingPrimeQuantileBoundary 3 - Real.log 2
  let U : Set ℝ := Ioo a b \ {0}
  have hab : a < b := by
    dsimp only [a, b]
    linarith [ccmOutgoingPrimeQuantileBoundary_two_lt_three]
  have hUopen : IsOpen U := isOpen_Ioo.sdiff isClosed_singleton
  have hUne : U.Nonempty := by
    let x := (2 * a + b) / 3
    let z := (a + 2 * b) / 3
    have hx : x ∈ Ioo a b := by
      dsimp only [x]
      constructor <;> linarith
    have hz : z ∈ Ioo a b := by
      dsimp only [z]
      constructor <;> linarith
    have hxz : x ≠ z := by
      dsimp only [x, z]
      linarith
    by_cases hx0 : x = 0
    · exact ⟨z, hz, by simpa [hx0] using hxz.symm⟩
    · exact ⟨x, hx, by simpa using hx0⟩
  have hUpos : 0 < volume U := hUopen.measure_pos volume hUne
  have hnonneg : ∀ r : ℝ,
      0 ≤ RHTower.ccmOutgoingQuantileDisplacementDensity N r ^ 2 *
        RHTower.ccmGammaHigherBinetDualDensity |r| := by
    intro r
    exact mul_nonneg (sq_nonneg _)
      (RHTower.ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r))
  have hsub : U ⊆ Function.support (fun r : ℝ =>
      RHTower.ccmOutgoingQuantileDisplacementDensity N r ^ 2 *
        RHTower.ccmGammaHigherBinetDualDensity |r|) := by
    intro r hr
    have hrI : r ∈ Ioc a b := ⟨hr.1.1, hr.1.2.le⟩
    have hcell : 0 < RHTower.ccmOutgoingQuantileDisplacementCellDensity 2 r := by
      rw [RHTower.ccmOutgoingQuantileDisplacementCellDensity, indicator_of_mem]
      · positivity
      · simpa only [a, b, Nat.reduceAdd, Nat.cast_ofNat] using hrI
    have hdisp : 0 < RHTower.ccmOutgoingQuantileDisplacementDensity N r := by
      unfold RHTower.ccmOutgoingQuantileDisplacementDensity
      exact Finset.sum_pos'
        (fun n _ => RHTower.ccmOutgoingQuantileDisplacementCellDensity_nonneg n r)
        ⟨2, Finset.mem_range.mpr (by omega), hcell⟩
    have hr0 : r ≠ 0 := by simpa using hr.2
    have hdual : 0 < RHTower.ccmGammaHigherBinetDualDensity |r| := by
      unfold RHTower.ccmGammaHigherBinetDualDensity
      exact mul_pos (Real.exp_pos _)
        (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity)))
    rw [Function.mem_support]
    exact ne_of_gt (mul_pos (sq_pos_of_pos hdisp) hdual)
  unfold RHTower.ccmOutgoingQuantileGammaChiSquare
  rw [integral_pos_iff_support_of_nonneg hnonneg
    (RHTower.integrable_ccmOutgoingQuantileGammaChiSquareDensity N)]
  exact hUpos.trans_le (measure_mono hsub)

/-- Finite arithmetic heads large enough to contain the first prime cell. -/
structure OutgoingQuantileChiSquareClockIndex where
  value : ℕ
  three_le : 3 ≤ value

/-- Reciprocal-Gamma outgoing-head chi-square density, normalized by its strict mass. -/
def outgoingQuantileChiSquareDensityData
    (N : OutgoingQuantileChiSquareClockIndex) : RealProbabilityDensityData := by
  refine ⟨fun r =>
      (RHTower.ccmOutgoingQuantileDisplacementDensity N.value r ^ 2 *
        RHTower.ccmGammaHigherBinetDualDensity |r|) /
          RHTower.ccmOutgoingQuantileGammaChiSquare N.value, ?_, ?_, ?_⟩
  · exact (RHTower.integrable_ccmOutgoingQuantileGammaChiSquareDensity N.value).div_const _
  · intro r
    exact div_nonneg
      (mul_nonneg (sq_nonneg _)
        (RHTower.ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r)))
      (ccmOutgoingQuantileGammaChiSquare_pos N.three_le).le
  · rw [integral_div]
    change RHTower.ccmOutgoingQuantileGammaChiSquare N.value /
      RHTower.ccmOutgoingQuantileGammaChiSquare N.value = 1
    exact div_self (ccmOutgoingQuantileGammaChiSquare_pos N.three_le).ne'

/-- Probability clock generated by normalized outgoing-head arithmetic chi-square. -/
def outgoingQuantileChiSquareClockProbabilityMeasure
    (N : OutgoingQuantileChiSquareClockIndex) : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock (outgoingQuantileChiSquareDensityData N)

/-- Every outgoing-head arithmetic chi-square clock containing the first prime cell is Rajchman. -/
def outgoingQuantileChiSquareRajchmanClockLaw
    (N : OutgoingQuantileChiSquareClockIndex) : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw (outgoingQuantileChiSquareDensityData N)

/-- Arbitrary oscillator separation constant observed on a positive symmetric window. -/
structure OscillatorWindowParameters where
  separation : ℝ
  width : ℝ
  width_pos : 0 < width

/-- Exact positive square mass of an arbitrary oscillator profile on its observation window. -/
def oscillatorWindowNormalizer (p : OscillatorWindowParameters) : ℝ :=
  ∫ x in (-p.width)..p.width, RHTower.oscProfile p.separation x ^ 2

theorem oscillatorWindowNormalizer_pos (p : OscillatorWindowParameters) :
    0 < oscillatorWindowNormalizer p :=
  RHTower.integral_oscProfile_sq_pos p.separation p.width_pos

/-- Arbitrary-separation oscillator square, windowed and normalized to unit mass. -/
def oscillatorWindowDensity (p : OscillatorWindowParameters) : ℝ → ℝ :=
  (Ioc (-p.width) p.width).indicator
    (fun x => RHTower.oscProfile p.separation x ^ 2 / oscillatorWindowNormalizer p)

def oscillatorWindowDensityData
    (p : OscillatorWindowParameters) : RealProbabilityDensityData := by
  refine ⟨oscillatorWindowDensity p, ?_, ?_, ?_⟩
  · have hcont : Continuous (fun x =>
        RHTower.oscProfile p.separation x ^ 2 / oscillatorWindowNormalizer p) :=
      ((RHTower.continuous_oscProfile p.separation).pow 2).div_const _
    have hint : IntegrableOn (fun x =>
        RHTower.oscProfile p.separation x ^ 2 / oscillatorWindowNormalizer p)
        (Ioc (-p.width) p.width) := by
      have h := hcont.intervalIntegrable (μ := volume) (-p.width) p.width
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [p.width_pos])] at h
    exact hint.integrable_indicator measurableSet_Ioc
  · intro x
    by_cases hx : x ∈ Ioc (-p.width) p.width
    · simp only [oscillatorWindowDensity, indicator_of_mem hx]
      exact div_nonneg (sq_nonneg _) (oscillatorWindowNormalizer_pos p).le
    · simp [oscillatorWindowDensity, hx]
  · rw [oscillatorWindowDensity, integral_indicator measurableSet_Ioc, integral_div,
      ← intervalIntegral.integral_of_le (by linarith [p.width_pos])]
    exact div_self (oscillatorWindowNormalizer_pos p).ne'

/-- Probability clock generated by arbitrary oscillator-window energy. -/
def oscillatorWindowClockProbabilityMeasure
    (p : OscillatorWindowParameters) : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock (oscillatorWindowDensityData p)

/-- Every arbitrary-separation oscillator-window clock is Rajchman. -/
def oscillatorWindowRajchmanClockLaw
    (p : OscillatorWindowParameters) : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw (oscillatorWindowDensityData p)

/-- One-sided Sonin annulus interval. -/
structure SoninPositiveBumpParameters where
  lower : ℝ
  upper : ℝ
  lower_lt_upper : lower < upper

/-- Total mass of the one-sided Sonin annulus bump. -/
def soninPositiveBumpNormalizer (p : SoninPositiveBumpParameters) : ℝ :=
  ∫ x : ℝ, RHTower.soninPositiveBump p.lower p.upper p.lower_lt_upper x

theorem soninPositiveBumpNormalizer_pos (p : SoninPositiveBumpParameters) :
    0 < soninPositiveBumpNormalizer p := by
  have hint : Integrable
      (RHTower.soninPositiveBump p.lower p.upper p.lower_lt_upper) :=
    (RHTower.contDiff_soninPositiveBump p.lower p.upper p.lower_lt_upper).continuous
      |>.integrable_of_hasCompactSupport
        (RHTower.hasCompactSupport_soninPositiveBump
          p.lower p.upper p.lower_lt_upper)
  rw [soninPositiveBumpNormalizer]
  apply (integral_pos_iff_support_of_nonneg
    (fun x => show 0 ≤ RHTower.soninPositiveBump
        p.lower p.upper p.lower_lt_upper x from
      (RHTower.soninAnnulusBumpData
        p.lower p.upper p.lower_lt_upper).nonneg) hint).2
  have hcont :=
    (RHTower.contDiff_soninPositiveBump p.lower p.upper p.lower_lt_upper).continuous
  have hopen : IsOpen (Function.support
      (RHTower.soninPositiveBump p.lower p.upper p.lower_lt_upper)) :=
    isOpen_ne.preimage hcont
  have hmid : (p.lower + p.upper) / 2 ∈ Function.support
      (RHTower.soninPositiveBump p.lower p.upper p.lower_lt_upper) := by
    rw [Function.mem_support]
    have hone : RHTower.soninAnnulusBumpData
        p.lower p.upper p.lower_lt_upper ((p.lower + p.upper) / 2) = 1 := by
      refine (RHTower.soninAnnulusBumpData
        p.lower p.upper p.lower_lt_upper).one_of_mem_closedBall ?_
      rw [Metric.mem_closedBall, dist_self]
      exact (RHTower.soninAnnulusBumpData
        p.lower p.upper p.lower_lt_upper).rIn_pos.le
    simp [RHTower.soninPositiveBump, hone]
  exact hopen.measure_pos volume ⟨_, hmid⟩

/-- One-sided Sonin annulus bump normalized by its proved positive mass. -/
def soninPositiveBumpDensityData
    (p : SoninPositiveBumpParameters) : RealProbabilityDensityData := by
  refine ⟨fun x => RHTower.soninPositiveBump p.lower p.upper p.lower_lt_upper x /
      soninPositiveBumpNormalizer p, ?_, ?_, ?_⟩
  · exact ((RHTower.contDiff_soninPositiveBump p.lower p.upper p.lower_lt_upper).continuous
      |>.integrable_of_hasCompactSupport
        (RHTower.hasCompactSupport_soninPositiveBump
          p.lower p.upper p.lower_lt_upper)).div_const _
  · intro x
    exact div_nonneg
      (RHTower.soninAnnulusBumpData p.lower p.upper p.lower_lt_upper).nonneg
      (soninPositiveBumpNormalizer_pos p).le
  · rw [integral_div]
    exact div_self (soninPositiveBumpNormalizer_pos p).ne'

/-- Probability clock generated by a one-sided Sonin annulus bump. -/
def soninPositiveBumpClockProbabilityMeasure
    (p : SoninPositiveBumpParameters) : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock (soninPositiveBumpDensityData p)

/-- Every one-sided Sonin annulus-bump clock is Rajchman. -/
def soninPositiveBumpRajchmanClockLaw
    (p : SoninPositiveBumpParameters) : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw (soninPositiveBumpDensityData p)

/-- Positive theta-square index used by the physical truncated logarithmic atom. -/
structure PositiveThetaSquareIndex where
  value : ℕ
  one_le : 1 ≤ value

/-- Real nonnegative mass profile of one physical positive theta-square atom. -/
def thetaPositiveSquareNormDensity (m : PositiveThetaSquareIndex) (u : ℝ) : ℝ :=
  ‖RHTower.thetaPositiveSquareLogAtom m.value u‖

theorem integrable_thetaPositiveSquareNormDensity (m : PositiveThetaSquareIndex) :
    Integrable (thetaPositiveSquareNormDensity m) :=
  (RHTower.thetaPositiveSquareLogAtom_integrable m.one_le).norm

/-- Total `L¹` mass of a physical positive theta-square atom. -/
def thetaPositiveSquareNormalizer (m : PositiveThetaSquareIndex) : ℝ :=
  ∫ u : ℝ, thetaPositiveSquareNormDensity m u

theorem thetaPositiveSquareNormalizer_pos (m : PositiveThetaSquareIndex) :
    0 < thetaPositiveSquareNormalizer m := by
  have hnonneg : ∀ u : ℝ, 0 ≤ thetaPositiveSquareNormDensity m u :=
    fun _ => norm_nonneg _
  have hsub : Ioo (0 : ℝ) 1 ⊆ Function.support (thetaPositiveSquareNormDensity m) := by
    intro u hu
    rw [Function.mem_support]
    unfold thetaPositiveSquareNormDensity RHTower.thetaPositiveSquareLogAtom
      RHTower.positiveLogTruncation
    rw [indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu.1)]
    exact norm_ne_zero_iff.mpr (ofReal_ne_zero.mpr (by
      unfold RHTower.thetaSquareLogAtom
      positivity))
  have hIpos : 0 < volume (Ioo (0 : ℝ) 1) :=
    isOpen_Ioo.measure_pos volume ⟨1 / 2, by norm_num⟩
  rw [thetaPositiveSquareNormalizer,
    integral_pos_iff_support_of_nonneg hnonneg
      (integrable_thetaPositiveSquareNormDensity m)]
  exact hIpos.trans_le (measure_mono hsub)

/-- Existing superexponential atom estimate bounds the clock normalizer. -/
theorem thetaPositiveSquareNormalizer_le (m : PositiveThetaSquareIndex) :
    thetaPositiveSquareNormalizer m ≤
      Real.exp (-Real.pi * (m.value : ℝ) ^ 2) :=
  RHTower.integral_norm_thetaPositiveSquareLogAtom_le m.one_le

/-- Physical positive theta-square atom normalized to a probability density. -/
def thetaPositiveSquareDensityData
    (m : PositiveThetaSquareIndex) : RealProbabilityDensityData := by
  refine ⟨fun u => thetaPositiveSquareNormDensity m u /
      thetaPositiveSquareNormalizer m, ?_, ?_, ?_⟩
  · exact (integrable_thetaPositiveSquareNormDensity m).div_const _
  · intro u
    exact div_nonneg (norm_nonneg _) (thetaPositiveSquareNormalizer_pos m).le
  · rw [integral_div]
    exact div_self (thetaPositiveSquareNormalizer_pos m).ne'

/-- Probability clock generated by one normalized physical positive theta-square atom. -/
def thetaPositiveSquareClockProbabilityMeasure
    (m : PositiveThetaSquareIndex) : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock (thetaPositiveSquareDensityData m)

/-- Every physical positive theta-square clock is Rajchman. -/
def thetaPositiveSquareRajchmanClockLaw
    (m : PositiveThetaSquareIndex) : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw (thetaPositiveSquareDensityData m)

/-- Total Fourier-energy mass of an arbitrary positive-mass annulus amplitude. -/
def annulusAmplitudeSpectralNormalizer {b c : ℝ}
    (A : RHTower.AnnulusAmplitude b c) : ℝ :=
  ∫ eta : ℝ, A.ampSpectralDensity eta

theorem annulusAmplitudeSpectralNormalizer_pos {b c : ℝ}
    (A : RHTower.AnnulusAmplitude b c) :
    0 < annulusAmplitudeSpectralNormalizer A := by
  have hcontFourier : Continuous (𝓕 (fun x : ℝ => (A.toFun x : ℂ))) :=
    RHTower.continuous_fourier_of_integrable A.integrable.ofReal
  have hcont : Continuous A.ampSpectralDensity := by
    unfold RHTower.AnnulusAmplitude.ampSpectralDensity
    exact hcontFourier.norm.pow 2
  rw [annulusAmplitudeSpectralNormalizer,
    integral_pos_iff_support_of_nonneg A.ampSpectralDensity_nonneg
      A.integrable_ampSpectralDensity]
  have hopen : IsOpen (Function.support A.ampSpectralDensity) :=
    isOpen_ne.preimage hcont
  have hzero : (0 : ℝ) ∈ Function.support A.ampSpectralDensity := by
    rw [Function.mem_support]
    unfold RHTower.AnnulusAmplitude.ampSpectralDensity
    rw [RHTower.fourier_zero_eq_integral]
    have hIntegral := integral_ofReal (𝕜 := ℂ) (μ := volume) (f := A.toFun)
    have hIntegralNe : (∫ x : ℝ, (A.toFun x : ℂ)) ≠ 0 := by
      intro hzero
      exact (ofReal_ne_zero.mpr A.mass_pos'.ne') (hIntegral.symm.trans hzero)
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hIntegralNe)
  exact hopen.measure_pos volume ⟨0, hzero⟩

/-- Fourier energy of an arbitrary positive-mass annulus amplitude, normalized to unit mass. -/
def annulusAmplitudeSpectralDensityData {b c : ℝ}
    (A : RHTower.AnnulusAmplitude b c) : RealProbabilityDensityData := by
  refine ⟨fun eta => A.ampSpectralDensity eta /
      annulusAmplitudeSpectralNormalizer A, ?_, ?_, ?_⟩
  · exact A.integrable_ampSpectralDensity.div_const _
  · intro eta
    exact div_nonneg (A.ampSpectralDensity_nonneg eta)
      (annulusAmplitudeSpectralNormalizer_pos A).le
  · rw [integral_div]
    exact div_self (annulusAmplitudeSpectralNormalizer_pos A).ne'

/-- Probability clock generated by the spectral energy of an arbitrary annulus amplitude. -/
def annulusAmplitudeSpectralClockProbabilityMeasure {b c : ℝ}
    (A : RHTower.AnnulusAmplitude b c) : ProbabilityMeasure ℝ :=
  realProbabilityDensityClock (annulusAmplitudeSpectralDensityData A)

/-- Every positive-mass annulus amplitude has a Rajchman spectral-energy clock. -/
def annulusAmplitudeSpectralRajchmanClockLaw {b c : ℝ}
    (A : RHTower.AnnulusAmplitude b c) : RajchmanClockLaw :=
  realProbabilityDensityRajchmanClockLaw (annulusAmplitudeSpectralDensityData A)

/-! #### Torus and atomlessness consequences -/

theorem finiteSoninBumpClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure soninBumpClockProbabilityMeasure energy :
        Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman soninBumpRajchmanClockLaw energy m

theorem countableSoninBumpClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure soninBumpClockProbabilityMeasure omega :
        Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman soninBumpRajchmanClockLaw omega m

theorem countableSoninBumpClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I]
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure soninBumpClockProbabilityMeasure
        (fun j => (omega j).1) : Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman soninBumpRajchmanClockLaw omega i

theorem primeLogSoninBumpClockSample_isInfiniteTorusRayRajchman
    (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure soninBumpClockProbabilityMeasure
        (fun p : Nat.Primes => Real.log (p : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman soninBumpRajchmanClockLaw m

theorem soninBumpClockProbabilityMeasure_nullSingletonClass :
    NullSingletonClass (soninBumpClockProbabilityMeasure : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass soninBumpDensityData

theorem finiteOffLineCauchyPairEnergyClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (p : OffLineCauchyPairParameters) (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        (offLineCauchyPairEnergyClockProbabilityMeasure p) energy : Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (offLineCauchyPairEnergyRajchmanClockLaw p) energy m

theorem countableOffLineCauchyPairEnergyClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (p : OffLineCauchyPairParameters) (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (offLineCauchyPairEnergyClockProbabilityMeasure p) omega :
          Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (offLineCauchyPairEnergyRajchmanClockLaw p) omega m

theorem countableOffLineCauchyPairEnergyClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (p : OffLineCauchyPairParameters)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (offLineCauchyPairEnergyClockProbabilityMeasure p) (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (offLineCauchyPairEnergyRajchmanClockLaw p) omega i

theorem primeLogOffLineCauchyPairEnergyClockSample_isInfiniteTorusRayRajchman
    (p : OffLineCauchyPairParameters) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (offLineCauchyPairEnergyClockProbabilityMeasure p)
        (fun q : Nat.Primes => Real.log (q : ℝ)) : Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (offLineCauchyPairEnergyRajchmanClockLaw p) m

theorem offLineCauchyPairEnergyClockProbabilityMeasure_nullSingletonClass
    (p : OffLineCauchyPairParameters) :
    NullSingletonClass (offLineCauchyPairEnergyClockProbabilityMeasure p : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass (offLineCauchyPairEnergyDensityData p)

theorem finiteRadialPSWFClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (p : RadialPSWFClockParameters) (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure (radialPSWFClockProbabilityMeasure p) energy :
        Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (radialPSWFRajchmanClockLaw p) energy m

theorem countableRadialPSWFClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (p : RadialPSWFClockParameters) (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure (radialPSWFClockProbabilityMeasure p) omega :
        Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (radialPSWFRajchmanClockLaw p) omega m

theorem countableRadialPSWFClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (p : RadialPSWFClockParameters)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure (radialPSWFClockProbabilityMeasure p)
        (fun j => (omega j).1) : Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (radialPSWFRajchmanClockLaw p) omega i

theorem primeLogRadialPSWFClockSample_isInfiniteTorusRayRajchman
    (p : RadialPSWFClockParameters) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure (radialPSWFClockProbabilityMeasure p)
        (fun q : Nat.Primes => Real.log (q : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (radialPSWFRajchmanClockLaw p) m

theorem radialPSWFClockProbabilityMeasure_nullSingletonClass
    (p : RadialPSWFClockParameters) :
    NullSingletonClass (radialPSWFClockProbabilityMeasure p : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass (radialPSWFClockDensityData p)

theorem finiteFieldOneLogSchwartzEnergyClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (h : NonzeroFieldOneCompactSmoothLog) (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        (fieldOneLogSchwartzEnergyClockProbabilityMeasure h) energy :
          Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (fieldOneLogSchwartzEnergyRajchmanClockLaw h) energy m

theorem countableFieldOneLogSchwartzEnergyClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (h : NonzeroFieldOneCompactSmoothLog) (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (fieldOneLogSchwartzEnergyClockProbabilityMeasure h) omega :
          Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (fieldOneLogSchwartzEnergyRajchmanClockLaw h) omega m

theorem countableFieldOneLogSchwartzEnergyClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (h : NonzeroFieldOneCompactSmoothLog)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (fieldOneLogSchwartzEnergyClockProbabilityMeasure h) (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (fieldOneLogSchwartzEnergyRajchmanClockLaw h) omega i

theorem primeLogFieldOneLogSchwartzEnergyClockSample_isInfiniteTorusRayRajchman
    (h : NonzeroFieldOneCompactSmoothLog) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (fieldOneLogSchwartzEnergyClockProbabilityMeasure h)
        (fun q : Nat.Primes => Real.log (q : ℝ)) : Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (fieldOneLogSchwartzEnergyRajchmanClockLaw h) m

theorem fieldOneLogSchwartzEnergyClockProbabilityMeasure_nullSingletonClass
    (h : NonzeroFieldOneCompactSmoothLog) :
    NullSingletonClass (fieldOneLogSchwartzEnergyClockProbabilityMeasure h : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass (fieldOneLogSchwartzEnergyDensityData h)

theorem finiteOutgoingQuantileChiSquareClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (N : OutgoingQuantileChiSquareClockIndex) (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        (outgoingQuantileChiSquareClockProbabilityMeasure N) energy :
          Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (outgoingQuantileChiSquareRajchmanClockLaw N) energy m

theorem countableOutgoingQuantileChiSquareClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (N : OutgoingQuantileChiSquareClockIndex) (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (outgoingQuantileChiSquareClockProbabilityMeasure N) omega :
          Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (outgoingQuantileChiSquareRajchmanClockLaw N) omega m

theorem countableOutgoingQuantileChiSquareClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (N : OutgoingQuantileChiSquareClockIndex)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (outgoingQuantileChiSquareClockProbabilityMeasure N) (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (outgoingQuantileChiSquareRajchmanClockLaw N) omega i

theorem primeLogOutgoingQuantileChiSquareClockSample_isInfiniteTorusRayRajchman
    (N : OutgoingQuantileChiSquareClockIndex) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (outgoingQuantileChiSquareClockProbabilityMeasure N)
        (fun q : Nat.Primes => Real.log (q : ℝ)) : Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (outgoingQuantileChiSquareRajchmanClockLaw N) m

theorem outgoingQuantileChiSquareClockProbabilityMeasure_nullSingletonClass
    (N : OutgoingQuantileChiSquareClockIndex) :
    NullSingletonClass (outgoingQuantileChiSquareClockProbabilityMeasure N : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass (outgoingQuantileChiSquareDensityData N)

theorem finiteOscillatorWindowClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (p : OscillatorWindowParameters) (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure (oscillatorWindowClockProbabilityMeasure p)
        energy : Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (oscillatorWindowRajchmanClockLaw p) energy m

theorem countableOscillatorWindowClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (p : OscillatorWindowParameters) (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure (oscillatorWindowClockProbabilityMeasure p)
        omega : Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (oscillatorWindowRajchmanClockLaw p) omega m

theorem countableOscillatorWindowClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (p : OscillatorWindowParameters)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure (oscillatorWindowClockProbabilityMeasure p)
        (fun j => (omega j).1) : Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (oscillatorWindowRajchmanClockLaw p) omega i

theorem primeLogOscillatorWindowClockSample_isInfiniteTorusRayRajchman
    (p : OscillatorWindowParameters) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure (oscillatorWindowClockProbabilityMeasure p)
        (fun q : Nat.Primes => Real.log (q : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (oscillatorWindowRajchmanClockLaw p) m

theorem oscillatorWindowClockProbabilityMeasure_nullSingletonClass
    (p : OscillatorWindowParameters) :
    NullSingletonClass (oscillatorWindowClockProbabilityMeasure p : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass (oscillatorWindowDensityData p)

theorem finiteSoninPositiveBumpClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (p : SoninPositiveBumpParameters) (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure (soninPositiveBumpClockProbabilityMeasure p)
        energy : Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (soninPositiveBumpRajchmanClockLaw p) energy m

theorem countableSoninPositiveBumpClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (p : SoninPositiveBumpParameters) (omega : I → ℝ)
    (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure (soninPositiveBumpClockProbabilityMeasure p)
        omega : Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (soninPositiveBumpRajchmanClockLaw p) omega m

theorem countableSoninPositiveBumpClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (p : SoninPositiveBumpParameters)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure (soninPositiveBumpClockProbabilityMeasure p)
        (fun j => (omega j).1) : Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (soninPositiveBumpRajchmanClockLaw p) omega i

theorem primeLogSoninPositiveBumpClockSample_isInfiniteTorusRayRajchman
    (p : SoninPositiveBumpParameters) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure (soninPositiveBumpClockProbabilityMeasure p)
        (fun q : Nat.Primes => Real.log (q : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (soninPositiveBumpRajchmanClockLaw p) m

theorem soninPositiveBumpClockProbabilityMeasure_nullSingletonClass
    (p : SoninPositiveBumpParameters) :
    NullSingletonClass (soninPositiveBumpClockProbabilityMeasure p : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass (soninPositiveBumpDensityData p)

theorem finiteThetaPositiveSquareClockSample_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (m : PositiveThetaSquareIndex) (energy : d → ℝ)
    (k : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure (thetaPositiveSquareClockProbabilityMeasure m)
        energy : Measure (UnitAddTorus d)) k.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (thetaPositiveSquareRajchmanClockLaw m) energy k

theorem countableThetaPositiveSquareClockSample_isInfiniteTorusRayRajchman
    {I : Type*} [Countable I] (m : PositiveThetaSquareIndex) (omega : I → ℝ)
    (k : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure (thetaPositiveSquareClockProbabilityMeasure m)
        omega : Measure (I → UnitAddCircle)) k.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (thetaPositiveSquareRajchmanClockLaw m) omega k

theorem countableThetaPositiveSquareClockSample_isInfiniteTorusCoordinateRajchman
    {I : Type*} [Countable I] (m : PositiveThetaSquareIndex)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure (thetaPositiveSquareClockProbabilityMeasure m)
        (fun j => (omega j).1) : Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (thetaPositiveSquareRajchmanClockLaw m) omega i

theorem primeLogThetaPositiveSquareClockSample_isInfiniteTorusRayRajchman
    (m : PositiveThetaSquareIndex) (k : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure (thetaPositiveSquareClockProbabilityMeasure m)
        (fun q : Nat.Primes => Real.log (q : ℝ)) :
          Measure (Nat.Primes → UnitAddCircle)) k.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (thetaPositiveSquareRajchmanClockLaw m) k

theorem thetaPositiveSquareClockProbabilityMeasure_nullSingletonClass
    (m : PositiveThetaSquareIndex) :
    NullSingletonClass (thetaPositiveSquareClockProbabilityMeasure m : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass (thetaPositiveSquareDensityData m)

theorem finiteAnnulusAmplitudeSpectralClockSample_isFiniteTorusRayRajchman
    {b c : ℝ} {d : Type*} [Fintype d] (A : RHTower.AnnulusAmplitude b c)
    (energy : d → ℝ) (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteClockSampledPhaseProbabilityMeasure
        (annulusAmplitudeSpectralClockProbabilityMeasure A) energy :
          Measure (UnitAddTorus d)) m.1 :=
  finiteRajchmanClockSample_isFiniteTorusRayRajchman
    (annulusAmplitudeSpectralRajchmanClockLaw A) energy m

theorem countableAnnulusAmplitudeSpectralClockSample_isInfiniteTorusRayRajchman
    {b c : ℝ} {I : Type*} [Countable I] (A : RHTower.AnnulusAmplitude b c)
    (omega : I → ℝ) (m : NonresonantInfiniteTorusCharacter omega) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (annulusAmplitudeSpectralClockProbabilityMeasure A) omega :
          Measure (I → UnitAddCircle)) m.1 :=
  countableRajchmanClockSample_isInfiniteTorusRayRajchman
    (annulusAmplitudeSpectralRajchmanClockLaw A) omega m

theorem countableAnnulusAmplitudeSpectralClockSample_isInfiniteTorusCoordinateRajchman
    {b c : ℝ} {I : Type*} [Countable I] (A : RHTower.AnnulusAmplitude b c)
    (omega : CoordinatewiseNonzeroCountableSpectrum I) (i : I) :
    IsInfiniteTorusCoordinateRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (annulusAmplitudeSpectralClockProbabilityMeasure A) (fun j => (omega j).1) :
          Measure (I → UnitAddCircle)) i :=
  countableRajchmanClockSample_isInfiniteTorusCoordinateRajchman
    (annulusAmplitudeSpectralRajchmanClockLaw A) omega i

theorem primeLogAnnulusAmplitudeSpectralClockSample_isInfiniteTorusRayRajchman
    {b c : ℝ} (A : RHTower.AnnulusAmplitude b c)
    (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (annulusAmplitudeSpectralClockProbabilityMeasure A)
        (fun q : Nat.Primes => Real.log (q : ℝ)) : Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  primeLogRajchmanClockSample_isInfiniteTorusRayRajchman
    (annulusAmplitudeSpectralRajchmanClockLaw A) m

theorem annulusAmplitudeSpectralClockProbabilityMeasure_nullSingletonClass
    {b c : ℝ} (A : RHTower.AnnulusAmplitude b c) :
    NullSingletonClass (annulusAmplitudeSpectralClockProbabilityMeasure A : Measure ℝ) :=
  realProbabilityDensityClock_nullSingletonClass (annulusAmplitudeSpectralDensityData A)

end

end GaloisForLFunctions.HTGeometry
