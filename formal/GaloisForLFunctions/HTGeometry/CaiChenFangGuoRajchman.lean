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
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Probability.Independence.Integration

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
open scoped BigOperators ComplexConjugate

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
      congr 3
      dsimp only [δ]
      push_cast
      ring
    · have hshift := hpos.comp (tendsto_add_atTop_nat 1)
      apply hshift.congr'
      filter_upwards [] with n
      rw [charFun_triangularClockProbabilityMeasure]
      congr 3
      rw [← Real.sinc_neg]
      congr 2
      dsimp only [δ]
      push_cast
      ring⟩

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

end

end GaloisForLFunctions.HTGeometry
