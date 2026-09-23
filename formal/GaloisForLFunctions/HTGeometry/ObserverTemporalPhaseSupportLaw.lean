import GaloisForLFunctions.HTGeometry.ArbitrarySpectrumTemporalWallCrossingLaw
import GaloisForLFunctions.HTGeometry.FiniteAnalyticPhaseEnsembleWallCrossingLaw
import GaloisForLFunctions.HTGeometry.ObserverRestrictedTemporalConstraintLaw
import GaloisForLFunctions.HTGeometry.SpectralCharacterDimensionBridgeLaw

/-!
# Observer-temporal phase-support law

For a finite analytic real spectrum, the spectral relations unresolved
through an observation horizon are exactly the projective torus characters
that remain identically one under the limiting phase probability law.

This identifies the algebraic temporal-dimension filtration with an
operational filtration of the probability laws actually sampled in time.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A finite projective character written as a full integer coordinate
function, as required by finite-torus Fourier monomials. -/
def finiteCharacterOfProjective
    {d : Type*} [Fintype d]
    (k : ProjectiveCharacter d) : d → ℤ :=
  fun i => k.1 i

/-- Detuning of a finite projective character. -/
def finiteProjectiveCharacterDetuning
    {d : Type*} [Fintype d]
    (k : ProjectiveCharacter d) (omega : d → ℝ) : ℝ :=
  k.1.sum fun i m => (m : ℝ) * omega i

theorem finiteTorusCharacterDetuning_finiteCharacterOfProjective
    {d : Type*} [Fintype d]
    (k : ProjectiveCharacter d) (omega : d → ℝ) :
    finiteTorusCharacterDetuning
        (finiteCharacterOfProjective k) omega =
      finiteProjectiveCharacterDetuning k omega := by
  classical
  rw [finiteProjectiveCharacterDetuning, Finsupp.sum_fintype]
  rfl
  intro i
  simp

/-- Fourier coefficient of one projective character in the actual
uniform-time phase ensemble. -/
def finiteProjectivePhaseCoefficient
    {d : Type*} [Fintype d]
    (k : ProjectiveCharacter d)
    (omega : d → ℝ) (A : ℝ) : ℂ :=
  ∫ x, UnitAddTorus.mFourier
      (finiteCharacterOfProjective k) x
    ∂(finiteTorusPhaseProbabilityMeasure omega A :
      Measure (UnitAddTorus d))

theorem finiteProjectivePhaseCoefficient_eq_sinc
    {d : Type*} [Fintype d]
    (k : ProjectiveCharacter d)
    (omega : d → ℝ) (A : ℝ) :
    finiteProjectivePhaseCoefficient k omega A =
      Real.sinc
        (A * finiteProjectiveCharacterDetuning k omega) := by
  rw [finiteProjectivePhaseCoefficient,
    finiteTorusPhaseProbabilityMeasure_mFourier_integral,
    finiteTorusCharacterDetuning_finiteCharacterOfProjective]

/-- Sinc is strictly different from one at every nonzero argument. -/
theorem real_sinc_ne_one_of_ne_zero
    {x : ℝ} (hx : x ≠ 0) :
    Real.sinc x ≠ 1 := by
  have hstrict : |Real.sinc x| < 1 := by
    rw [Real.sinc_of_ne_zero hx, abs_div]
    exact (div_lt_one (abs_pos.mpr hx)).2
      (Real.abs_sin_lt_abs hx)
  intro h
  rw [h, abs_one] at hstrict
  exact lt_irrefl 1 hstrict

/-- Sinc is even after multiplication by a nonnegative scale. -/
theorem real_sinc_mul_abs
    (a x : ℝ) (ha : 0 ≤ a) :
    Real.sinc (a * |x|) = Real.sinc (a * x) := by
  have h : Real.sinc |a * x| = Real.sinc (a * x) := by
    by_cases hx : 0 ≤ a * x
    · rw [abs_of_nonneg hx]
    · rw [abs_of_neg (lt_of_not_ge hx)]
      exact Real.sinc_neg (a * x)
  rw [abs_mul, abs_of_nonneg ha] at h
  exact h

/-- Sinc evenness after the positive inverse-power observation rescaling. -/
theorem coe_real_sinc_scaled_abs
    (τ x g : ℝ) (r : ℕ) (hτ : 0 ≤ τ) (hg : 0 < g) :
    (Real.sinc ((τ / g ^ r) * x) : ℂ) =
      (Real.sinc (τ * (|x| / g ^ r)) : ℂ) := by
  apply congrArg (fun y : ℝ => (y : ℂ))
  rw [show
    τ * (|x| / g ^ r) = (τ / g ^ r) * |x| by
      field_simp]
  exact
    (real_sinc_mul_abs
      (τ / g ^ r) x
      (div_nonneg hτ (pow_nonneg hg.le r))).symm

/-- Along the physical real coupling germ, the analytic projective
character response is the corresponding real spectral detuning. -/
theorem projectiveCharacterResponse_eventually_eq_detuning
    {d : Type*} [Fintype d]
    (energy : d → ℂ → ℂ)
    (omega : ℝ → d → ℝ)
    (hreal : ∀ i, ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      energy i (g : ℂ) = (omega g i : ℂ))
    (k : ProjectiveCharacter d) :
    ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      projectiveCharacterResponse energy k (g : ℂ) =
        (finiteProjectiveCharacterDetuning k (omega g) : ℂ) := by
  classical
  have hallReal :
      ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ), ∀ i,
        energy i (g : ℂ) = (omega g i : ℂ) := by
    rw [Filter.eventually_all]
    exact hreal
  filter_upwards [hallReal] with g hg
  unfold projectiveCharacterResponse
    finiteProjectiveCharacterDetuning
  rw [Finsupp.sum]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  rw [hg]

/-- Every active finite projective character has a positive exact birth
profile whose order is its spectral-character valuation. -/
theorem hasPositiveBirthProfile_finiteProjectiveCharacter
    {d : Type*} [Fintype d]
    (energy : d → ℂ → ℂ)
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (omega : ℝ → d → ℝ)
    (hreal : ∀ i, ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      energy i (g : ℂ) = (omega g i : ℂ))
    (k : ProjectiveCharacter d)
    (hactive :
      SpectralCharacterActive (spectralTaylorJet series) k) :
    ∃ c : ℝ,
      HasPositiveBirthProfile
        (fun g =>
          |finiteProjectiveCharacterDetuning k (omega g)|)
        (spectralCharacterBirthOrder
          (spectralTaylorJet series) k hactive) c := by
  let response := projectiveCharacterResponse energy k
  let responseSeries := projectiveCharacterSeries series k
  have hresponse :
      HasFPowerSeriesAt response responseSeries 0 :=
    hasFPowerSeriesAt_projectiveCharacterResponse
      energy series henergy k
  have hseries : responseSeries ≠ 0 := by
    exact
      (spectralCharacterActive_iff_characterSeries_ne_zero
        series k).mp hactive
  have hsector : AnalyticSectorActive response := by
    intro hzero
    exact hseries (hresponse.eq_zero_of_eventually hzero)
  have hprofile :=
    hasPositiveBirthProfile_norm_of_active hresponse hsector
  change
    HasPositiveBirthProfile
      (fun g : ℝ => ‖response (g : ℂ)‖)
      responseSeries.order
      ‖analyticBirthUnit response responseSeries 0‖ at hprofile
  have hbirth :
      spectralCharacterBirthOrder
          (spectralTaylorJet series) k hactive =
        responseSeries.order := by
    exact spectralCharacterBirthOrder_eq_series_order
      series k hactive
  refine
    ⟨‖analyticBirthUnit response responseSeries 0‖, ?_⟩
  rw [hbirth]
  refine ⟨?_, hprofile.2⟩
  apply hprofile.1.congr'
  have hrealResponse :=
    projectiveCharacterResponse_eventually_eq_detuning
      energy omega hreal k
  filter_upwards [hrealResponse] with g hg
  dsimp only [response] at hg ⊢
  rw [hg]
  simp [Complex.norm_real, Real.norm_eq_abs]

/-- **Projective-character phase wall crossing.** Every active projective
character of a finite analytic real spectrum is unresolved below its exact
birth order, has one nontrivial sinc coefficient at birth, and is dephased
above birth. -/
theorem finiteProjectivePhaseCoefficient_wallCrossing
    {d : Type*} [Fintype d]
    (energy : d → ℂ → ℂ)
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (omega : ℝ → d → ℝ)
    (hreal : ∀ i, ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      energy i (g : ℂ) = (omega g i : ℂ))
    (k : ProjectiveCharacter d)
    (hactive :
      SpectralCharacterActive (spectralTaylorJet series) k)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ c : ℝ, 0 < c ∧
      let b := spectralCharacterBirthOrder
        (spectralTaylorJet series) k hactive
      (∀ r < b,
        Tendsto
          (fun g =>
            finiteProjectivePhaseCoefficient k (omega g)
              (τ / g ^ r))
          (𝓝[>] 0) (𝓝 1)) ∧
      Tendsto
        (fun g =>
          finiteProjectivePhaseCoefficient k (omega g)
            (τ / g ^ b))
        (𝓝[>] 0) (𝓝 (Real.sinc (τ * c))) ∧
      (∀ r, b < r →
        Tendsto
          (fun g =>
            finiteProjectivePhaseCoefficient k (omega g)
              (τ / g ^ r))
          (𝓝[>] 0) (𝓝 0)) := by
  obtain ⟨c, hprofile⟩ :=
    hasPositiveBirthProfile_finiteProjectiveCharacter
      energy series henergy omega hreal k hactive
  refine ⟨c, hprofile.2, ?_⟩
  have hwall :=
    spectralCharacterReporter_wallCrossing hprofile hτ
  dsimp only
  constructor
  · intro r hr
    have ht := hwall.1 r hr
    apply
      (Complex.continuous_ofReal.continuousAt.tendsto.comp ht).congr'
    filter_upwards [self_mem_nhdsWithin] with g hg
    change 0 < g at hg
    rw [finiteProjectivePhaseCoefficient_eq_sinc]
    exact (coe_real_sinc_scaled_abs τ
      (finiteProjectiveCharacterDetuning k (omega g))
      g r hτ.le hg).symm
  constructor
  · have ht := hwall.2.1
    apply
      (Complex.continuous_ofReal.continuousAt.tendsto.comp ht).congr'
    filter_upwards [self_mem_nhdsWithin] with g hg
    change 0 < g at hg
    rw [finiteProjectivePhaseCoefficient_eq_sinc]
    exact (coe_real_sinc_scaled_abs τ
      (finiteProjectiveCharacterDetuning k (omega g))
      g
      (spectralCharacterBirthOrder
        (spectralTaylorJet series) k hactive)
      hτ.le hg).symm
  · intro r hr
    have ht := hwall.2.2 r hr
    apply
      (Complex.continuous_ofReal.continuousAt.tendsto.comp ht).congr'
    filter_upwards [self_mem_nhdsWithin] with g hg
    change 0 < g at hg
    rw [finiteProjectivePhaseCoefficient_eq_sinc]
    exact (coe_real_sinc_scaled_abs τ
      (finiteProjectiveCharacterDetuning k (omega g))
      g r hτ.le hg).symm

/-- Projective characters that are equal to one almost surely under a phase
law. These are exactly the phase relations invisible to the law. -/
def phaseLawConstraint
    {d : Type*} [Fintype d]
    (μ : ProbabilityMeasure (UnitAddTorus d))
    (k : ProjectiveCharacter d) : Prop :=
  UnitAddTorus.mFourier (finiteCharacterOfProjective k) =ᵐ[
      (μ : Measure (UnitAddTorus d))]
    fun _ => 1

/-- Every finite-torus Fourier monomial has pointwise norm one. -/
theorem norm_mFourier_apply
    {d : Type*} [Fintype d]
    (n : d → ℤ) (x : UnitAddTorus d) :
    ‖UnitAddTorus.mFourier n x‖ = 1 := by
  simp [UnitAddTorus.mFourier]

/-- A projective character is one almost surely exactly when its Fourier
coefficient is one. -/
theorem phaseLawConstraint_iff_integral_eq_one
    {d : Type*} [Fintype d]
    (μ : ProbabilityMeasure (UnitAddTorus d))
    (k : ProjectiveCharacter d) :
    phaseLawConstraint μ k ↔
      (∫ x, UnitAddTorus.mFourier
          (finiteCharacterOfProjective k) x
        ∂(μ : Measure (UnitAddTorus d))) = 1 := by
  let character :=
    UnitAddTorus.mFourier (finiteCharacterOfProjective k)
  constructor
  · intro h
    change
      (fun x => character x) =ᵐ[
        (μ : Measure (UnitAddTorus d))] (fun _ => 1) at h
    calc
      (∫ x, character x
          ∂(μ : Measure (UnitAddTorus d))) =
          ∫ _x, (1 : ℂ)
            ∂(μ : Measure (UnitAddTorus d)) :=
        integral_congr_ae h
      _ = 1 := by simp
  · intro h
    have hcharacter :
        Integrable (fun x => character x)
          (μ : Measure (UnitAddTorus d)) :=
      character.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    let defect : UnitAddTorus d → ℝ :=
      fun x => ‖character x - 1‖ ^ (2 : ℕ)
    have hdefectContinuous : Continuous defect := by
      dsimp [defect]
      fun_prop
    have hdefectIntegrable :
        Integrable defect
          (μ : Measure (UnitAddTorus d)) :=
      hdefectContinuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hpoint (x : UnitAddTorus d) :
        defect x = 2 - 2 * (character x).re := by
      have hnorm : ‖character x‖ = 1 := by
        exact norm_mFourier_apply _ _
      have hsq :
          (character x).re ^ (2 : ℕ) + (character x).im ^ (2 : ℕ) = 1 := by
        calc
          (character x).re ^ (2 : ℕ) + (character x).im ^ (2 : ℕ) =
              Complex.normSq (character x) := by
            simp [Complex.normSq_apply, pow_two]
          _ = ‖character x‖ ^ (2 : ℕ) := Complex.normSq_eq_norm_sq _
          _ = 1 := by rw [hnorm]; norm_num
      dsimp [defect]
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.one_re, Complex.sub_im,
        Complex.one_im, sub_zero]
      nlinarith
    have hdefectIntegral :
        ∫ x, defect x
            ∂(μ : Measure (UnitAddTorus d)) = 0 := by
      calc
        (∫ x, defect x
            ∂(μ : Measure (UnitAddTorus d))) =
            ∫ x, (2 - 2 * (character x).re)
              ∂(μ : Measure (UnitAddTorus d)) :=
          integral_congr_ae
            (Filter.Eventually.of_forall hpoint)
        _ =
            (∫ _x, (2 : ℝ)
                ∂(μ : Measure (UnitAddTorus d))) -
              2 * (∫ x, (character x).re
                ∂(μ : Measure (UnitAddTorus d))) := by
          rw [integral_sub, integral_const_mul]
          · exact integrable_const 2
          · exact hcharacter.re.const_mul 2
        _ = 2 - 2 *
            (∫ x, (character x).re
              ∂(μ : Measure (UnitAddTorus d))) := by
          simp
        _ = 2 - 2 *
            (∫ x, character x
              ∂(μ : Measure (UnitAddTorus d))).re := by
          rw [← RCLike.re_eq_complex_re, integral_re hcharacter]
        _ = 0 := by rw [h]; norm_num
    have hzero :
        defect =ᵐ[(μ : Measure (UnitAddTorus d))] 0 :=
      (integral_eq_zero_iff_of_nonneg
        (fun x => sq_nonneg ‖character x - 1‖)
        hdefectIntegrable).mp hdefectIntegral
    filter_upwards [hzero] with x hx
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    exact sq_eq_zero_iff.mp hx

/-- Fourier coefficient of one projective character under a phase
probability law. -/
def projectivePhaseLawFourierCoefficient
    {d : Type*} [Fintype d]
    (μ : ProbabilityMeasure (UnitAddTorus d))
    (k : ProjectiveCharacter d) : ℂ :=
  ∫ x, UnitAddTorus.mFourier
      (finiteCharacterOfProjective k) x
    ∂(μ : Measure (UnitAddTorus d))

/-- **Complete spectral-resolution Fourier law.** For every projective
character of every finite analytic real spectrum, its coefficient in the
limiting phase law is exactly:

* `1` before its analytic birth;
* the sinc of its nonzero initial coefficient at birth;
* `0` after birth;
* and always `1` when the character is an exact analytic relation.

This theorem retains the critical crossover information discarded by the
unit-character constraint space and its rank. -/
theorem finiteAnalyticTemporalPhase_fourierTrichotomy
    {d : Type*} [Fintype d]
    (energy : d → ℂ → ℂ)
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (omega : ℝ → d → ℝ)
    (hreal : ∀ i, ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      energy i (g : ℂ) = (omega g i : ℂ))
    (r : ℕ) {τ : ℝ} (hτ : 0 < τ)
    (μ : ProbabilityMeasure (UnitAddTorus d))
    (hμ :
      Tendsto
        (fun g =>
          finiteTorusPhaseProbabilityMeasure
            (omega g) (τ / g ^ r))
        (𝓝[>] 0) (𝓝 μ))
    (k : ProjectiveCharacter d) :
    (¬SpectralCharacterActive (spectralTaylorJet series) k →
      projectivePhaseLawFourierCoefficient μ k = 1) ∧
    (∀ hactive :
        SpectralCharacterActive (spectralTaylorJet series) k,
      ∃ c : ℝ, c ≠ 0 ∧
        (r < spectralCharacterBirthOrder
            (spectralTaylorJet series) k hactive →
          projectivePhaseLawFourierCoefficient μ k = 1) ∧
        (r = spectralCharacterBirthOrder
            (spectralTaylorJet series) k hactive →
          projectivePhaseLawFourierCoefficient μ k =
            Real.sinc (τ * c)) ∧
        (spectralCharacterBirthOrder
            (spectralTaylorJet series) k hactive < r →
          projectivePhaseLawFourierCoefficient μ k = 0)) := by
  let coefficient :
      ProbabilityMeasure (UnitAddTorus d) → ℂ :=
    fun ρ => projectivePhaseLawFourierCoefficient ρ k
  have hcoefficient :
      Tendsto
        (fun g =>
          coefficient
            (finiteTorusPhaseProbabilityMeasure
              (omega g) (τ / g ^ r)))
        (𝓝[>] 0) (𝓝 (coefficient μ)) :=
    (continuous_integral_complex_continuousMap
      (UnitAddTorus.mFourier
        (finiteCharacterOfProjective k))).continuousAt.tendsto.comp hμ
  constructor
  · intro hinactive
    have hseries :
        projectiveCharacterSeries series k = 0 := by
      simpa [spectralCharacterActive_iff_characterSeries_ne_zero]
        using hinactive
    have hresponse :=
      hasFPowerSeriesAt_projectiveCharacterResponse
        energy series henergy k
    have hzero :
        projectiveCharacterResponse energy k =ᶠ[𝓝 0]
          (fun _ : ℂ => 0) :=
      HasFPowerSeriesAt.eventually_eq_zero
        (by simpa [hseries] using hresponse)
    have ht :
        Tendsto (fun g : ℝ => (g : ℂ))
          (𝓝[>] 0) (𝓝 0) :=
      Complex.continuous_ofReal.continuousAt.tendsto.mono_left
        inf_le_left
    have hzeroReal := hzero.comp_tendsto ht
    have hresponseReal :=
      projectiveCharacterResponse_eventually_eq_detuning
        energy omega hreal k
    have hcoefficientOne :
        Tendsto
          (fun g =>
            coefficient
              (finiteTorusPhaseProbabilityMeasure
                (omega g) (τ / g ^ r)))
          (𝓝[>] 0) (𝓝 1) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hzeroReal, hresponseReal] with g hz hgr
      have hdetuning :
          finiteProjectiveCharacterDetuning k (omega g) = 0 := by
        apply Complex.ofReal_eq_zero.mp
        rw [← hgr]
        exact hz
      symm
      change finiteProjectivePhaseCoefficient k
        (omega g) (τ / g ^ r) = 1
      rw [finiteProjectivePhaseCoefficient_eq_sinc, hdetuning]
      simp
    exact tendsto_nhds_unique hcoefficient hcoefficientOne
  · intro hactive
    obtain ⟨c, hc, hwall⟩ :=
      finiteProjectivePhaseCoefficient_wallCrossing
        energy series henergy omega hreal k hactive hτ
    refine ⟨c, hc.ne', ?_, ?_, ?_⟩
    · intro hrb
      have hunresolved :
          Tendsto
            (fun g =>
              coefficient
                (finiteTorusPhaseProbabilityMeasure
                  (omega g) (τ / g ^ r)))
            (𝓝[>] 0) (𝓝 1) := by
        simpa [coefficient, projectivePhaseLawFourierCoefficient,
          finiteProjectivePhaseCoefficient] using
            hwall.1 r hrb
      exact tendsto_nhds_unique hcoefficient hunresolved
    · intro hrb
      subst r
      have hcritical :
          Tendsto
            (fun g =>
              coefficient
                (finiteTorusPhaseProbabilityMeasure
                  (omega g) (τ /
                    g ^ spectralCharacterBirthOrder
                      (spectralTaylorJet series) k hactive)))
            (𝓝[>] 0) (𝓝 (Real.sinc (τ * c))) := by
        simpa [coefficient, projectivePhaseLawFourierCoefficient,
          finiteProjectivePhaseCoefficient] using hwall.2.1
      exact tendsto_nhds_unique hcoefficient hcritical
    · intro hbr
      have hdephased :
          Tendsto
            (fun g =>
              coefficient
                (finiteTorusPhaseProbabilityMeasure
                  (omega g) (τ / g ^ r)))
            (𝓝[>] 0) (𝓝 0) := by
        simpa [coefficient, projectivePhaseLawFourierCoefficient,
          finiteProjectivePhaseCoefficient] using
            hwall.2.2 r hbr
      exact tendsto_nhds_unique hcoefficient hdephased

/-- Complete character transform prescribed by the analytic birth
filtration at one inverse-power observation horizon. -/
def SpectralResolutionFourierLaw
    {d : Type*} [Fintype d]
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (r : ℕ) (τ : ℝ)
    (μ : ProbabilityMeasure (UnitAddTorus d)) : Prop :=
  ∀ k : ProjectiveCharacter d,
    (¬SpectralCharacterActive (spectralTaylorJet series) k →
      projectivePhaseLawFourierCoefficient μ k = 1) ∧
    (∀ hactive :
        SpectralCharacterActive (spectralTaylorJet series) k,
      ∃ c : ℝ, c ≠ 0 ∧
        (r < spectralCharacterBirthOrder
            (spectralTaylorJet series) k hactive →
          projectivePhaseLawFourierCoefficient μ k = 1) ∧
        (r = spectralCharacterBirthOrder
            (spectralTaylorJet series) k hactive →
          projectivePhaseLawFourierCoefficient μ k =
            Real.sinc (τ * c)) ∧
        (spectralCharacterBirthOrder
            (spectralTaylorJet series) k hactive < r →
          projectivePhaseLawFourierCoefficient μ k = 0))

/-- Every limiting phase law of a finite analytic real spectrum satisfies
the complete spectral-resolution Fourier law. -/
theorem finiteAnalyticTemporalPhase_completeFourierLaw
    {d : Type*} [Fintype d]
    (energy : d → ℂ → ℂ)
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (omega : ℝ → d → ℝ)
    (hreal : ∀ i, ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      energy i (g : ℂ) = (omega g i : ℂ))
    (r : ℕ) {τ : ℝ} (hτ : 0 < τ)
    (μ : ProbabilityMeasure (UnitAddTorus d))
    (hμ :
      Tendsto
        (fun g =>
          finiteTorusPhaseProbabilityMeasure
            (omega g) (τ / g ^ r))
        (𝓝[>] 0) (𝓝 μ)) :
    SpectralResolutionFourierLaw series r τ μ := by
  intro k
  exact finiteAnalyticTemporalPhase_fourierTrichotomy
    energy series henergy omega hreal r hτ μ hμ k

/-- Every continuous phase statistic—including every finite spectral
form-factor polynomial—converges to its expectation under the same limiting
spectral-resolution law. -/
theorem finiteAnalyticTemporalPhase_continuousStatistic
    {d : Type*} [Fintype d]
    (omega : ℝ → d → ℝ)
    (r : ℕ) {τ : ℝ}
    (μ : ProbabilityMeasure (UnitAddTorus d))
    (hμ :
      Tendsto
        (fun g =>
          finiteTorusPhaseProbabilityMeasure
            (omega g) (τ / g ^ r))
        (𝓝[>] 0) (𝓝 μ))
    (statistic : C(UnitAddTorus d, ℂ)) :
    Tendsto
      (fun g =>
        ∫ x, statistic x
          ∂(finiteTorusPhaseProbabilityMeasure
            (omega g) (τ / g ^ r) :
              Measure (UnitAddTorus d)))
      (𝓝[>] 0)
      (𝓝
        (∫ x, statistic x
          ∂(μ : Measure (UnitAddTorus d)))) :=
  (continuous_integral_complex_continuousMap
    statistic).continuousAt.tendsto.comp hμ

/-- Rational span of all projective characters that remain almost surely
invisible under one phase probability law. -/
def phaseLawConstraintRationalSpace
    {d : Type*} [Fintype d]
    (μ : ProbabilityMeasure (UnitAddTorus d)) :
    Submodule ℚ (ProjectiveRationalCharacter d) :=
  Submodule.span ℚ
    (projectiveCharacterToRational ''
      {k : ProjectiveCharacter d | phaseLawConstraint μ k})

/-- Operational dimension of a phase law: total projective character rank
minus the rational rank of its almost-sure phase constraints. -/
noncomputable def phaseLawTemporalDimension
    {d : Type*} [Fintype d]
    (μ : ProbabilityMeasure (UnitAddTorus d)) : ℕ :=
  Module.finrank ℚ (ProjectiveRationalCharacter d) -
    Module.finrank ℚ (phaseLawConstraintRationalSpace μ)

/-- Pullback of a phase law's almost-sure rational constraints to one
observer-accessible character carrier. -/
def observerPhaseLawConstraintSpace
    {d O : Type*} [Fintype d]
    [AddCommGroup O] [Module ℚ O]
    (μ : ProbabilityMeasure (UnitAddTorus d))
    (observe : O →ₗ[ℚ] ProjectiveRationalCharacter d) :
    Submodule ℚ O :=
  (phaseLawConstraintRationalSpace μ).comap observe

/-- Operational temporal dimension accessible to one observer under one
phase probability law. -/
noncomputable def observerPhaseLawTemporalDimension
    {d O : Type*} [Fintype d]
    [AddCommGroup O] [Module ℚ O] [FiniteDimensional ℚ O]
    (μ : ProbabilityMeasure (UnitAddTorus d))
    (observe : O →ₗ[ℚ] ProjectiveRationalCharacter d) : ℕ :=
  Module.finrank ℚ O -
    Module.finrank ℚ
      (observerPhaseLawConstraintSpace μ observe)

/-- **Observer-temporal phase-support identity.** At observation order
`r`, a projective character is almost surely invisible in the unique
limiting phase law exactly when all of its spectral jets through order `r`
vanish. -/
theorem existsUnique_finiteAnalyticTemporalPhaseSupport
    {d : Type*} [Fintype d]
    (energy : d → ℂ → ℂ)
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (omega : ℝ → d → ℝ)
    (hreal : ∀ i, ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      energy i (g : ℂ) = (omega g i : ℂ))
    (r : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    ∃! μ : ProbabilityMeasure (UnitAddTorus d),
      Tendsto
        (fun g =>
          finiteTorusPhaseProbabilityMeasure
            (omega g) (τ / g ^ r))
        (𝓝[>] 0) (𝓝 μ) ∧
      ∀ k : ProjectiveCharacter d,
        phaseLawConstraint μ k ↔
          k ∈ spectralConstraintFiltration
            (spectralTaylorJet series) (r + 1) := by
  obtain ⟨μ, hμ, hμunique⟩ :=
    existsUnique_finiteAnalyticPhaseEnsemble_limit
      energy series henergy omega hreal r hτ
  refine ⟨μ, ⟨hμ, ?_⟩, ?_⟩
  · intro k
    rw [phaseLawConstraint_iff_integral_eq_one]
    let coefficient :
        ProbabilityMeasure (UnitAddTorus d) → ℂ :=
      fun ρ =>
        ∫ x, UnitAddTorus.mFourier
            (finiteCharacterOfProjective k) x
          ∂(ρ : Measure (UnitAddTorus d))
    have hcoefficient :
        Tendsto
          (fun g =>
            coefficient
              (finiteTorusPhaseProbabilityMeasure
                (omega g) (τ / g ^ r)))
          (𝓝[>] 0) (𝓝 (coefficient μ)) :=
      (continuous_integral_complex_continuousMap
        (UnitAddTorus.mFourier
          (finiteCharacterOfProjective k))).continuousAt.tendsto.comp hμ
    by_cases hactive :
        SpectralCharacterActive (spectralTaylorJet series) k
    · obtain ⟨c, hc, hwall⟩ :=
        finiteProjectivePhaseCoefficient_wallCrossing
          energy series henergy omega hreal k hactive hτ
      let b :=
        spectralCharacterBirthOrder
          (spectralTaylorJet series) k hactive
      have hmem :
          k ∈ spectralConstraintFiltration
              (spectralTaylorJet series) (r + 1) ↔
            r < b := by
        rw [mem_spectralConstraintFiltration_iff_le_birthOrder
          hactive]
        omega
      rw [hmem]
      constructor
      · intro hcoeff
        change coefficient μ = 1 at hcoeff
        by_contra hnot
        have hbr : b ≤ r := not_lt.mp hnot
        rcases hbr.eq_or_lt with hbeq | hblt
        · subst r
          have hcritical :
              Tendsto
                (fun g =>
                  coefficient
                    (finiteTorusPhaseProbabilityMeasure
                      (omega g) (τ / g ^ b)))
                (𝓝[>] 0) (𝓝 (Real.sinc (τ * c))) := by
            simpa [coefficient,
              finiteProjectivePhaseCoefficient] using hwall.2.1
          have heq :
              coefficient μ = Real.sinc (τ * c) :=
            tendsto_nhds_unique hcoefficient hcritical
          have hne : Real.sinc (τ * c) ≠ 1 :=
            real_sinc_ne_one_of_ne_zero
              (mul_ne_zero hτ.ne' hc.ne')
          have hsincComplex :
              (Real.sinc (τ * c) : ℂ) = 1 :=
            heq.symm.trans hcoeff
          have hsincReal : Real.sinc (τ * c) = 1 :=
            Complex.ofReal_injective (by simpa using hsincComplex)
          exact hne hsincReal
        · have hdephase :
              Tendsto
                (fun g =>
                  coefficient
                    (finiteTorusPhaseProbabilityMeasure
                      (omega g) (τ / g ^ r)))
                (𝓝[>] 0) (𝓝 0) := by
            simpa [coefficient,
              finiteProjectivePhaseCoefficient] using
                hwall.2.2 r hblt
          have heq : coefficient μ = 0 :=
            tendsto_nhds_unique hcoefficient hdephase
          rw [heq] at hcoeff
          norm_num at hcoeff
      · intro hrb
        have hunresolved :
            Tendsto
              (fun g =>
                coefficient
                  (finiteTorusPhaseProbabilityMeasure
                    (omega g) (τ / g ^ r)))
              (𝓝[>] 0) (𝓝 1) := by
          simpa [coefficient,
            finiteProjectivePhaseCoefficient] using
              hwall.1 r hrb
        exact tendsto_nhds_unique hcoefficient hunresolved
    · have hseries :
          projectiveCharacterSeries series k = 0 := by
        simpa [spectralCharacterActive_iff_characterSeries_ne_zero]
          using hactive
      have hresponse :=
        hasFPowerSeriesAt_projectiveCharacterResponse
          energy series henergy k
      have hzero :
          projectiveCharacterResponse energy k =ᶠ[𝓝 0]
            (fun _ : ℂ => 0) :=
        HasFPowerSeriesAt.eventually_eq_zero
          (by simpa [hseries] using hresponse)
      have ht :
          Tendsto (fun g : ℝ => (g : ℂ))
            (𝓝[>] 0) (𝓝 0) :=
        Complex.continuous_ofReal.continuousAt.tendsto.mono_left
          inf_le_left
      have hzeroReal := hzero.comp_tendsto ht
      have hresponseReal :=
        projectiveCharacterResponse_eventually_eq_detuning
          energy omega hreal k
      have hcoefficientOne :
          Tendsto
            (fun g =>
              coefficient
                (finiteTorusPhaseProbabilityMeasure
                  (omega g) (τ / g ^ r)))
            (𝓝[>] 0) (𝓝 1) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [hzeroReal, hresponseReal] with g hz hgr
        have hdetuning :
            finiteProjectiveCharacterDetuning k (omega g) = 0 := by
          apply Complex.ofReal_eq_zero.mp
          rw [← hgr]
          exact hz
        symm
        change finiteProjectivePhaseCoefficient k
          (omega g) (τ / g ^ r) = 1
        rw [finiteProjectivePhaseCoefficient_eq_sinc, hdetuning]
        simp
      have hcoeffOne : coefficient μ = 1 :=
        tendsto_nhds_unique hcoefficient hcoefficientOne
      have hmem :
          k ∈ spectralConstraintFiltration
            (spectralTaylorJet series) (r + 1) :=
        (not_spectralCharacterActive_iff_forall_mem.mp hactive) _
      exact iff_of_true hcoeffOne hmem
  · intro ν hν
    exact hμunique ν hν.1

/-- The almost-sure constraints of the limiting phase law span exactly the
rational spectral relations unresolved at that horizon. -/
theorem finiteAnalyticTemporalPhase_constraintSpace_eq
    {d : Type*} [Fintype d]
    (energy : d → ℂ → ℂ)
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (omega : ℝ → d → ℝ)
    (hreal : ∀ i, ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      energy i (g : ℂ) = (omega g i : ℂ))
    (r : ℕ) {τ : ℝ} (hτ : 0 < τ)
    (μ : ProbabilityMeasure (UnitAddTorus d))
    (hμ :
      Tendsto
        (fun g =>
          finiteTorusPhaseProbabilityMeasure
            (omega g) (τ / g ^ r))
        (𝓝[>] 0) (𝓝 μ)) :
    phaseLawConstraintRationalSpace μ =
      rationalSpectralConstraintSpace
        (spectralTaylorJet series) (r + 1) := by
  obtain ⟨ν, hν, hνunique⟩ :=
    existsUnique_finiteAnalyticTemporalPhaseSupport
      energy series henergy omega hreal r hτ
  have hμν : μ = ν := by
    exact tendsto_nhds_unique hμ hν.1
  subst μ
  rw [phaseLawConstraintRationalSpace,
    rationalConstraint_eq_span_integerConstraints]
  apply congrArg (Submodule.span ℚ)
  ext q
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, (hν.2 k).mp hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, (hν.2 k).mpr hk, rfl⟩

/-- Pulling the limiting law's phase constraints back through an arbitrary
finite observer carrier gives exactly the observer-restricted spectral-jet
constraint space. -/
theorem finiteAnalyticObserverPhase_constraintSpace_eq
    {d O : Type*} [Fintype d]
    [AddCommGroup O] [Module ℚ O]
    (energy : d → ℂ → ℂ)
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (omega : ℝ → d → ℝ)
    (hreal : ∀ i, ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      energy i (g : ℂ) = (omega g i : ℂ))
    (observe : O →ₗ[ℚ] ProjectiveRationalCharacter d)
    (r : ℕ) {τ : ℝ} (hτ : 0 < τ)
    (μ : ProbabilityMeasure (UnitAddTorus d))
    (hμ :
      Tendsto
        (fun g =>
          finiteTorusPhaseProbabilityMeasure
            (omega g) (τ / g ^ r))
        (𝓝[>] 0) (𝓝 μ)) :
    observerPhaseLawConstraintSpace μ observe =
      observerSpectralConstraintSpace
        (spectralTaylorJet series) observe (r + 1) := by
  have hfull :=
    finiteAnalyticTemporalPhase_constraintSpace_eq
      energy series henergy omega hreal r hτ μ hμ
  ext q
  rw [observerPhaseLawConstraintSpace, hfull]
  rfl

/-- **Operational dimension identity.** The dimension inferred solely from
the limiting phase probability law equals the algebraic temporal dimension
resolved by spectral jets through the same horizon. -/
theorem finiteAnalyticTemporalPhase_dimension_eq
    {d : Type*} [Fintype d]
    (energy : d → ℂ → ℂ)
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (omega : ℝ → d → ℝ)
    (hreal : ∀ i, ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      energy i (g : ℂ) = (omega g i : ℂ))
    (r : ℕ) {τ : ℝ} (hτ : 0 < τ)
    (μ : ProbabilityMeasure (UnitAddTorus d))
    (hμ :
      Tendsto
        (fun g =>
          finiteTorusPhaseProbabilityMeasure
            (omega g) (τ / g ^ r))
        (𝓝[>] 0) (𝓝 μ)) :
    phaseLawTemporalDimension μ =
      temporalDimension (spectralTaylorJet series) (r + 1) := by
  have hspace :=
    finiteAnalyticTemporalPhase_constraintSpace_eq
      energy series henergy omega hreal r hτ μ hμ
  have hrank :=
    temporalDimension_add_constraintFinrank
      (spectralTaylorJet series) (r + 1)
  unfold phaseLawTemporalDimension
  rw [hspace]
  omega

/-- **Observer-operational dimension identity.** For every finite rational
observer carrier, dimension inferred from the limiting phase law equals the
rank of spectral-jet directions accessible to that same observer. -/
theorem finiteAnalyticObserverPhase_dimension_eq
    {d O : Type*} [Fintype d]
    [AddCommGroup O] [Module ℚ O] [FiniteDimensional ℚ O]
    (energy : d → ℂ → ℂ)
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (omega : ℝ → d → ℝ)
    (hreal : ∀ i, ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      energy i (g : ℂ) = (omega g i : ℂ))
    (observe : O →ₗ[ℚ] ProjectiveRationalCharacter d)
    (r : ℕ) {τ : ℝ} (hτ : 0 < τ)
    (μ : ProbabilityMeasure (UnitAddTorus d))
    (hμ :
      Tendsto
        (fun g =>
          finiteTorusPhaseProbabilityMeasure
            (omega g) (τ / g ^ r))
        (𝓝[>] 0) (𝓝 μ)) :
    observerPhaseLawTemporalDimension μ observe =
      observerTemporalDimension
        (spectralTaylorJet series) observe (r + 1) := by
  have hspace :=
    finiteAnalyticObserverPhase_constraintSpace_eq
      energy series henergy omega hreal observe r hτ μ hμ
  have hrank :=
    observerTemporalDimension_add_constraintFinrank
      (spectralTaylorJet series) observe (r + 1)
  unfold observerPhaseLawTemporalDimension
  rw [hspace]
  omega

/-- **Observer-temporal support conservation law.** At every
inverse-power horizon, one unique limiting phase law exists; its operational
temporal dimension plus its almost-sure constraint rank equals the complete
projective spectral rank. -/
theorem existsUnique_finiteAnalyticTemporalSupportConservation
    {d : Type*} [Fintype d]
    (energy : d → ℂ → ℂ)
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (omega : ℝ → d → ℝ)
    (hreal : ∀ i, ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      energy i (g : ℂ) = (omega g i : ℂ))
    (r : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    ∃! μ : ProbabilityMeasure (UnitAddTorus d),
      Tendsto
        (fun g =>
          finiteTorusPhaseProbabilityMeasure
            (omega g) (τ / g ^ r))
        (𝓝[>] 0) (𝓝 μ) ∧
      phaseLawTemporalDimension μ =
        temporalDimension (spectralTaylorJet series) (r + 1) ∧
      phaseLawTemporalDimension μ +
          Module.finrank ℚ (phaseLawConstraintRationalSpace μ) =
        Module.finrank ℚ (ProjectiveRationalCharacter d) := by
  obtain ⟨μ, hμ, hμunique⟩ :=
    existsUnique_finiteAnalyticPhaseEnsemble_limit
      energy series henergy omega hreal r hτ
  refine ⟨μ, ⟨hμ, ?_, ?_⟩, ?_⟩
  · exact finiteAnalyticTemporalPhase_dimension_eq
      energy series henergy omega hreal r hτ μ hμ
  · unfold phaseLawTemporalDimension
    have hle :
        Module.finrank ℚ (phaseLawConstraintRationalSpace μ) ≤
          Module.finrank ℚ (ProjectiveRationalCharacter d) :=
      Submodule.finrank_le _
    omega
  · intro ν hν
    exact hμunique ν hν.1

/-- **Observer-restricted temporal support conservation.** One limiting
phase law simultaneously induces the exact dimension/constraint
conservation identity for every chosen finite observer carrier. -/
theorem existsUnique_finiteAnalyticObserverSupportConservation
    {d O : Type*} [Fintype d]
    [AddCommGroup O] [Module ℚ O] [FiniteDimensional ℚ O]
    (energy : d → ℂ → ℂ)
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (omega : ℝ → d → ℝ)
    (hreal : ∀ i, ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      energy i (g : ℂ) = (omega g i : ℂ))
    (observe : O →ₗ[ℚ] ProjectiveRationalCharacter d)
    (r : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    ∃! μ : ProbabilityMeasure (UnitAddTorus d),
      Tendsto
        (fun g =>
          finiteTorusPhaseProbabilityMeasure
            (omega g) (τ / g ^ r))
        (𝓝[>] 0) (𝓝 μ) ∧
      observerPhaseLawTemporalDimension μ observe =
        observerTemporalDimension
          (spectralTaylorJet series) observe (r + 1) ∧
      observerPhaseLawTemporalDimension μ observe +
          Module.finrank ℚ
            (observerPhaseLawConstraintSpace μ observe) =
        Module.finrank ℚ O := by
  obtain ⟨μ, hμ, hμunique⟩ :=
    existsUnique_finiteAnalyticPhaseEnsemble_limit
      energy series henergy omega hreal r hτ
  refine ⟨μ, ⟨hμ, ?_, ?_⟩, ?_⟩
  · exact finiteAnalyticObserverPhase_dimension_eq
      energy series henergy omega hreal observe r hτ μ hμ
  · unfold observerPhaseLawTemporalDimension
    have hle :
        Module.finrank ℚ
            (observerPhaseLawConstraintSpace μ observe) ≤
          Module.finrank ℚ O :=
      Submodule.finrank_le _
    omega
  · intro ν hν
    exact hμunique ν hν.1

end

end GaloisForLFunctions.HTGeometry
