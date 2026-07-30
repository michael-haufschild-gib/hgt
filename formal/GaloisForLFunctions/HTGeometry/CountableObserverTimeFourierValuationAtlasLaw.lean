import GaloisForLFunctions.HTGeometry.CountableAnalyticPhaseEnsembleWallCrossingLaw
import GaloisForLFunctions.HTGeometry.ObserverTimeFourierValuationAtlasLaw

/-!
# Fourier--valuation atlas for countable analytic spectra

The all-horizon phase atlas does not require a finite ambient spectrum.
Every character of a countable product torus has finite support, so its
analytic birth valuation and Fourier wall crossing remain finite objects.
The complete family of character laws determines one unique probability
law at every horizon and one unique simultaneous atlas over all horizons.
-/

open Filter MeasureTheory Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Sinc is insensitive to the sign of a real detuning when the observation
scale is nonnegative. -/
private theorem countableAtlas_sinc_mul_abs_eq
    (a x : ℝ) (ha : 0 ≤ a) :
    Real.sinc (a * |x|) = Real.sinc (a * x) := by
  have h : Real.sinc |a * x| = Real.sinc (a * x) := by
    by_cases hx : 0 ≤ a * x
    · rw [abs_of_nonneg hx]
    · rw [abs_of_neg (lt_of_not_ge hx)]
      exact Real.sinc_neg (a * x)
  rw [abs_mul, abs_of_nonneg ha] at h
  exact h

private theorem countableAtlas_coe_sinc_scaled_abs_eq
    (τ x g : ℝ) (r : ℕ) (hτ : 0 ≤ τ) (hg : 0 < g) :
    (Real.sinc ((τ / g ^ r) * x) : ℂ) =
      (Real.sinc (τ * (|x| / g ^ r)) : ℂ) := by
  apply congrArg (fun y : ℝ => (y : ℂ))
  rw [show
    τ * (|x| / g ^ r) = (τ / g ^ r) * |x| by
      field_simp]
  exact
    (countableAtlas_sinc_mul_abs_eq
      (τ / g ^ r) x
      (div_nonneg hτ (pow_nonneg hg.le r))).symm

/-- Fourier coefficient of a finite-support character under a probability
law on a countable product phase torus. -/
def countablePhaseLawFourierCoefficient
    {I : Type*}
    (μ : ProbabilityMeasure (I → UnitAddCircle))
    (n : I →₀ ℤ) : ℂ :=
  ∫ x, infiniteTorusFourier n x
    ∂(μ : Measure (I → UnitAddCircle))

/-- Complete countable character transform at one inverse-power horizon.
Exact relations remain locked.  A character with positive birth profile
is locked below birth, has its sinc coefficient at birth, and is dephased
above birth. -/
def CountableSpectralResolutionFourierLaw
    {I : Type*}
    (omega : ℝ → I → ℝ)
    (r : ℕ) (τ : ℝ)
    (μ : ProbabilityMeasure (I → UnitAddCircle)) : Prop :=
  ∀ n : I →₀ ℤ,
    ((∀ᶠ g in 𝓝[>] (0 : ℝ),
        infiniteTorusCharacterDetuning n (omega g) = 0) →
      countablePhaseLawFourierCoefficient μ n = 1) ∧
    (∀ b c,
      HasPositiveBirthProfile
          (fun g =>
            |infiniteTorusCharacterDetuning n (omega g)|) b c →
        (r < b →
          countablePhaseLawFourierCoefficient μ n = 1) ∧
        (r = b →
          countablePhaseLawFourierCoefficient μ n =
            Real.sinc (τ * c)) ∧
        (b < r →
          countablePhaseLawFourierCoefficient μ n = 0))

/-- Every weak limit of a complete countable phase ensemble satisfies the
complete characterwise Fourier wall-crossing law. -/
theorem countableTemporalPhase_completeFourierLaw
    {I : Type*} [Countable I]
    (omega : ℝ → I → ℝ)
    (hcomplete : HasCompleteCountableCharacterBirthProfiles omega)
    (r : ℕ) {τ : ℝ} (hτ : 0 < τ)
    (μ : ProbabilityMeasure (I → UnitAddCircle))
    (hμ :
      Tendsto
        (fun g =>
          infiniteTorusPhaseProbabilityMeasure
            (omega g) (τ / g ^ r))
        (𝓝[>] 0) (𝓝 μ)) :
    CountableSpectralResolutionFourierLaw omega r τ μ := by
  intro n
  let coefficient :
      ProbabilityMeasure (I → UnitAddCircle) → ℂ :=
    fun ρ => countablePhaseLawFourierCoefficient ρ n
  have hcoefficient :
      Tendsto
        (fun g =>
          coefficient
            (infiniteTorusPhaseProbabilityMeasure
              (omega g) (τ / g ^ r)))
        (𝓝[>] 0) (𝓝 (coefficient μ)) :=
    (continuous_integral_complex_continuousMap_infinite
      (infiniteTorusFourier n)).continuousAt.tendsto.comp hμ
  constructor
  · intro hinactive
    have hone :
        Tendsto
          (fun g =>
            coefficient
              (infiniteTorusPhaseProbabilityMeasure
                (omega g) (τ / g ^ r)))
          (𝓝[>] 0) (𝓝 1) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hinactive, self_mem_nhdsWithin] with g hgzero hg
      change 0 < g at hg
      symm
      change
        countablePhaseLawFourierCoefficient
          (infiniteTorusPhaseProbabilityMeasure
            (omega g) (τ / g ^ r)) n = 1
      rw [countablePhaseLawFourierCoefficient,
        infiniteTorusPhaseProbabilityMeasure_fourier_integral,
        hgzero]
      simp [coefficient, countablePhaseLawFourierCoefficient]
    exact tendsto_nhds_unique hcoefficient hone
  · intro b c hprofile
    have hwall := spectralCharacterReporter_wallCrossing hprofile hτ
    constructor
    · intro hrb
      have hone :
          Tendsto
            (fun g =>
              coefficient
                (infiniteTorusPhaseProbabilityMeasure
                  (omega g) (τ / g ^ r)))
            (𝓝[>] 0) (𝓝 1) := by
        have ht := hwall.1 r hrb
        apply
          (Complex.continuous_ofReal.continuousAt.tendsto.comp ht).congr'
        filter_upwards [self_mem_nhdsWithin] with g hg
        change 0 < g at hg
        change
          (Real.sinc
            (τ *
              (|infiniteTorusCharacterDetuning n (omega g)| /
                g ^ r)) : ℂ) =
            countablePhaseLawFourierCoefficient
              (infiniteTorusPhaseProbabilityMeasure
                (omega g) (τ / g ^ r)) n
        rw [countablePhaseLawFourierCoefficient,
          infiniteTorusPhaseProbabilityMeasure_fourier_integral]
        exact
          (countableAtlas_coe_sinc_scaled_abs_eq τ
            (infiniteTorusCharacterDetuning n (omega g))
            g r hτ.le hg).symm
      exact tendsto_nhds_unique hcoefficient hone
    constructor
    · intro hrb
      subst r
      have hcritical :
          Tendsto
            (fun g =>
              coefficient
                (infiniteTorusPhaseProbabilityMeasure
                  (omega g) (τ / g ^ b)))
            (𝓝[>] 0) (𝓝 (Real.sinc (τ * c))) := by
        have ht := hwall.2.1
        apply
          (Complex.continuous_ofReal.continuousAt.tendsto.comp ht).congr'
        filter_upwards [self_mem_nhdsWithin] with g hg
        change 0 < g at hg
        change
          (Real.sinc
            (τ *
              (|infiniteTorusCharacterDetuning n (omega g)| /
                g ^ b)) : ℂ) =
            countablePhaseLawFourierCoefficient
              (infiniteTorusPhaseProbabilityMeasure
                (omega g) (τ / g ^ b)) n
        rw [countablePhaseLawFourierCoefficient,
          infiniteTorusPhaseProbabilityMeasure_fourier_integral]
        exact
          (countableAtlas_coe_sinc_scaled_abs_eq τ
            (infiniteTorusCharacterDetuning n (omega g))
            g b hτ.le hg).symm
      exact tendsto_nhds_unique hcoefficient hcritical
    · intro hbr
      have hzero :
          Tendsto
            (fun g =>
              coefficient
                (infiniteTorusPhaseProbabilityMeasure
                  (omega g) (τ / g ^ r)))
            (𝓝[>] 0) (𝓝 0) := by
        have ht := hwall.2.2 r hbr
        apply
          (Complex.continuous_ofReal.continuousAt.tendsto.comp ht).congr'
        filter_upwards [self_mem_nhdsWithin] with g hg
        change 0 < g at hg
        change
          (Real.sinc
            (τ *
              (|infiniteTorusCharacterDetuning n (omega g)| /
                g ^ r)) : ℂ) =
            countablePhaseLawFourierCoefficient
              (infiniteTorusPhaseProbabilityMeasure
                (omega g) (τ / g ^ r)) n
        rw [countablePhaseLawFourierCoefficient,
          infiniteTorusPhaseProbabilityMeasure_fourier_integral]
        exact
          (countableAtlas_coe_sinc_scaled_abs_eq τ
            (infiniteTorusCharacterDetuning n (omega g))
            g r hτ.le hg).symm
      exact tendsto_nhds_unique hcoefficient hzero

/-- A simultaneous countable Fourier--valuation atlas. -/
def IsCountableObserverTimeFourierValuationAtlas
    {I : Type*} [Countable I]
    (omega : ℝ → I → ℝ)
    (τ : ℝ)
    (atlas : ℕ → ProbabilityMeasure (I → UnitAddCircle)) : Prop :=
  ∀ r,
    Tendsto
        (fun g =>
          infiniteTorusPhaseProbabilityMeasure
            (omega g) (τ / g ^ r))
        (𝓝[>] 0) (𝓝 (atlas r)) ∧
      CountableSpectralResolutionFourierLaw omega r τ (atlas r)

/-- **Countable observer-time atlas law.** Every countable analytic real
spectrum has one unique complete all-horizon Fourier--valuation atlas. -/
theorem existsUnique_countableObserverTimeFourierValuationAtlas
    {I : Type*} [Countable I]
    (energy : I → ℂ → ℂ)
    (series : I → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (omega : ℝ → I → ℝ)
    (hreal : ∀ i, ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      energy i (g : ℂ) = (omega g i : ℂ))
    {τ : ℝ} (hτ : 0 < τ) :
    ∃! atlas : ℕ → ProbabilityMeasure (I → UnitAddCircle),
      IsCountableObserverTimeFourierValuationAtlas omega τ atlas := by
  have hcomplete :=
    hasCompleteCountableCharacterBirthProfiles_of_analytic
      energy series henergy omega hreal
  let atlas : ℕ → ProbabilityMeasure (I → UnitAddCircle) :=
    fun r =>
      Classical.choose
        (existsUnique_countableAnalyticPhaseEnsemble_limit
          energy series henergy omega hreal r hτ)
  have hatlasLimit : ∀ r,
      Tendsto
        (fun g =>
          infiniteTorusPhaseProbabilityMeasure
            (omega g) (τ / g ^ r))
        (𝓝[>] 0) (𝓝 (atlas r)) := by
    intro r
    exact
      (Classical.choose_spec
        (existsUnique_countableAnalyticPhaseEnsemble_limit
          energy series henergy omega hreal r hτ)).1
  refine ⟨atlas, ?_, ?_⟩
  · intro r
    exact
      ⟨hatlasLimit r,
        countableTemporalPhase_completeFourierLaw
          omega hcomplete r hτ (atlas r) (hatlasLimit r)⟩
  · intro other hother
    funext r
    exact tendsto_nhds_unique (hother r).1 (hatlasLimit r)

/-- Complete two-scale atlas for a countable product phase torus. -/
def IsCompleteCountableObserverTimeFourierValuationAtlas
    {I : Type*} [Countable I]
    (omega : ℝ → I → ℝ)
    (atlas :
      ℕ → PositiveObservationPrefactor →
        ProbabilityMeasure (I → UnitAddCircle)) : Prop :=
  ∀ r τ,
    Tendsto
        (fun g =>
          infiniteTorusPhaseProbabilityMeasure
            (omega g) (τ.1 / g ^ r))
        (𝓝[>] 0) (𝓝 (atlas r τ)) ∧
      CountableSpectralResolutionFourierLaw
        omega r τ.1 (atlas r τ)

/-- **Complete countable atlas law.** Every countable analytic real
spectrum determines one unique phase-probability atlas over all discrete
horizon orders and all positive continuous prefactors. -/
theorem existsUnique_completeCountableObserverTimeFourierValuationAtlas
    {I : Type*} [Countable I]
    (energy : I → ℂ → ℂ)
    (series : I → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (omega : ℝ → I → ℝ)
    (hreal : ∀ i, ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      energy i (g : ℂ) = (omega g i : ℂ)) :
    ∃! atlas :
        ℕ → PositiveObservationPrefactor →
          ProbabilityMeasure (I → UnitAddCircle),
      IsCompleteCountableObserverTimeFourierValuationAtlas
        omega atlas := by
  have hcomplete :=
    hasCompleteCountableCharacterBirthProfiles_of_analytic
      energy series henergy omega hreal
  let atlas :
      ℕ → PositiveObservationPrefactor →
        ProbabilityMeasure (I → UnitAddCircle) :=
    fun r τ =>
      Classical.choose
        (existsUnique_countableAnalyticPhaseEnsemble_limit
          energy series henergy omega hreal r τ.2)
  have hatlasLimit : ∀ r τ,
      Tendsto
        (fun g =>
          infiniteTorusPhaseProbabilityMeasure
            (omega g) (τ.1 / g ^ r))
        (𝓝[>] 0) (𝓝 (atlas r τ)) := by
    intro r τ
    exact
      (Classical.choose_spec
        (existsUnique_countableAnalyticPhaseEnsemble_limit
          energy series henergy omega hreal r τ.2)).1
  refine ⟨atlas, ?_, ?_⟩
  · intro r τ
    exact
      ⟨hatlasLimit r τ,
        countableTemporalPhase_completeFourierLaw
          omega hcomplete r τ.2
          (atlas r τ) (hatlasLimit r τ)⟩
  · intro other hother
    funext r τ
    exact tendsto_nhds_unique
      (hother r τ).1 (hatlasLimit r τ)

/-- **Countable critical-profile law.** Every finite-support character
with a positive analytic birth profile has one unique positive activation
magnitude encoded by the complete countable atlas. -/
theorem completeCountableObserverTimeAtlas_uniqueCriticalProfile
    {I : Type*} [Countable I]
    (omega : ℝ → I → ℝ)
    (atlas :
      ℕ → PositiveObservationPrefactor →
        ProbabilityMeasure (I → UnitAddCircle))
    (hatlas :
      IsCompleteCountableObserverTimeFourierValuationAtlas
        omega atlas)
    (n : I →₀ ℤ) (b : ℕ) :
    (∃ c : ℝ,
      HasPositiveBirthProfile
        (fun g =>
          |infiniteTorusCharacterDetuning n (omega g)|) b c) →
    ∃! c : ℝ, 0 < c ∧
      ∀ τ : PositiveObservationPrefactor,
        countablePhaseLawFourierCoefficient (atlas b τ) n =
          Real.sinc (τ.1 * c) := by
  rintro ⟨c, hprofile⟩
  have hcritical : ∀ τ : PositiveObservationPrefactor,
      countablePhaseLawFourierCoefficient (atlas b τ) n =
        Real.sinc (τ.1 * c) := by
    intro τ
    let coefficient :
        ProbabilityMeasure (I → UnitAddCircle) → ℂ :=
      fun ρ => countablePhaseLawFourierCoefficient ρ n
    have hcoefficient :
        Tendsto
          (fun g =>
            coefficient
              (infiniteTorusPhaseProbabilityMeasure
                (omega g) (τ.1 / g ^ b)))
          (𝓝[>] 0) (𝓝 (coefficient (atlas b τ))) :=
      (continuous_integral_complex_continuousMap_infinite
        (infiniteTorusFourier n)).continuousAt.tendsto.comp
          (hatlas b τ).1
    have hwall :=
      spectralCharacterReporter_wallCrossing hprofile τ.2
    have hreporter :
        Tendsto
          (fun g =>
            coefficient
              (infiniteTorusPhaseProbabilityMeasure
                (omega g) (τ.1 / g ^ b)))
          (𝓝[>] 0) (𝓝 (Real.sinc (τ.1 * c))) := by
      apply
        (Complex.continuous_ofReal.continuousAt.tendsto.comp
          hwall.2.1).congr'
      filter_upwards [self_mem_nhdsWithin] with g hg
      change 0 < g at hg
      change
        (Real.sinc
          (τ.1 *
            (|infiniteTorusCharacterDetuning n (omega g)| /
              g ^ b)) : ℂ) =
          countablePhaseLawFourierCoefficient
            (infiniteTorusPhaseProbabilityMeasure
              (omega g) (τ.1 / g ^ b)) n
      rw [countablePhaseLawFourierCoefficient,
        infiniteTorusPhaseProbabilityMeasure_fourier_integral]
      exact
        (countableAtlas_coe_sinc_scaled_abs_eq τ.1
          (infiniteTorusCharacterDetuning n (omega g))
          g b τ.2.le hg).symm
    exact tendsto_nhds_unique hcoefficient hreporter
  refine ⟨c, ⟨hprofile.2, hcritical⟩, ?_⟩
  intro other hother
  symm
  apply real_sinc_positive_scale_injective hprofile.2 hother.1
  intro τ hτ
  let τpos : PositiveObservationPrefactor := ⟨τ, hτ⟩
  apply Complex.ofReal_injective
  exact (hcritical τpos).symm.trans (hother.2 τpos)

end

end GaloisForLFunctions.HTGeometry
