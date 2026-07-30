import GaloisForLFunctions.HTGeometry.TemporalPhaseValuationTomographyLaw
import GaloisForLFunctions.HTGeometry.FiniteTerminalTemporalHaarLaw

/-!
# The observer-time Fourier--valuation atlas

A finite analytic real spectrum does not produce an unrelated limiting law
at each inverse-power observation horizon.  All horizons belong to one
unique phase atlas.  Every member of the atlas has the complete character
transform prescribed by the same analytic birth valuation.

The atlas is operationally complete in the converse direction: the first
atlas layer whose Fourier coefficient ceases to be one recovers the exact
analytic birth order of that character.  Thus the scale-indexed phase laws
and the character valuation are two representations of one invariant.
-/

open Filter MeasureTheory Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A scale-indexed phase law is the Fourier--valuation atlas of an analytic
spectrum when every inverse-power horizon is the corresponding weak limit
and satisfies the complete spectral-resolution Fourier law. -/
def IsObserverTimeFourierValuationAtlas
    {d : Type*} [Fintype d]
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (omega : ℝ → d → ℝ)
    (τ : ℝ)
    (atlas : ℕ → ProbabilityMeasure (UnitAddTorus d)) : Prop :=
  ∀ r,
    Tendsto
        (fun g =>
          finiteTorusPhaseProbabilityMeasure
            (omega g) (τ / g ^ r))
        (𝓝[>] 0) (𝓝 (atlas r)) ∧
      SpectralResolutionFourierLaw series r τ (atlas r)

/-- **Observer-time Fourier--valuation atlas law.** Every finite analytic
real spectrum and every positive observation prefactor determine one unique
simultaneous atlas over all inverse-power horizons. -/
theorem existsUnique_observerTimeFourierValuationAtlas
    {d : Type*} [Fintype d]
    (energy : d → ℂ → ℂ)
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (omega : ℝ → d → ℝ)
    (hreal : ∀ i, ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      energy i (g : ℂ) = (omega g i : ℂ))
    {τ : ℝ} (hτ : 0 < τ) :
    ∃! atlas : ℕ → ProbabilityMeasure (UnitAddTorus d),
      IsObserverTimeFourierValuationAtlas series omega τ atlas := by
  let atlas : ℕ → ProbabilityMeasure (UnitAddTorus d) :=
    fun r =>
      Classical.choose
        (existsUnique_finiteAnalyticPhaseEnsemble_limit
          energy series henergy omega hreal r hτ)
  have hatlasLimit : ∀ r,
      Tendsto
        (fun g =>
          finiteTorusPhaseProbabilityMeasure
            (omega g) (τ / g ^ r))
        (𝓝[>] 0) (𝓝 (atlas r)) := by
    intro r
    exact
      (Classical.choose_spec
        (existsUnique_finiteAnalyticPhaseEnsemble_limit
          energy series henergy omega hreal r hτ)).1
  refine ⟨atlas, ?_, ?_⟩
  · intro r
    refine ⟨hatlasLimit r, ?_⟩
    exact finiteAnalyticTemporalPhase_completeFourierLaw
      energy series henergy omega hreal r hτ
      (atlas r) (hatlasLimit r)
  · intro other hother
    funext r
    exact tendsto_nhds_unique (hother r).1 (hatlasLimit r)

/-- Every atlas layer's almost-sure character constraints are exactly the
analytic relations whose valuation lies beyond that layer. -/
theorem observerTimeFourierValuationAtlas_constraint_iff
    {d : Type*} [Fintype d]
    (energy : d → ℂ → ℂ)
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (omega : ℝ → d → ℝ)
    (hreal : ∀ i, ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      energy i (g : ℂ) = (omega g i : ℂ))
    {τ : ℝ} (hτ : 0 < τ)
    (atlas : ℕ → ProbabilityMeasure (UnitAddTorus d))
    (hatlas :
      IsObserverTimeFourierValuationAtlas series omega τ atlas)
    (r : ℕ) (k : ProjectiveCharacter d) :
    phaseLawConstraint (atlas r) k ↔
      k ∈ spectralConstraintFiltration
        (spectralTaylorJet series) (r + 1) := by
  obtain ⟨μ, hμ, hμunique⟩ :=
    existsUnique_finiteAnalyticTemporalPhaseSupport
      energy series henergy omega hreal r hτ
  have hatlasEq : atlas r = μ :=
    tendsto_nhds_unique (hatlas r).1 hμ.1
  rw [hatlasEq]
  exact hμ.2 k

/-- **Fourier--valuation tomography.** The atlas recovers every active
character's exact analytic birth valuation as its first unlocked layer. -/
theorem observerTimeFourierValuationAtlas_firstUnlock_eq_birthOrder
    {d : Type*} [Fintype d]
    (energy : d → ℂ → ℂ)
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (omega : ℝ → d → ℝ)
    (hreal : ∀ i, ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      energy i (g : ℂ) = (omega g i : ℂ))
    {τ : ℝ} (hτ : 0 < τ)
    (atlas : ℕ → ProbabilityMeasure (UnitAddTorus d))
    (hatlas :
      IsObserverTimeFourierValuationAtlas series omega τ atlas)
    (k : ProjectiveCharacter d)
    (hactive :
      SpectralCharacterActive (spectralTaylorJet series) k) :
    ∃ hunlocks : ∃ r, PhaseLawCharacterUnlocked (atlas r) k,
      firstPhaseLawCharacterUnlockingOrder atlas k hunlocks =
        spectralCharacterBirthOrder
          (spectralTaylorJet series) k hactive := by
  exact firstPhaseLawCharacterUnlockingOrder_eq_birthOrder
    energy series henergy omega hreal hτ atlas
    (fun r => (hatlas r).1) k hactive

/-- At every atlas layer, observable character dimension and unresolved
constraint rank are complementary parts of one fixed projective rank. -/
theorem observerTimeFourierValuationAtlas_dimension_conservation
    {d : Type*} [Fintype d]
    (energy : d → ℂ → ℂ)
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (omega : ℝ → d → ℝ)
    (hreal : ∀ i, ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      energy i (g : ℂ) = (omega g i : ℂ))
    {τ : ℝ} (hτ : 0 < τ)
    (atlas : ℕ → ProbabilityMeasure (UnitAddTorus d))
    (hatlas :
      IsObserverTimeFourierValuationAtlas series omega τ atlas)
    (r : ℕ) :
    phaseLawTemporalDimension (atlas r) =
        temporalDimension (spectralTaylorJet series) (r + 1) ∧
      phaseLawTemporalDimension (atlas r) +
          Module.finrank ℚ
            (phaseLawConstraintRationalSpace (atlas r)) =
        Module.finrank ℚ (ProjectiveRationalCharacter d) := by
  obtain ⟨μ, hμ, hμunique⟩ :=
    existsUnique_finiteAnalyticTemporalSupportConservation
      energy series henergy omega hreal r hτ
  have hatlasEq : atlas r = μ :=
    tendsto_nhds_unique (hatlas r).1 hμ.1
  rw [hatlasEq]
  exact ⟨hμ.2.1, hμ.2.2⟩

/-- Positive continuous observation prefactors. -/
abbrev PositiveObservationPrefactor := Set.Ioi (0 : ℝ)

/-- The complete observer-time atlas retains every inverse-power horizon
and every positive continuous observation prefactor. -/
def IsCompleteObserverTimeFourierValuationAtlas
    {d : Type*} [Fintype d]
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (omega : ℝ → d → ℝ)
    (atlas :
      ℕ → PositiveObservationPrefactor →
        ProbabilityMeasure (UnitAddTorus d)) : Prop :=
  ∀ r τ,
    Tendsto
        (fun g =>
          finiteTorusPhaseProbabilityMeasure
            (omega g) (τ.1 / g ^ r))
        (𝓝[>] 0) (𝓝 (atlas r τ)) ∧
      SpectralResolutionFourierLaw series r τ.1 (atlas r τ)

/-- **Complete observer-time atlas law.** A finite analytic real spectrum
determines one unique simultaneous probability-law atlas over every
discrete horizon order and every positive continuous observation
prefactor. -/
theorem existsUnique_completeObserverTimeFourierValuationAtlas
    {d : Type*} [Fintype d]
    (energy : d → ℂ → ℂ)
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (omega : ℝ → d → ℝ)
    (hreal : ∀ i, ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      energy i (g : ℂ) = (omega g i : ℂ)) :
    ∃! atlas :
        ℕ → PositiveObservationPrefactor →
          ProbabilityMeasure (UnitAddTorus d),
      IsCompleteObserverTimeFourierValuationAtlas
        series omega atlas := by
  let atlas :
      ℕ → PositiveObservationPrefactor →
        ProbabilityMeasure (UnitAddTorus d) :=
    fun r τ =>
      Classical.choose
        (existsUnique_finiteAnalyticPhaseEnsemble_limit
          energy series henergy omega hreal r τ.2)
  have hatlasLimit : ∀ r τ,
      Tendsto
        (fun g =>
          finiteTorusPhaseProbabilityMeasure
            (omega g) (τ.1 / g ^ r))
        (𝓝[>] 0) (𝓝 (atlas r τ)) := by
    intro r τ
    exact
      (Classical.choose_spec
        (existsUnique_finiteAnalyticPhaseEnsemble_limit
          energy series henergy omega hreal r τ.2)).1
  refine ⟨atlas, ?_, ?_⟩
  · intro r τ
    exact
      ⟨hatlasLimit r τ,
        finiteAnalyticTemporalPhase_completeFourierLaw
          energy series henergy omega hreal r τ.2
          (atlas r τ) (hatlasLimit r τ)⟩
  · intro other hother
    funext r τ
    exact tendsto_nhds_unique
      (hother r τ).1 (hatlasLimit r τ)

/-- Every positive-prefactor slice of the complete atlas is the unique
fixed-prefactor Fourier--valuation atlas. -/
theorem completeObserverTimeFourierValuationAtlas_slice
    {d : Type*} [Fintype d]
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (omega : ℝ → d → ℝ)
    (atlas :
      ℕ → PositiveObservationPrefactor →
        ProbabilityMeasure (UnitAddTorus d))
    (hatlas :
      IsCompleteObserverTimeFourierValuationAtlas
        series omega atlas)
    (τ : PositiveObservationPrefactor) :
    IsObserverTimeFourierValuationAtlas
      series omega τ.1 (fun r => atlas r τ) := by
  intro r
  exact hatlas r τ

/-- Sinc vanishes exactly where sine vanishes away from the removable
origin. -/
theorem real_sinc_eq_zero_iff_sin_eq_zero
    {x : ℝ} (hx : x ≠ 0) :
    Real.sinc x = 0 ↔ Real.sin x = 0 := by
  rw [Real.sinc_of_ne_zero hx]
  simp [hx]

/-- **Critical-profile identifiability.** The complete positive-scale sinc
profile determines its positive activation magnitude uniquely. -/
theorem real_sinc_positive_scale_injective
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hprofile : ∀ τ : ℝ, 0 < τ →
      Real.sinc (τ * a) = Real.sinc (τ * b)) :
    a = b := by
  have hπa : 0 < Real.pi / a := div_pos Real.pi_pos ha
  have hπb : 0 < Real.pi / b := div_pos Real.pi_pos hb
  have hsincπ : Real.sinc Real.pi = 0 := by
    rw [Real.sinc_of_ne_zero Real.pi_ne_zero, Real.sin_pi]
    simp
  have hzeroB : Real.sinc ((Real.pi / a) * b) = 0 := by
    have h := hprofile (Real.pi / a) hπa
    rw [show (Real.pi / a) * a = Real.pi by field_simp] at h
    exact hsincπ ▸ h.symm
  have hargB : (Real.pi / a) * b ≠ 0 :=
    mul_ne_zero (div_ne_zero Real.pi_ne_zero ha.ne') hb.ne'
  obtain ⟨n, hn⟩ :=
    Real.sin_eq_zero_iff.mp
      ((real_sinc_eq_zero_iff_sin_eq_zero hargB).mp hzeroB)
  have hnratio : (n : ℝ) = b / a := by
    apply mul_left_cancel₀ Real.pi_ne_zero
    calc
      Real.pi * (n : ℝ) = (n : ℝ) * Real.pi := mul_comm _ _
      _ = (Real.pi / a) * b := hn
      _ = Real.pi * (b / a) := by field_simp
  have hzeroA : Real.sinc ((Real.pi / b) * a) = 0 := by
    have h := hprofile (Real.pi / b) hπb
    rw [show (Real.pi / b) * b = Real.pi by field_simp] at h
    exact hsincπ ▸ h
  have hargA : (Real.pi / b) * a ≠ 0 :=
    mul_ne_zero (div_ne_zero Real.pi_ne_zero hb.ne') ha.ne'
  obtain ⟨m, hm⟩ :=
    Real.sin_eq_zero_iff.mp
      ((real_sinc_eq_zero_iff_sin_eq_zero hargA).mp hzeroA)
  have hmratio : (m : ℝ) = a / b := by
    apply mul_left_cancel₀ Real.pi_ne_zero
    calc
      Real.pi * (m : ℝ) = (m : ℝ) * Real.pi := mul_comm _ _
      _ = (Real.pi / b) * a := hm
      _ = Real.pi * (a / b) := by field_simp
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    rw [hnratio]
    exact div_pos hb ha
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    rw [hmratio]
    exact div_pos ha hb
  have hnint : (1 : ℤ) ≤ n := by
    exact_mod_cast hnpos
  have hmint : (1 : ℤ) ≤ m := by
    exact_mod_cast hmpos
  have hnge : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hnint
  have hmge : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hmint
  have hprod : (n : ℝ) * (m : ℝ) = 1 := by
    rw [hnratio, hmratio]
    field_simp
  have hnle : (n : ℝ) ≤ 1 := by
    calc
      (n : ℝ) = (n : ℝ) * 1 := by ring
      _ ≤ (n : ℝ) * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hmge
          (le_trans (by norm_num) hnge)
      _ = 1 := hprod
  have hn1 : (n : ℝ) = 1 := le_antisymm hnle hnge
  rw [hnratio] at hn1
  field_simp at hn1
  linarith

/-- **Complete critical-profile law.** For every active projective
character, its atlas coefficients at the birth horizon form one sinc
profile with a unique positive activation magnitude. -/
theorem completeObserverTimeAtlas_uniqueCriticalProfile
    {d : Type*} [Fintype d]
    (energy : d → ℂ → ℂ)
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (omega : ℝ → d → ℝ)
    (hreal : ∀ i, ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      energy i (g : ℂ) = (omega g i : ℂ))
    (atlas :
      ℕ → PositiveObservationPrefactor →
        ProbabilityMeasure (UnitAddTorus d))
    (hatlas :
      IsCompleteObserverTimeFourierValuationAtlas
        series omega atlas)
    (k : ProjectiveCharacter d)
    (hactive :
      SpectralCharacterActive (spectralTaylorJet series) k) :
    ∃! c : ℝ, 0 < c ∧
      ∀ τ : PositiveObservationPrefactor,
        projectivePhaseLawFourierCoefficient
            (atlas
              (spectralCharacterBirthOrder
                (spectralTaylorJet series) k hactive) τ) k =
          Real.sinc (τ.1 * c) := by
  obtain ⟨c, hprofile⟩ :=
    hasPositiveBirthProfile_finiteProjectiveCharacter
      energy series henergy omega hreal k hactive
  let b :=
    spectralCharacterBirthOrder
      (spectralTaylorJet series) k hactive
  have hcritical : ∀ τ : PositiveObservationPrefactor,
      projectivePhaseLawFourierCoefficient (atlas b τ) k =
        Real.sinc (τ.1 * c) := by
    intro τ
    let coefficient :
        ProbabilityMeasure (UnitAddTorus d) → ℂ :=
      fun ρ => projectivePhaseLawFourierCoefficient ρ k
    have hcoefficient :
        Tendsto
          (fun g =>
            coefficient
              (finiteTorusPhaseProbabilityMeasure
                (omega g) (τ.1 / g ^ b)))
          (𝓝[>] 0) (𝓝 (coefficient (atlas b τ))) :=
      (continuous_integral_complex_continuousMap
        (UnitAddTorus.mFourier
          (finiteCharacterOfProjective k))).continuousAt.tendsto.comp
            (hatlas b τ).1
    have hwall :=
      spectralCharacterReporter_wallCrossing hprofile τ.2
    have hreporter :
        Tendsto
          (fun g =>
            coefficient
              (finiteTorusPhaseProbabilityMeasure
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
            (|finiteProjectiveCharacterDetuning k (omega g)| /
              g ^ b)) : ℂ) =
          projectivePhaseLawFourierCoefficient
            (finiteTorusPhaseProbabilityMeasure
              (omega g) (τ.1 / g ^ b)) k
      rw [projectivePhaseLawFourierCoefficient]
      change
        (Real.sinc
          (τ.1 *
            (|finiteProjectiveCharacterDetuning k (omega g)| /
              g ^ b)) : ℂ) =
          finiteProjectivePhaseCoefficient k
            (omega g) (τ.1 / g ^ b)
      rw [finiteProjectivePhaseCoefficient_eq_sinc]
      exact
        (coe_real_sinc_scaled_abs τ.1
          (finiteProjectiveCharacterDetuning k (omega g))
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
