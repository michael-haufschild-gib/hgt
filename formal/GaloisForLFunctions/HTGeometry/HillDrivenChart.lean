import GaloisForLFunctions.HTGeometry.HillDrivenWave
import GaloisForLFunctions.HTGeometry.HillEventContinuity
import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonChartGeneric
import GaloisForLFunctions.HTGeometry.ClockPiPartialC1

/-!
# The chart field of the driven evolution, and its first partials

The corpus's chart instrument is generic in the density family, so the field of the driven evolution
and its coordinate derivatives are instances of it: the time coordinate differentiates the family,
a spatial coordinate multiplies it by the frequency factor.

Continuity of the partials in the event does *not* go through continuity in the frequency — the
velocity density is only known to be measurable there — but through the dominated-convergence
instrument of the free construction, which asks for continuity in time and a window bound instead.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

section DrivenChart

variable {d N : ℕ}

/-- The chart field of the driven evolution. -/
noncomputable def hillDrivenChartField (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) N)
    (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ) : (Fin (d + 1) → ℝ) → ℝ :=
  kgChartOf (hillDrivenDensity a b G₀)

/-! ## Continuity in time at a fixed frequency -/

theorem continuous_hillDrivenDensity_time (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) N) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (ξ : EuclideanSpace ℝ (Fin d)) :
    Continuous fun t : ℝ => hillDrivenDensity a b G₀ t ξ := by
  have heval : Continuous fun t : ℝ => hillPotentialFlow a b G₀ t ξ :=
    (BoundedContinuousFunction.evalCLM (𝕜 := ℝ) ξ).continuous.comp
      (continuous_hillPotentialFlow a b G₀)
  exact continuous_const.mul heval

theorem continuous_hillDrivenDensityDeriv_time (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) N) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (ξ : EuclideanSpace ℝ (Fin d)) :
    Continuous fun t : ℝ => hillDrivenDensityDeriv a b G₀ t ξ := by
  have hderiv : Continuous fun t : ℝ => hillFlowApplyDeriv a b G₀ ξ t :=
    continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_hillFlowApplyDeriv a b G₀ ξ t).continuousAt
  exact continuous_const.mul hderiv

theorem continuous_hillDrivenDensitySecond_time (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) N) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (ξ : EuclideanSpace ℝ (Fin d)) :
    Continuous fun t : ℝ => hillDrivenDensitySecond a b G₀ t ξ := by
  have hfreq : Continuous fun t : ℝ => ((a.freq ξ t ^ (2 : ℕ) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((a.continuous_freq ξ).pow 2)
  have heval : Continuous fun t : ℝ => hillPotentialFlow a b G₀ t ξ :=
    (BoundedContinuousFunction.evalCLM (𝕜 := ℝ) ξ).continuous.comp
      (continuous_hillPotentialFlow a b G₀)
  have hsrc : Continuous fun t : ℝ => hillFlowSource a b G₀ ξ t :=
    continuous_hillFlowSource a b G₀ ξ
  exact continuous_const.mul ((hfreq.neg.mul heval).add hsrc)

/-! ## The window bounds in the form the instrument consumes -/

theorem norm_hillDrivenDensity_le_weight (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) N) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    {T t : ℝ} (hT : 0 ≤ T) (ht : |t| ≤ T) (ξ : EuclideanSpace ℝ (Fin d)) :
    ‖hillDrivenDensity a b G₀ t ξ‖ ≤ hillFlowSize a b G₀ T * (kgFreq ξ ^ N)⁻¹ := by
  have hbase := norm_kgWeighted_le N (hillPotentialFlow a b G₀ t) ξ
  have hflow := norm_hillPotentialFlow_le_window a b G₀ hT ht
  refine hbase.trans ?_
  have hinv : (0 : ℝ) ≤ (kgFreq ξ ^ N)⁻¹ := inv_nonneg.mpr (pow_pos (kgFreq_pos ξ) N).le
  calc (kgFreq ξ ^ N)⁻¹ * ‖hillPotentialFlow a b G₀ t‖
      ≤ (kgFreq ξ ^ N)⁻¹ * hillFlowSize a b G₀ T := mul_le_mul_of_nonneg_left hflow hinv
    _ = hillFlowSize a b G₀ T * (kgFreq ξ ^ N)⁻¹ := by ring

theorem norm_hillDrivenDensityDeriv_le_weight (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) N) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    {T t : ℝ} (hT : 0 ≤ T) (ht : |t| ≤ T) (ξ : EuclideanSpace ℝ (Fin d)) :
    ‖hillDrivenDensityDeriv a b G₀ t ξ‖ ≤ hillVelocitySize a b G₀ T * (kgFreq ξ ^ N)⁻¹ := by
  rw [norm_hillDrivenDensityDeriv]
  have hinv : (0 : ℝ) ≤ (kgFreq ξ ^ N)⁻¹ := inv_nonneg.mpr (pow_pos (kgFreq_pos ξ) N).le
  calc (kgFreq ξ ^ N)⁻¹ * ‖hillFlowApplyDeriv a b G₀ ξ t‖
      ≤ (kgFreq ξ ^ N)⁻¹ * hillVelocitySize a b G₀ T :=
        mul_le_mul_of_nonneg_left (norm_hillFlowApplyDeriv_le_window a b G₀ hT ht ξ) hinv
    _ = hillVelocitySize a b G₀ T * (kgFreq ξ ^ N)⁻¹ := by ring

theorem norm_kgDirDensity_hillDriven_le_weight (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) N) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (v : EuclideanSpace ℝ (Fin d)) {T t : ℝ} (hT : 0 ≤ T) (ht : |t| ≤ T)
    (ξ : EuclideanSpace ℝ (Fin d)) :
    ‖kgDirDensity v (hillDrivenDensity a b G₀ t) ξ‖
      ≤ 2 * Real.pi * ‖v‖ * hillFlowSize a b G₀ T * (kgFreq ξ * (kgFreq ξ ^ N)⁻¹) := by
  refine (norm_kgDirDensity_le v _ ξ).trans ?_
  have hpiv : (0 : ℝ) ≤ 2 * Real.pi * ‖v‖ := by positivity
  have hstep : kgFreq ξ * ‖hillDrivenDensity a b G₀ t ξ‖
      ≤ kgFreq ξ * (hillFlowSize a b G₀ T * (kgFreq ξ ^ N)⁻¹) :=
    mul_le_mul_of_nonneg_left (norm_hillDrivenDensity_le_weight a b G₀ hT ht ξ)
      (le_of_lt (kgFreq_pos ξ))
  calc 2 * Real.pi * ‖v‖ * (kgFreq ξ * ‖hillDrivenDensity a b G₀ t ξ‖)
      ≤ 2 * Real.pi * ‖v‖ * (kgFreq ξ * (hillFlowSize a b G₀ T * (kgFreq ξ ^ N)⁻¹)) :=
        mul_le_mul_of_nonneg_left hstep hpiv
    _ = 2 * Real.pi * ‖v‖ * hillFlowSize a b G₀ T * (kgFreq ξ * (kgFreq ξ ^ N)⁻¹) := by ring

/-! ## Continuity of the chart objects -/

theorem continuous_kgChartOf_of_bound {F : ℝ → EuclideanSpace ℝ (Fin d) → ℂ}
    {B : EuclideanSpace ℝ (Fin d) → ℝ}
    (hmeas : ∀ r : ℝ, AEStronglyMeasurable (F r) (volume))
    (htime : ∀ ξ : EuclideanSpace ℝ (Fin d), Continuous fun r : ℝ => F r ξ)
    (hbound : ∀ T : ℝ, ∃ A : ℝ, ∀ r : ℝ, |r| ≤ T → ∀ ξ : EuclideanSpace ℝ (Fin d),
      ‖F r ξ‖ ≤ A * B ξ)
    (hB : Integrable B (volume)) : Continuous (kgChartOf F) := by
  have hjoint : Continuous fun p : ℝ × EuclideanSpace ℝ (Fin d) => kgSynthesis (F p.1) p.2 :=
    continuous_kgSynthesis_event hmeas htime hbound hB
  have hfun : kgChartOf F
      = (fun p : ℝ × EuclideanSpace ℝ (Fin d) => (kgSynthesis (F p.1) p.2).re)
        ∘ (fun y : Fin (d + 1) → ℝ => (y 0, kgSpatial d y)) := rfl
  rw [hfun]
  exact (Complex.continuous_re.comp hjoint).comp (continuous_chartPoint d)

theorem continuous_hillDrivenChartField (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < N)
    (a : HillSpeed) (b : WienerFamily (EuclideanSpace ℝ (Fin d)) N)
    (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ) : Continuous (hillDrivenChartField a b G₀) := by
  refine continuous_kgChartOf_of_bound
    (fun r => (continuous_hillDrivenDensity a b G₀ r).aestronglyMeasurable)
    (fun ξ => continuous_hillDrivenDensity_time a b G₀ ξ) ?_
    (integrable_kgFreq_inv_pow (E := EuclideanSpace ℝ (Fin d)) hN)
  intro T
  rcases le_or_gt 0 T with hT | hT
  · exact ⟨hillFlowSize a b G₀ T, fun r hr ξ => norm_hillDrivenDensity_le_weight a b G₀ hT hr ξ⟩
  · refine ⟨0, fun r hr ξ => ?_⟩
    exact absurd (le_trans (abs_nonneg r) hr) (not_le.mpr hT)

/-! ## The first partials -/

/-- The time partial of the driven chart field. -/
noncomputable def hillDrivenChartTimePartial (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) N) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ) :
    (Fin (d + 1) → ℝ) → ℝ := kgChartOf (hillDrivenDensityDeriv a b G₀)

/-- The `i`-th spatial partial of the driven chart field. -/
noncomputable def hillDrivenChartSpacePartial (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) N) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (i : Fin d) : (Fin (d + 1) → ℝ) → ℝ :=
  kgChartOf (fun t => kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i) (hillDrivenDensity a b G₀ t))

/-- The partial derivatives, indexed by the chart coordinates. -/
noncomputable def hillDrivenChartPartial (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) N) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (j : Fin (d + 1)) : (Fin (d + 1) → ℝ) → ℝ :=
  Fin.cases (hillDrivenChartTimePartial a b G₀)
    (fun i => hillDrivenChartSpacePartial a b G₀ i) j

theorem hillDrivenChartPartial_zero (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) N) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ) :
    hillDrivenChartPartial a b G₀ 0 = hillDrivenChartTimePartial a b G₀ := rfl

theorem hillDrivenChartPartial_succ (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) N) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (i : Fin d) :
    hillDrivenChartPartial a b G₀ i.succ = hillDrivenChartSpacePartial a b G₀ i := by
  rw [hillDrivenChartPartial, Fin.cases_succ]

theorem integrable_hillDrivenDensity (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < N)
    (a : HillSpeed) (b : WienerFamily (EuclideanSpace ℝ (Fin d)) N)
    (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ) (t : ℝ) :
    Integrable (hillDrivenDensity a b G₀ t) (volume) :=
  integrable_kgWeighted (E := EuclideanSpace ℝ (Fin d)) hN (hillPotentialFlow a b G₀ t)

theorem integrable_kgFreq_mul_hillDrivenDensity
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 1 < N) (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) N) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (t : ℝ) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin d) =>
      kgFreq ξ * ‖hillDrivenDensity a b G₀ t ξ‖) (volume) := by
  have hjN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + (1 : ℕ) < N := by
    push_cast
    linarith
  refine (integrable_kgFreq_pow_mul_kgWeighted' (E := EuclideanSpace ℝ (Fin d)) (j := 1) hjN
    (hillPotentialFlow a b G₀ t)).congr ?_
  filter_upwards with ξ
  rw [pow_one]
  rfl

/-- **The driven chart field has all coordinate derivatives.** -/
theorem hasDerivAt_hillDrivenChartField_update
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 1 < N) (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) N) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (y : Fin (d + 1) → ℝ) (j : Fin (d + 1)) :
    HasDerivAt (fun r : ℝ => hillDrivenChartField a b G₀ (Function.update y j r))
      (hillDrivenChartPartial a b G₀ j y) (y j) := by
  have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < N := by linarith
  refine Fin.cases ?_ ?_ j
  · rw [hillDrivenChartPartial_zero]
    refine hasDerivAt_kgChartOf_zero (N := N) hdim
      (fun t => (continuous_hillDrivenDensity a b G₀ t).aestronglyMeasurable)
      (fun t => aestronglyMeasurable_hillDrivenDensityDeriv a b G₀ t)
      (fun t ξ => hasDerivAt_hillDrivenDensity a b G₀ ξ t) ?_
      (fun t => integrable_hillDrivenDensity hdim a b G₀ t) y
    intro T
    rcases le_or_gt 0 T with hT | hT
    · refine ⟨hillVelocitySize a b G₀ T, fun r hr ξ => ?_⟩
      have h := norm_hillDrivenDensityDeriv_le_weight a b G₀ hT hr ξ
      calc ‖hillDrivenDensityDeriv a b G₀ r ξ‖
          ≤ hillVelocitySize a b G₀ T * (kgFreq ξ ^ N)⁻¹ := h
        _ = (kgFreq ξ ^ N)⁻¹ * hillVelocitySize a b G₀ T := by ring
    · refine ⟨0, fun r hr ξ => ?_⟩
      exact absurd (le_trans (abs_nonneg r) hr) (not_le.mpr hT)
  · intro i
    rw [hillDrivenChartPartial_succ]
    exact hasDerivAt_kgChartOf_succ
      (fun t => (continuous_hillDrivenDensity a b G₀ t).aestronglyMeasurable)
      (fun t => integrable_hillDrivenDensity hdim a b G₀ t)
      (fun t => integrable_kgFreq_mul_hillDrivenDensity hN a b G₀ t) y i

/-- **Every first partial is continuous in the event.** -/
theorem continuous_hillDrivenChartPartial
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 1 < N) (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) N) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (j : Fin (d + 1)) : Continuous (hillDrivenChartPartial a b G₀ j) := by
  have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < N := by linarith
  have hjN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + (1 : ℕ) < N := by
    push_cast
    linarith
  refine Fin.cases ?_ ?_ j
  · rw [hillDrivenChartPartial_zero, hillDrivenChartTimePartial]
    refine continuous_kgChartOf_of_bound
      (fun r => aestronglyMeasurable_hillDrivenDensityDeriv a b G₀ r)
      (fun ξ => continuous_hillDrivenDensityDeriv_time a b G₀ ξ) ?_
      (integrable_kgFreq_inv_pow (E := EuclideanSpace ℝ (Fin d)) hdim)
    intro T
    rcases le_or_gt 0 T with hT | hT
    · exact ⟨hillVelocitySize a b G₀ T,
        fun r hr ξ => norm_hillDrivenDensityDeriv_le_weight a b G₀ hT hr ξ⟩
    · refine ⟨0, fun r hr ξ => ?_⟩
      exact absurd (le_trans (abs_nonneg r) hr) (not_le.mpr hT)
  · intro i
    rw [hillDrivenChartPartial_succ, hillDrivenChartSpacePartial]
    refine continuous_kgChartOf_of_bound
      (fun r => aestronglyMeasurable_kgDirDensity
        (continuous_hillDrivenDensity a b G₀ r).aestronglyMeasurable _)
      (fun ξ => ?_) ?_
      (integrable_kgFreq_pow_mul_inv_pow (E := EuclideanSpace ℝ (Fin d)) (j := 1) hjN)
    · exact continuous_kgDirDensity_time _ ξ (continuous_hillDrivenDensity_time a b G₀ ξ)
    · intro T
      rcases le_or_gt 0 T with hT | hT
      · refine ⟨2 * Real.pi * ‖((2 * Real.pi)⁻¹ • kgDir d i : EuclideanSpace ℝ (Fin d))‖ *
          hillFlowSize a b G₀ T, fun r hr ξ => ?_⟩
        rw [pow_one]
        exact norm_kgDirDensity_hillDriven_le_weight a b G₀ _ hT hr ξ
      · refine ⟨0, fun r hr ξ => ?_⟩
        exact absurd (le_trans (abs_nonneg r) hr) (not_le.mpr hT)

/-- **The driven chart field has continuous partial derivatives everywhere.** -/
theorem isC1OnPi_hillDrivenChartField
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 1 < N) (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) N) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ) :
    IsC1OnPi (hillDrivenChartField a b G₀) (hillDrivenChartPartial a b G₀) Set.univ where
  isOpen := isOpen_univ
  hasDeriv := fun y _ j => hasDerivAt_hillDrivenChartField_update hN a b G₀ y j
  cont := fun j => continuous_hillDrivenChartPartial hN a b G₀ j

/-- **Hence it is differentiable, with the expected differential.** -/
theorem hasFDerivAt_hillDrivenChartField
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 1 < N) (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) N) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (y : Fin (d + 1) → ℝ) :
    HasFDerivAt (hillDrivenChartField a b G₀)
      (piToCLM fun j => hillDrivenChartPartial a b G₀ j y) y :=
  hasFDerivAt_of_isC1OnPi (d + 1) (hillDrivenChartField a b G₀) (hillDrivenChartPartial a b G₀)
    Set.univ (isC1OnPi_hillDrivenChartField hN a b G₀) y (Set.mem_univ y)

/-- **And its coordinate partials are the computed ones.** -/
theorem coordPartial_hillDrivenChartField
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 1 < N) (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) N) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (j : Fin (d + 1)) (y : Fin (d + 1) → ℝ) :
    coordPartial j (hillDrivenChartField a b G₀) y = hillDrivenChartPartial a b G₀ j y := by
  rw [coordPartial, (hasFDerivAt_hillDrivenChartField hN a b G₀ y).fderiv, piToCLM_single]

end DrivenChart

end GaloisForLFunctions.HTGeometry
