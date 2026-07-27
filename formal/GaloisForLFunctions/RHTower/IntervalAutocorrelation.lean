import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Shifted overlap integrals of interval indicators

For two closed intervals, the lag-`h` overlap integral of their indicators is the length of another
closed interval, cut out by the two shifted constraints.  The proof is a set identity followed by
the Lebesgue measure of an interval.

Specializing to a single interval gives the triangle profile `((d - c) - |h|)⁺`.

This is the physical-side building block for the two-edge rectangular window, whose transform is
already present in the corpus but whose autocorrelation is not.  The general two-interval form is
needed because the two-edge window is a sum of two indicators, so its autocorrelation has cross
terms between distinct intervals.
-/

open MeasureTheory Set

namespace RHTower

/-- The two constraints `x + h ∈ [c₁,d₁]` and `x ∈ [c₂,d₂]` cut out a closed interval. -/
theorem shift_inter_Icc (c₁ d₁ c₂ d₂ h : ℝ) :
    {x : ℝ | x + h ∈ Icc c₁ d₁ ∧ x ∈ Icc c₂ d₂}
      = Icc (max c₂ (c₁ - h)) (min d₂ (d₁ - h)) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Icc, max_le_iff, le_min_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨h3, by linarith⟩, h4, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by linarith, by linarith⟩, h1, h3⟩

/-- **Shifted overlap of two interval indicators.** -/
theorem integral_indicator_Icc_shift_mul_Icc (c₁ d₁ c₂ d₂ h : ℝ) :
    ∫ x : ℝ, (Icc c₁ d₁).indicator (fun _ => (1 : ℝ)) (x + h) *
        (Icc c₂ d₂).indicator (fun _ => (1 : ℝ)) x
      = max (min d₂ (d₁ - h) - max c₂ (c₁ - h)) 0 := by
  have hpt : ∀ x : ℝ,
      (Icc c₁ d₁).indicator (fun _ => (1 : ℝ)) (x + h) *
          (Icc c₂ d₂).indicator (fun _ => (1 : ℝ)) x
        = (Icc (max c₂ (c₁ - h)) (min d₂ (d₁ - h))).indicator (fun _ => (1 : ℝ)) x := by
    intro x
    have hmem : x ∈ Icc (max c₂ (c₁ - h)) (min d₂ (d₁ - h)) ↔
        (x + h ∈ Icc c₁ d₁ ∧ x ∈ Icc c₂ d₂) := by
      rw [← shift_inter_Icc c₁ d₁ c₂ d₂ h]
      exact Iff.rfl
    by_cases hx : x + h ∈ Icc c₁ d₁ ∧ x ∈ Icc c₂ d₂
    · rw [Set.indicator_of_mem hx.1, Set.indicator_of_mem hx.2,
        Set.indicator_of_mem (hmem.mpr hx)]
      norm_num
    · rw [Set.indicator_of_notMem (fun hcon => hx (hmem.mp hcon))]
      rcases not_and_or.1 hx with h1 | h1
      · rw [Set.indicator_of_notMem h1]
        ring
      · rw [Set.indicator_of_notMem h1]
        ring
  rw [funext hpt, MeasureTheory.integral_indicator_const (1 : ℝ) measurableSet_Icc,
    Real.volume_real_Icc, smul_eq_mul, mul_one]

/-- The length of the self-overlap interval is the triangle profile. -/
theorem min_sub_max_eq (c d h : ℝ) :
    min d (d - h) - max c (c - h) = (d - c) - |h| := by
  rcases le_total 0 h with hh | hh
  · rw [min_eq_right (by linarith), max_eq_left (by linarith), abs_of_nonneg hh]
    ring
  · rw [min_eq_left (by linarith), max_eq_right (by linarith), abs_of_nonpos hh]
    ring

/-- **Interval autocorrelation.**  The lag-`h` autocorrelation of the indicator of `[c,d]` is the
triangle `((d - c) - |h|)⁺`. -/
theorem integral_indicator_Icc_shift_mul (c d h : ℝ) :
    ∫ x : ℝ, (Icc c d).indicator (fun _ => (1 : ℝ)) (x + h) *
        (Icc c d).indicator (fun _ => (1 : ℝ)) x
      = max ((d - c) - |h|) 0 := by
  rw [integral_indicator_Icc_shift_mul_Icc c d c d h, min_sub_max_eq]

/-- The overlap vanishes as soon as the shifted first interval lies strictly left of the second. -/
theorem integral_indicator_Icc_shift_mul_Icc_eq_zero_of_lt
    {c₁ d₁ c₂ d₂ h : ℝ} (hsep : d₁ - h < c₂) :
    ∫ x : ℝ, (Icc c₁ d₁).indicator (fun _ => (1 : ℝ)) (x + h) *
        (Icc c₂ d₂).indicator (fun _ => (1 : ℝ)) x = 0 := by
  rw [integral_indicator_Icc_shift_mul_Icc c₁ d₁ c₂ d₂ h]
  have hle : min d₂ (d₁ - h) - max c₂ (c₁ - h) ≤ 0 := by
    have h1 : min d₂ (d₁ - h) ≤ d₁ - h := min_le_right _ _
    have h2 : c₂ ≤ max c₂ (c₁ - h) := le_max_left _ _
    linarith
  exact max_eq_right hle

/-! ## Complex-valued form, for the aperture carrier

The aperture autocorrelation used by the polar--prime carrier is complex valued and conjugates its
second argument.  Interval indicators are real, so conjugation is invisible, but the statement must
live in `ℂ` to compose. -/

/-- The pointwise product of a shifted and an unshifted interval indicator is the indicator of the
overlap interval. -/
theorem indicator_shift_mul_eq_indicator_inter_complex (c₁ d₁ c₂ d₂ h : ℝ) (x : ℝ) :
    (Icc c₁ d₁).indicator (fun _ => (1 : ℂ)) (x + h) *
        (Icc c₂ d₂).indicator (fun _ => (1 : ℂ)) x
      = (Icc (max c₂ (c₁ - h)) (min d₂ (d₁ - h))).indicator (fun _ => (1 : ℂ)) x := by
  have hmem : x ∈ Icc (max c₂ (c₁ - h)) (min d₂ (d₁ - h)) ↔
      (x + h ∈ Icc c₁ d₁ ∧ x ∈ Icc c₂ d₂) := by
    rw [← shift_inter_Icc c₁ d₁ c₂ d₂ h]
    exact Iff.rfl
  by_cases hx : x + h ∈ Icc c₁ d₁ ∧ x ∈ Icc c₂ d₂
  · rw [Set.indicator_of_mem hx.1, Set.indicator_of_mem hx.2,
      Set.indicator_of_mem (hmem.mpr hx)]
    norm_num
  · rw [Set.indicator_of_notMem (fun hcon => hx (hmem.mp hcon))]
    rcases not_and_or.1 hx with h1 | h1
    · rw [Set.indicator_of_notMem h1]
      ring
    · rw [Set.indicator_of_notMem h1]
      ring

/-- Each shifted overlap integrand is integrable: it is the indicator of a bounded interval. -/
theorem integrable_indicator_shift_mul_complex (c₁ d₁ c₂ d₂ h : ℝ) :
    Integrable (fun x : ℝ => (Icc c₁ d₁).indicator (fun _ => (1 : ℂ)) (x + h) *
        (Icc c₂ d₂).indicator (fun _ => (1 : ℂ)) x) := by
  have hfun : (fun x : ℝ => (Icc c₁ d₁).indicator (fun _ => (1 : ℂ)) (x + h) *
      (Icc c₂ d₂).indicator (fun _ => (1 : ℂ)) x)
      = (Icc (max c₂ (c₁ - h)) (min d₂ (d₁ - h))).indicator (fun _ => (1 : ℂ)) :=
    funext (indicator_shift_mul_eq_indicator_inter_complex c₁ d₁ c₂ d₂ h)
  rw [hfun]
  have hfin : (volume (Icc (max c₂ (c₁ - h)) (min d₂ (d₁ - h)))) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  exact (integrableOn_const (C := (1 : ℂ)) hfin).integrable_indicator measurableSet_Icc

/-- Shifted overlap of two interval indicators, complex-valued. -/
theorem integral_indicator_Icc_shift_mul_Icc_complex (c₁ d₁ c₂ d₂ h : ℝ) :
    ∫ x : ℝ, (Icc c₁ d₁).indicator (fun _ => (1 : ℂ)) (x + h) *
        (Icc c₂ d₂).indicator (fun _ => (1 : ℂ)) x
      = ((max (min d₂ (d₁ - h) - max c₂ (c₁ - h)) 0 : ℝ) : ℂ) := by
  rw [funext (indicator_shift_mul_eq_indicator_inter_complex c₁ d₁ c₂ d₂ h),
    MeasureTheory.integral_indicator_const (1 : ℂ) measurableSet_Icc,
    Real.volume_real_Icc, Complex.real_smul, mul_one]

/-- The complex overlap vanishes under the same separation hypothesis. -/
theorem integral_indicator_Icc_shift_mul_Icc_complex_eq_zero_of_lt
    {c₁ d₁ c₂ d₂ h : ℝ} (hsep : d₁ - h < c₂) :
    ∫ x : ℝ, (Icc c₁ d₁).indicator (fun _ => (1 : ℂ)) (x + h) *
        (Icc c₂ d₂).indicator (fun _ => (1 : ℂ)) x = 0 := by
  rw [integral_indicator_Icc_shift_mul_Icc_complex c₁ d₁ c₂ d₂ h]
  have hle : min d₂ (d₁ - h) - max c₂ (c₁ - h) ≤ 0 := by
    have h1 : min d₂ (d₁ - h) ≤ d₁ - h := min_le_right _ _
    have h2 : c₂ ≤ max c₂ (c₁ - h) := le_max_left _ _
    linarith
  rw [max_eq_right hle]
  norm_num

end RHTower
