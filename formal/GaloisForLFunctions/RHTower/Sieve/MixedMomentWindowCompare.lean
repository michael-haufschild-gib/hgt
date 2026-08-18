import GaloisForLFunctions.RHTower.Sieve.MixedMomentAssembly
import GaloisForLFunctions.RHTower.Sieve.PerronCompareLowFreq

/-!
# The mixed first moment against the window-comparison kernel

The difference of two truncated Perron kernels, for windows of lengths `h ≤ h₁` at the same left
endpoint `x`, obeys the three-branch bound
`min (min (2h) (2|t|hh₁/x)) (4(x+h₁)/|t|)`.  Its low-frequency branch vanishes linearly at `t = 0`,
so the comparison sees nothing below height `x/h₁`; this replaces the main-term subtraction that the
single-window Perron kernel `min(x/t, h)` requires.

The mixed first moment of two Dirichlet polynomials against this weight is bounded here in both
ranges: below the truncation height the kernel is a constant `2hδ`, and above it the kernel decays
like `4(x+h₁)/t`, which is the hypothesis of the dyadic assembly.
-/

namespace RHTower.Sieve

open MeasureTheory

noncomputable section

/-- The window-comparison kernel `min(2h, 2|t|hh₁/x, 4(x+h₁)/|t|)`, with the denominator of the
decaying branch floored at `t₀` so as to be globally continuous.  For `|t| ≥ t₀` it agrees with the
three-branch majorant of `perronCompareKernel`. -/
def windowCompareKernel (x h h₁ t₀ : ℝ) : ℝ → ℝ := fun t =>
  min (min (2 * h) (2 * |t| * h * h₁ / x)) (4 * (x + h₁) / max |t| t₀)

theorem continuous_windowCompareKernel {x h h₁ t₀ : ℝ} (ht₀ : 0 < t₀) :
    Continuous (windowCompareKernel x h h₁ t₀) := by
  have habs : Continuous fun t : ℝ => |t| := continuous_abs
  have hden : Continuous fun t : ℝ => max |t| t₀ := habs.max continuous_const
  have hne : ∀ t : ℝ, max |t| t₀ ≠ 0 := fun t =>
    ne_of_gt (lt_of_lt_of_le ht₀ (le_max_right _ _))
  have h1 : Continuous fun t : ℝ => 2 * |t| * h * h₁ / x :=
    (((continuous_const.mul habs).mul continuous_const).mul continuous_const).div_const x
  exact (continuous_const.min h1).min (continuous_const.div hden hne)

theorem windowCompareKernel_nonneg {x h h₁ t₀ : ℝ} (hx : 0 < x) (hh : 0 ≤ h) (hh₁ : 0 ≤ h₁)
    (ht₀ : 0 < t₀) (t : ℝ) : 0 ≤ windowCompareKernel x h h₁ t₀ t := by
  have hden : (0 : ℝ) < max |t| t₀ := lt_of_lt_of_le ht₀ (le_max_right _ _)
  simp only [windowCompareKernel]
  refine le_min (le_min (by linarith) ?_) (div_nonneg (by linarith) hden.le)
  exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg t)) hh) hh₁) hx.le

/-- Above the truncation height the kernel decays like `4(x+h₁)/t`. -/
theorem windowCompareKernel_le_div {x h h₁ t₀ t : ℝ} (ht₀ : 0 < t₀) (ht : t₀ ≤ t) :
    windowCompareKernel x h h₁ t₀ t ≤ 4 * (x + h₁) / t := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le ht₀ ht
  have hmax : max |t| t₀ = t := by
    rw [abs_of_pos ht0]
    exact max_eq_left ht
  simp only [windowCompareKernel, hmax]
  exact min_le_right _ _

/-- The kernel majorizes the Perron window difference above the truncation height. -/
theorem norm_perronCompareKernel_le_windowCompareKernel {x h h₁ t₀ t : ℝ} (hx : 0 < x) (hh : 0 < h)
    (hh₁ : 0 < h₁) (hle : h ≤ h₁) (ht₀ : 0 < t₀) (ht : t₀ ≤ |t|) :
    ‖perronCompareKernel x h h₁ t‖ ≤ windowCompareKernel x h h₁ t₀ t := by
  have htne : t ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at ht
    linarith
  have hmax : max |t| t₀ = |t| := max_eq_left ht
  simp only [windowCompareKernel, hmax]
  exact norm_perronCompareKernel_le_min3 hx hh hh₁ hle htne

/-- **The comparison sees nothing below height `x/h₁`.** -/
theorem windowCompareKernel_le_of_low {x h h₁ t₀ δ t : ℝ} (hx : 0 < x) (hh : 0 ≤ h)
    (hh₁ : 0 < h₁) (hlow : |t| ≤ δ * x / h₁) :
    windowCompareKernel x h h₁ t₀ t ≤ 2 * h * δ := by
  refine le_trans (min_le_left _ _) (le_trans (min_le_right _ _) ?_)
  rw [div_le_iff₀ hx]
  have h1 : |t| * h₁ ≤ δ * x := by
    rw [le_div_iff₀ hh₁] at hlow
    linarith
  nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 2 * h)]

/-- **The low-frequency range.**  Below the truncation height the whole mixed moment is carried by
the constant `2hδ`, where `δ = t₀h₁/x`; both mean-square majorants enter only through their values
at `t₀`. -/
theorem integral_lowRange_windowCompare_le {A B : ℝ → ℂ} (hA : Continuous A) (hB : Continuous B)
    {QA κA QB κB x h h₁ t₀ δ : ℝ} (hQA : 0 ≤ QA) (hκA : 0 ≤ κA) (hQB : 0 ≤ QB) (hκB : 0 ≤ κB)
    (hx : 0 < x) (hh : 0 ≤ h) (hh₁ : 0 < h₁) (ht₀ : 0 < t₀) (hδ : 0 ≤ δ)
    (hlow : t₀ ≤ δ * x / h₁)
    (hmsA : (∫ t in Set.Icc (-t₀) t₀, ‖A t‖ ^ 2) ≤ QA + κA * t₀)
    (hmsB : (∫ t in Set.Icc (-t₀) t₀, ‖B t‖ ^ 2) ≤ QB + κB * t₀) :
    (∫ t in (0 : ℝ)..t₀, (‖A t‖ * ‖B t‖) * windowCompareKernel x h h₁ t₀ t)
      ≤ 2 * h * δ * (Real.sqrt QA * Real.sqrt QB
          + (Real.sqrt QA * Real.sqrt κB + Real.sqrt κA * Real.sqrt QB) * Real.sqrt t₀
          + Real.sqrt κA * Real.sqrt κB * t₀) := by
  have hF : Continuous fun t : ℝ => ‖A t‖ * ‖B t‖ := hA.norm.mul hB.norm
  have hK : ∀ t ∈ Set.Icc (0 : ℝ) t₀,
      (‖A t‖ * ‖B t‖) * windowCompareKernel x h h₁ t₀ t ≤ (‖A t‖ * ‖B t‖) * (2 * h * δ) := by
    intro t ht
    have habs : |t| ≤ δ * x / h₁ := by
      rw [abs_of_nonneg ht.1]
      exact le_trans ht.2 hlow
    exact mul_le_mul_of_nonneg_left (windowCompareKernel_le_of_low hx hh hh₁ habs)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hmono := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun t : ℝ => ‖A t‖ * ‖B t‖ * windowCompareKernel x h h₁ t₀ t)
    (g := fun t : ℝ => ‖A t‖ * ‖B t‖ * (2 * h * δ)) ht₀.le
    ((hF.mul (continuous_windowCompareKernel ht₀)).intervalIntegrable _ _)
    ((hF.mul continuous_const).intervalIntegrable _ _) hK
  rw [intervalIntegral.integral_mul_const] at hmono
  have hcs := GaloisForLFunctions.HTGeometry.integral_norm_mul_norm_le_general_affine (A := A) (B := B) hA hB hQA hκA hQB hκB
    hmsA hmsB le_rfl ht₀.le ht₀
  have hpos : (0 : ℝ) ≤ 2 * h * δ := by positivity
  have hstep := mul_le_mul_of_nonneg_right hcs hpos
  linarith [hmono, hstep]

/-- **The dyadic range.**  Above the truncation height the comparison kernel obeys the hypothesis of
the mixed-moment assembly with `C = 4(x+h₁)`. -/
theorem integral_dyadicRange_windowCompare_le {A B : ℝ → ℂ} (hA : Continuous A) (hB : Continuous B)
    {QA κA QB κB x h h₁ t₀ : ℝ} (hQA : 0 ≤ QA) (hκA : 0 ≤ κA) (hQB : 0 ≤ QB) (hκB : 0 ≤ κB)
    (hx : 0 < x) (hh₁ : 0 ≤ h₁) (ht₀ : 0 < t₀)
    (hmsA : ∀ U : ℝ, t₀ ≤ U → (∫ t in Set.Icc (-U) U, ‖A t‖ ^ 2) ≤ QA + κA * U)
    (hmsB : ∀ U : ℝ, t₀ ≤ U → (∫ t in Set.Icc (-U) U, ‖B t‖ ^ 2) ≤ QB + κB * U) (M : ℕ) :
    (∫ t in t₀..(t₀ * 2 ^ M), (‖A t‖ * ‖B t‖) * windowCompareKernel x h h₁ t₀ t)
      ≤ 2 * (4 * (x + h₁) * (Real.sqrt QA * Real.sqrt QB) / t₀)
          + (4 * (x + h₁) * (Real.sqrt QA * Real.sqrt κB + Real.sqrt κA * Real.sqrt QB)
              * Real.sqrt 2 / Real.sqrt t₀) * (1 - Real.sqrt 2 / 2)⁻¹
          + 2 * (4 * (x + h₁)) * (Real.sqrt κA * Real.sqrt κB) * M :=
  GaloisForLFunctions.HTGeometry.integral_norm_mul_norm_mul_kernel_le hA hB
    (continuous_windowCompareKernel (x := x) (h := h) (h₁ := h₁) ht₀) hQA hκA hQB hκB
    (by linarith : (0 : ℝ) ≤ 4 * (x + h₁)) ht₀ hmsA hmsB M
    (fun _ ht _ => windowCompareKernel_le_div ht₀ ht)

/-- **The complete mixed first moment against the window-comparison kernel.**  The low-frequency
range contributes only `2hδ` times the Cauchy–Schwarz product of the two mean-square majorants at
the truncation height; the dyadic range contributes the assembly's `√height` term and a term linear
in the number of blocks. -/
theorem integral_mixed_moment_windowCompare_le {A B : ℝ → ℂ} (hA : Continuous A)
    (hB : Continuous B) {QA κA QB κB x h h₁ t₀ δ : ℝ} (hQA : 0 ≤ QA) (hκA : 0 ≤ κA)
    (hQB : 0 ≤ QB) (hκB : 0 ≤ κB) (hx : 0 < x) (hh : 0 ≤ h) (hh₁ : 0 < h₁) (ht₀ : 0 < t₀)
    (hδ : 0 ≤ δ) (hlow : t₀ ≤ δ * x / h₁)
    (hmsA : ∀ U : ℝ, t₀ ≤ U → (∫ t in Set.Icc (-U) U, ‖A t‖ ^ 2) ≤ QA + κA * U)
    (hmsB : ∀ U : ℝ, t₀ ≤ U → (∫ t in Set.Icc (-U) U, ‖B t‖ ^ 2) ≤ QB + κB * U) (M : ℕ) :
    (∫ t in (0 : ℝ)..(t₀ * 2 ^ M), (‖A t‖ * ‖B t‖) * windowCompareKernel x h h₁ t₀ t)
      ≤ 2 * h * δ * (Real.sqrt QA * Real.sqrt QB
            + (Real.sqrt QA * Real.sqrt κB + Real.sqrt κA * Real.sqrt QB) * Real.sqrt t₀
            + Real.sqrt κA * Real.sqrt κB * t₀)
        + (2 * (4 * (x + h₁) * (Real.sqrt QA * Real.sqrt QB) / t₀)
          + (4 * (x + h₁) * (Real.sqrt QA * Real.sqrt κB + Real.sqrt κA * Real.sqrt QB)
              * Real.sqrt 2 / Real.sqrt t₀) * (1 - Real.sqrt 2 / 2)⁻¹
          + 2 * (4 * (x + h₁)) * (Real.sqrt κA * Real.sqrt κB) * M) := by
  have hF : Continuous fun t : ℝ =>
      (‖A t‖ * ‖B t‖) * windowCompareKernel x h h₁ t₀ t :=
    (hA.norm.mul hB.norm).mul (continuous_windowCompareKernel ht₀)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (f := fun t : ℝ => (‖A t‖ * ‖B t‖) * windowCompareKernel x h h₁ t₀ t)
    (μ := volume) (a := 0) (b := t₀) (c := t₀ * 2 ^ M)
    (hF.intervalIntegrable _ _) (hF.intervalIntegrable _ _)
  have hlowr := integral_lowRange_windowCompare_le hA hB hQA hκA hQB hκB hx hh hh₁ ht₀ hδ hlow
    (hmsA t₀ le_rfl) (hmsB t₀ le_rfl)
  have hhigh := integral_dyadicRange_windowCompare_le hA hB hQA hκA hQB hκB hx hh₁.le ht₀
    (h := h) hmsA hmsB M
  linarith [hsplit, hlowr, hhigh]

end

end RHTower.Sieve
