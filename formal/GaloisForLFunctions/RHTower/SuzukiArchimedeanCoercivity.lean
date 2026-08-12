import GaloisForLFunctions.RHTower.ArchimedeanGamma
import GaloisForLFunctions.RHTower.DigammaVerticalMinimum
import GaloisForLFunctions.HTGeometry.GammaProjectiveBoundary
import GaloisForLFunctions.RHTower.SuzukiL2GramRepair

/-!
# Correct archimedean coercivity in Suzuki's small-aperture argument

The archimedean spectral weight in Suzuki (2022), Eq. (4.7), is the real part of the logarithmic
connection of `Gamma_R` at `1/2 - i z`.  The printed proof later uses inconsistent factors of `1/2`.
This file fixes one exact normalization and proves its global minimum and high-frequency
coercivity unconditionally.
-/

open MeasureTheory Set Filter
open GaloisForLFunctions

noncomputable section

namespace RHTower

/-- Exact archimedean weight from Suzuki (2022), Eq. (4.7). -/
def suzukiArchimedeanWeight (z : ℝ) : ℝ :=
  (gammaRealLogConnection (((1 / 2 : ℝ) : ℂ) - Complex.I * (z : ℂ))).re

/-- Correct quarter-line digamma normalization of Suzuki's archimedean weight. -/
theorem suzukiArchimedeanWeight_eq (z : ℝ) :
    suzukiArchimedeanWeight z =
      (Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((-z / 2 : ℝ) : ℂ) * Complex.I)).re / 2 -
        Real.log Real.pi / 2 := by
  unfold suzukiArchimedeanWeight gammaRealLogConnection
  rw [show ((((1 / 2 : ℝ) : ℂ) - Complex.I * (z : ℂ)) / 2) =
      (((1 / 4 : ℝ) : ℂ) + ((-z / 2 : ℝ) : ℂ) * Complex.I) by
    push_cast
    ring]
  simp [Complex.sub_re, Complex.add_re, Complex.div_re]
  ring

/-- The real point is the global minimum of Suzuki's archimedean weight. -/
theorem suzukiArchimedeanWeight_zero_le (z : ℝ) :
    suzukiArchimedeanWeight 0 ≤ suzukiArchimedeanWeight z := by
  rw [suzukiArchimedeanWeight_eq, suzukiArchimedeanWeight_eq]
  have h := digamma_real_le_re_digamma_add_mul_I (a := (1 / 4 : ℝ)) (by norm_num)
    (-z / 2)
  have hd := div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 2)
  simpa using sub_le_sub_right hd (Real.log Real.pi / 2)

/-- Suzuki's archimedean weight is even. -/
theorem suzukiArchimedeanWeight_neg (z : ℝ) :
    suzukiArchimedeanWeight (-z) = suzukiArchimedeanWeight z := by
  rw [suzukiArchimedeanWeight_eq, suzukiArchimedeanWeight_eq]
  have h₁ := re_digamma_mono_of_abs_le (a := (1 / 4 : ℝ)) (by norm_num)
    (y := -(-z) / 2) (z := -z / 2) (by simp [abs_div, abs_neg])
  have h₂ := re_digamma_mono_of_abs_le (a := (1 / 4 : ℝ)) (by norm_num)
    (y := -z / 2) (z := -(-z) / 2) (by simp [abs_div, abs_neg])
  linarith

/-- **Corrected Suzuki Eq. (4.10), in the exact form used for coercivity.**  Every prescribed
lower bound holds uniformly outside a symmetric compact spectral band. -/
theorem exists_suzukiArchimedeanWeight_ge (C : ℝ) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ z : ℝ, T ≤ |z| → C ≤ suzukiArchimedeanWeight z := by
  have htop := GaloisForLFunctions.re_digamma_vertical_tendsto_atTop
    (σ := (1 / 4 : ℝ)) (by norm_num)
  have hev : ∀ᶠ y : ℝ in atTop,
      2 * C + Real.log Real.pi ≤
        (Complex.digamma (((1 / 4 : ℝ) : ℂ) + (y : ℂ) * Complex.I)).re :=
    (tendsto_atTop.1 htop) (2 * C + Real.log Real.pi)
  rcases (eventually_atTop.1 hev) with ⟨Y, hY⟩
  let Y₀ := max Y 0
  refine ⟨2 * Y₀, by positivity, ?_⟩
  intro z hz
  have hY₀ : 2 * C + Real.log Real.pi ≤
      (Complex.digamma (((1 / 4 : ℝ) : ℂ) + (Y₀ : ℂ) * Complex.I)).re :=
    hY Y₀ (le_max_left _ _)
  have habs : |Y₀| ≤ |-z / 2| := by
    have hYnonneg : 0 ≤ Y₀ := le_max_right _ _
    rw [abs_of_nonneg hYnonneg, abs_div, abs_neg]
    norm_num
    linarith
  have hmono := re_digamma_mono_of_abs_le (a := (1 / 4 : ℝ)) (by norm_num)
    (y := Y₀) (z := -z / 2) habs
  rw [suzukiArchimedeanWeight_eq]
  linarith

/-- **Correct global two-band lower envelope.**  This replaces the inconsistent `C₀ = max`
constant in the printed proof of Theorem 4.2.  The compact-band loss is exactly
`max 0 (C - w(0))`; outside the band the weight is at least `C`. -/
theorem exists_suzukiArchimedeanWeight_twoBand_lower (C : ℝ) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ z : ℝ,
      C - max 0 (C - suzukiArchimedeanWeight 0) *
          (Icc (-T) T).indicator (fun _ => (1 : ℝ)) z ≤
        suzukiArchimedeanWeight z := by
  rcases exists_suzukiArchimedeanWeight_ge C with ⟨T, hT, hout⟩
  refine ⟨T, hT, ?_⟩
  intro z
  by_cases hz : z ∈ Icc (-T) T
  · rw [Set.indicator_of_mem hz, mul_one]
    have hmin := suzukiArchimedeanWeight_zero_le z
    by_cases hD : 0 ≤ C - suzukiArchimedeanWeight 0
    · rw [max_eq_right hD]
      linarith
    · rw [max_eq_left (le_of_not_ge hD)]
      linarith
  · rw [Set.indicator, if_neg hz, mul_zero, sub_zero]
    apply hout z
    by_cases hleft : z < -T
    · have hzneg : z < 0 := by linarith
      rw [abs_of_neg hzneg]
      linarith
    · have hminus : -T ≤ z := le_of_not_gt hleft
      have hright : T < z := lt_of_not_ge (fun hzT => hz ⟨hminus, hzT⟩)
      have hznonneg : 0 ≤ z := by linarith
      rw [abs_of_nonneg hznonneg]
      linarith

end RHTower

end
