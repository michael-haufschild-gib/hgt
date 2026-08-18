import GaloisForLFunctions.RHTower.Sieve.PerronKernelBound

/-!
# The two-window Perron comparison kernel
-/

namespace RHTower.Sieve

open Complex

noncomputable section

/-- The kernel of the short/long window comparison: the short-window Perron kernel minus the long
one, renormalised so that the two agree to leading order.  This is the object integrated in
Matomäki--Teräväinen's Lemma 3.1 and in the window comparison of their Section 7. -/
def perronCompareKernel (x h h₁ t : ℝ) : ℂ :=
  ((((x + h : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℝ) * Complex.I)
      - ((x : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℝ) * Complex.I))
    / ((1 : ℂ) + (t : ℝ) * Complex.I))
  - ((h / h₁ : ℝ) : ℂ)
    * ((((x + h₁ : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℝ) * Complex.I)
        - ((x : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℝ) * Complex.I))
      / ((1 : ℂ) + (t : ℝ) * Complex.I))

/-- **The comparison kernel is bounded by twice the short window.** -/
theorem norm_perronCompareKernel_le_length {x h h₁ : ℝ} (hx : 0 < x) (hh : 0 < h) (hh₁ : 0 < h₁)
    (t : ℝ) : ‖perronCompareKernel x h h₁ t‖ ≤ 2 * h := by
  have hA := norm_perron_kernel_le_length hx hh t
  have hB := norm_perron_kernel_le_length hx hh₁ t
  have hc : ‖((h / h₁ : ℝ) : ℂ)‖ = h / h₁ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hprod : ‖((h / h₁ : ℝ) : ℂ)
      * ((((x + h₁ : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℝ) * Complex.I)
          - ((x : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℝ) * Complex.I))
        / ((1 : ℂ) + (t : ℝ) * Complex.I))‖ ≤ h := by
    rw [norm_mul, hc]
    have hval : h / h₁ * h₁ = h := by field_simp
    calc h / h₁ * ‖(_ : ℂ)‖ ≤ h / h₁ * h₁ :=
          mul_le_mul_of_nonneg_left hB (by positivity)
      _ = h := hval
  rw [perronCompareKernel]
  refine le_trans (norm_sub_le _ _) ?_
  linarith [hA, hprod]

/-- **The comparison kernel decays like `1/|t|`.** -/
theorem norm_perronCompareKernel_le_div {x h h₁ t : ℝ} (hx : 0 < x) (hh : 0 < h) (hh₁ : 0 < h₁)
    (hle : h ≤ h₁) (ht : t ≠ 0) :
    ‖perronCompareKernel x h h₁ t‖ ≤ 4 * (x + h₁) / |t| := by
  have habs : (0 : ℝ) < |t| := abs_pos.2 ht
  have hA := norm_perron_kernel_le_div hx hh ht
  have hB := norm_perron_kernel_le_div hx hh₁ ht
  have hc : ‖((h / h₁ : ℝ) : ℂ)‖ = h / h₁ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hcle : h / h₁ ≤ 1 := by
    rw [div_le_one hh₁]
    exact hle
  have hprod : ‖((h / h₁ : ℝ) : ℂ)
      * ((((x + h₁ : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℝ) * Complex.I)
          - ((x : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℝ) * Complex.I))
        / ((1 : ℂ) + (t : ℝ) * Complex.I))‖ ≤ 2 * (x + h₁) / |t| := by
    rw [norm_mul, hc]
    have hpos : (0 : ℝ) ≤ 2 * (x + h₁) / |t| := by positivity
    calc h / h₁ * ‖(_ : ℂ)‖ ≤ 1 * (2 * (x + h₁) / |t|) :=
          mul_le_mul hcle hB (norm_nonneg _) (by norm_num)
      _ = 2 * (x + h₁) / |t| := by ring
  have hAle : 2 * (x + h) / |t| ≤ 2 * (x + h₁) / |t| := by
    refine div_le_div_of_nonneg_right ?_ habs.le
    linarith
  rw [perronCompareKernel]
  refine le_trans (norm_sub_le _ _) ?_
  have : (4 : ℝ) * (x + h₁) / |t| = 2 * (x + h₁) / |t| + 2 * (x + h₁) / |t| := by ring
  linarith [hA, hAle, hprod, this]

/-- **The comparison kernel, both branches.** -/
theorem norm_perronCompareKernel_le_min {x h h₁ t : ℝ} (hx : 0 < x) (hh : 0 < h) (hh₁ : 0 < h₁)
    (hle : h ≤ h₁) (ht : t ≠ 0) :
    ‖perronCompareKernel x h h₁ t‖ ≤ min (2 * h) (4 * (x + h₁) / |t|) :=
  le_min (norm_perronCompareKernel_le_length hx hh hh₁ t)
    (norm_perronCompareKernel_le_div hx hh hh₁ hle ht)

end

end RHTower.Sieve
