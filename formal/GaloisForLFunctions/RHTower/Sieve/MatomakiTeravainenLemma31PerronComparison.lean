import GaloisForLFunctions.RHTower.Sieve.PerronWindowKernel
import GaloisForLFunctions.RHTower.Sieve.PerronCompareLowFreq

/-!
# Exact two-window Perron comparison for Matomäki--Teräväinen Lemma 3.1

The arithmetic difference between a short interval and its normalized long reference interval is
written as one integral against `perronCompareKernel`, with all four truncated-Perron endpoint
errors retained explicitly.
-/

namespace RHTower.Sieve

open Complex MeasureTheory

noncomputable section

/-- Coefficient sum on the natural window `(A, A + H]`, truncated at `M`. -/
def perronWindowSum (c : ℕ → ℂ) (M A H : ℕ) : ℂ :=
  (∑ n ∈ Finset.Icc 1 (min M (A + H)), c n) -
    ∑ n ∈ Finset.Icc 1 (min M A), c n

/-- The two endpoint kernels are exactly the positive-real Perron window kernel based at
`A + 1/2`. -/
theorem perronPrefixKernel_window_eq (A H : ℕ) (t : ℝ) :
    perronPrefixKernel (A + H) 1 t - perronPrefixKernel A 1 t =
      ((((((A : ℝ) + 1 / 2) + H : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℝ) * I) -
          ((((A : ℝ) + 1 / 2 : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℝ) * I))) /
        ((1 : ℂ) + (t : ℝ) * I)) := by
  simp only [perronPrefixKernel]
  rw [← sub_div]
  congr 2
  push_cast
  ring_nf

/-- The normalized difference of two prefix-integral windows is one integral against the literal
comparison kernel. -/
theorem perronPrefixIntegral_window_compare_eq
    (c : ℕ → ℂ) (M A H H₁ : ℕ) (T : ℝ) :
    (perronPrefixIntegral c M (A + H) 1 T - perronPrefixIntegral c M A 1 T) -
        (((H : ℝ) / H₁ : ℝ) : ℂ) *
          (perronPrefixIntegral c M (A + H₁) 1 T - perronPrefixIntegral c M A 1 T) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
        perronPoly c M 1 t *
          perronCompareKernel ((A : ℝ) + 1 / 2) H H₁ t := by
  rw [perronPrefixIntegral_sub c M A (A + H) (by norm_num : (0 : ℝ) < 1) T,
    perronPrefixIntegral_sub c M A (A + H₁) (by norm_num : (0 : ℝ) < 1) T]
  have hshort : Continuous fun t : ℝ =>
      perronPoly c M 1 t *
        (perronPrefixKernel (A + H) 1 t - perronPrefixKernel A 1 t) :=
    (continuous_perronPoly c M 1).mul
      ((continuous_perronPrefixKernel (A + H) (by norm_num)).sub
        (continuous_perronPrefixKernel A (by norm_num)))
  have hlong : Continuous fun t : ℝ =>
      (((H : ℝ) / H₁ : ℝ) : ℂ) *
        (perronPoly c M 1 t *
          (perronPrefixKernel (A + H₁) 1 t - perronPrefixKernel A 1 t)) :=
    continuous_const.mul ((continuous_perronPoly c M 1).mul
      ((continuous_perronPrefixKernel (A + H₁) (by norm_num)).sub
        (continuous_perronPrefixKernel A (by norm_num))))
  have hfactor :
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t in (-T)..T, perronPoly c M 1 t *
            (perronPrefixKernel (A + H) 1 t - perronPrefixKernel A 1 t)) -
        (((H : ℝ) / H₁ : ℝ) : ℂ) *
          (((1 / (2 * Real.pi) : ℝ) : ℂ) *
            (∫ t in (-T)..T, perronPoly c M 1 t *
              (perronPrefixKernel (A + H₁) 1 t - perronPrefixKernel A 1 t))) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ((∫ t in (-T)..T, perronPoly c M 1 t *
            (perronPrefixKernel (A + H) 1 t - perronPrefixKernel A 1 t)) -
          (((H : ℝ) / H₁ : ℝ) : ℂ) *
            (∫ t in (-T)..T, perronPoly c M 1 t *
              (perronPrefixKernel (A + H₁) 1 t - perronPrefixKernel A 1 t))) := by
    ring
  rw [hfactor]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_sub (μ := volume)
    (hshort.intervalIntegrable _ _) (hlong.intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr ?_
  intro t _
  change perronPoly c M 1 t *
        (perronPrefixKernel (A + H) 1 t - perronPrefixKernel A 1 t) -
      (((H : ℝ) / H₁ : ℝ) : ℂ) *
        (perronPoly c M 1 t *
          (perronPrefixKernel (A + H₁) 1 t - perronPrefixKernel A 1 t)) =
    perronPoly c M 1 t * perronCompareKernel ((A : ℝ) + 1 / 2) H H₁ t
  rw [perronPrefixKernel_window_eq A H t, perronPrefixKernel_window_eq A H₁ t]
  simp only [perronCompareKernel]
  push_cast
  ring

/-- **Pointwise Perron reduction in Lemma 3.1.** The exact normalized short/long arithmetic
window difference differs from the comparison-kernel integral by no more than the four explicit
near-diagonal endpoint errors. -/
theorem norm_perronWindowSum_compare_sub_integral_le
    {c : ℕ → ℂ} {M A H H₁ : ℕ} {K T : ℝ}
    (hK : ∀ n, ‖c n‖ ≤ K) (hT : 0 < T) :
    ‖perronWindowSum c M A H - (((H : ℝ) / H₁ : ℝ) : ℂ) * perronWindowSum c M A H₁ -
        ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
          perronPoly c M 1 t * perronCompareKernel ((A : ℝ) + 1 / 2) H H₁ t‖ ≤
      perronNearError K M (A + H) 1 T + perronNearError K M A 1 T +
        ((H : ℝ) / H₁) *
          (perronNearError K M (A + H₁) 1 T + perronNearError K M A 1 T) := by
  have hshort := norm_sum_Icc_sub_sum_Icc_sub_perronInterval_le
    (c := c) (M := M) (A := A) (B := A + H) hK (by norm_num : (1 : ℝ) ≤ 1) hT
  have hlong := norm_sum_Icc_sub_sum_Icc_sub_perronInterval_le
    (c := c) (M := M) (A := A) (B := A + H₁) hK (by norm_num : (1 : ℝ) ≤ 1) hT
  have hratio : 0 ≤ (H : ℝ) / H₁ := div_nonneg (Nat.cast_nonneg H) (Nat.cast_nonneg H₁)
  have hscale :
      ‖(((H : ℝ) / H₁ : ℝ) : ℂ) *
          (perronWindowSum c M A H₁ -
            (perronPrefixIntegral c M (A + H₁) 1 T - perronPrefixIntegral c M A 1 T))‖ ≤
        ((H : ℝ) / H₁) *
          (perronNearError K M (A + H₁) 1 T + perronNearError K M A 1 T) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hratio]
    exact mul_le_mul_of_nonneg_left (by simpa only [perronWindowSum] using hlong) hratio
  rw [← perronPrefixIntegral_window_compare_eq c M A H H₁ T]
  have hid :
      perronWindowSum c M A H - (((H : ℝ) / H₁ : ℝ) : ℂ) * perronWindowSum c M A H₁ -
          ((perronPrefixIntegral c M (A + H) 1 T - perronPrefixIntegral c M A 1 T) -
            (((H : ℝ) / H₁ : ℝ) : ℂ) *
              (perronPrefixIntegral c M (A + H₁) 1 T - perronPrefixIntegral c M A 1 T)) =
        (perronWindowSum c M A H -
          (perronPrefixIntegral c M (A + H) 1 T - perronPrefixIntegral c M A 1 T)) -
          (((H : ℝ) / H₁ : ℝ) : ℂ) *
            (perronWindowSum c M A H₁ -
              (perronPrefixIntegral c M (A + H₁) 1 T - perronPrefixIntegral c M A 1 T)) := by
    ring
  rw [hid]
  exact (norm_sub_le _ _).trans (add_le_add (by simpa only [perronWindowSum] using hshort) hscale)

end

end RHTower.Sieve
