import Mathlib

/-!
# Radial L² convergence of Hardy `H²` functions

For a square-summable coefficient sequence `(aₙ)`, the Parseval defect between the radial
dilate `∑ aₙ rⁿ e^{inθ}` and the boundary function `∑ aₙ e^{inθ}` equals
`∑ₙ |aₙ|² (1 - rⁿ)²`, which tends to `0` as `r → 1⁻`.  This is the analytic core of the statement
that an `H²` function has `L²` boundary values (via dominated convergence), an input of the Riesz
factorization behind the F.&M. Riesz theorem.
-/

open Filter Topology Set

namespace GaloisForLFunctions.HTGeometry

/-- **Radial `H²` Parseval defect vanishes at the boundary.**  For a summable nonnegative sequence
`b` (the squared moduli of the coefficients), `∑ₙ bₙ (1 - rⁿ)² → 0` as `r → 1⁻`. -/
theorem tendsto_abel_l2_defect {b : ℕ → ℝ} (hb : Summable b) (hbnn : ∀ n, 0 ≤ b n) :
    Tendsto (fun r : ℝ => ∑' n : ℕ, b n * (1 - r ^ n) ^ (2 : ℕ)) (𝓝[<] 1) (𝓝 0) := by
  have hzero : (0 : ℝ) = ∑' _n : ℕ, (0 : ℝ) := by simp
  rw [hzero]
  apply tendsto_tsum_of_dominated_convergence hb
  · intro n
    have hc : Continuous (fun r : ℝ => b n * (1 - r ^ n) ^ (2 : ℕ)) := by fun_prop
    have ht := hc.tendsto 1
    simp only [one_pow, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero] at ht
    exact ht.mono_left nhdsWithin_le_nhds
  · have hmem : Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := by
      rw [← Ioi_inter_Iio]
      exact inter_mem (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num)))
        self_mem_nhdsWithin
    filter_upwards [hmem] with r hr n
    rw [Set.mem_Ioo] at hr
    obtain ⟨hr0, hr1⟩ := hr
    have hrn : r ^ n ∈ Icc (0 : ℝ) 1 := ⟨by positivity, pow_le_one₀ hr0.le hr1.le⟩
    have hsq : (1 - r ^ n) ^ (2 : ℕ) ≤ 1 := by nlinarith [hrn.1, hrn.2]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hbnn n) (sq_nonneg _))]
    calc b n * (1 - r ^ n) ^ (2 : ℕ) ≤ b n * 1 := mul_le_mul_of_nonneg_left hsq (hbnn n)
      _ = b n := mul_one _

end GaloisForLFunctions.HTGeometry
