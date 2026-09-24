import Mathlib.Probability.Moments.ComplexMGF

open Complex MeasureTheory Set Filter Topology ProbabilityTheory

namespace RHTower

theorem positiveMGF_boundary_residue_norm_le
    (μ : Measure ℝ) (z0 : ℂ) (hz0re : z0.re = 0)
    (B : ℝ) (c : ℂ)
    (hreal : Tendsto (fun σ : ℝ => σ * mgf id μ (1 - σ))
      (𝓝[>] (0 : ℝ)) (𝓝 B))
    (himag : Tendsto (fun σ : ℝ =>
      (σ : ℂ) * complexMGF id μ ((1 : ℂ) - ((σ : ℂ) + z0)))
      (𝓝[>] (0 : ℝ)) (𝓝 c)) :
    ‖c‖ ≤ B := by
  have hle : ∀ᶠ σ : ℝ in 𝓝[>] (0 : ℝ),
      ‖(σ : ℂ) * complexMGF id μ ((1 : ℂ) - ((σ : ℂ) + z0))‖ ≤
        σ * mgf id μ (1 - σ) := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ]
    have hbound := norm_complexMGF_le_mgf (X := id) (μ := μ)
      (z := (1 : ℂ) - ((σ : ℂ) + z0))
    have hre : ((1 : ℂ) - ((σ : ℂ) + z0)).re = 1 - σ := by
      simp only [Complex.sub_re, Complex.one_re, Complex.add_re,
        Complex.ofReal_re, hz0re]
      ring
    rw [hre] at hbound
    exact mul_le_mul_of_nonneg_left hbound hσ.le
  exact le_of_tendsto_of_tendsto himag.norm hreal hle

end RHTower
