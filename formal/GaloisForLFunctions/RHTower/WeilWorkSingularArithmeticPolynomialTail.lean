import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticPolynomialProfile

/-!
# Absolute tails of the actual polynomial Gaussian profiles

The alternating tail is controlled through the actual half-scale series.
This supplies absolute tail control independently of the signed upper bound.
-/

open Complex MeasureTheory Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic

open GaussZeroSum

theorem exists_norm_sourceAlternatingGaussianProfile_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, 0 < t →
      ‖sourceAlternatingGaussianProfile lam t‖ ≤ D / t := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_source_twisted_gaussW_le hW
    (r := 1 / 2) (by norm_num)
  refine ⟨C * Real.pi, by positivity, fun t ht => ?_⟩
  have h := (hC (Real.sqrt (Real.pi / t))
    (Real.sqrt_pos.mpr (by positivity))).2
  have hg (n : ℕ) : gaussW (Real.sqrt (Real.pi / t)) ((n : ℝ) / 2) =
      Real.exp (-Real.pi * (n : ℝ) ^ 2 * t) := by
    rw [gaussW, Real.sq_sqrt (by positivity)]
    congr 1
    field_simp
    ring
  rw [source_twisted_gaussW_half_eq, Real.sq_sqrt (by positivity)] at h
  simp_rw [hg] at h
  simpa only [sourceAlternatingGaussianProfile, mul_div_assoc] using h

/-- The signed polynomial profile also has a genuine absolute tail bound. -/
theorem exists_norm_sourceTwoPointGaussianProfile_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (c : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, 0 < t →
      ‖sourceTwoPointGaussianProfile lam c t‖ ≤ D / t := by
  obtain ⟨D, hD0, hD⟩ := exists_norm_sourceGaussianProfile_le hW
  obtain ⟨E, hE0, hE⟩ := exists_norm_sourceAlternatingGaussianProfile_le hW
  let A : ℂ := 1 + (c : ℂ) ^ 2 / 2
  refine ⟨‖A‖ * D + ‖(c : ℂ) / 2‖ * E * 4 + ‖(c : ℂ)‖ * D / 4,
    by positivity, fun t ht => ?_⟩
  have h1 := hD t ht
  have h2 := hE (t / 4) (by positivity)
  have h3 := hD (4 * t) (by positivity)
  change ‖A * sourceGaussianProfile lam t -
    ((c : ℂ) / 2) * sourceAlternatingGaussianProfile lam (t / 4) -
    (c : ℂ) * sourceGaussianProfile lam (4 * t)‖ ≤ _
  calc
    _ ≤ ‖A * sourceGaussianProfile lam t -
        ((c : ℂ) / 2) * sourceAlternatingGaussianProfile lam (t / 4)‖ +
        ‖(c : ℂ) * sourceGaussianProfile lam (4 * t)‖ := norm_sub_le _ _
    _ ≤ (‖A * sourceGaussianProfile lam t‖ +
        ‖((c : ℂ) / 2) * sourceAlternatingGaussianProfile lam (t / 4)‖) +
        ‖(c : ℂ) * sourceGaussianProfile lam (4 * t)‖ := by
      gcongr
      exact norm_sub_le _ _
    _ = ‖A‖ * ‖sourceGaussianProfile lam t‖ +
        ‖(c : ℂ) / 2‖ * ‖sourceAlternatingGaussianProfile lam (t / 4)‖ +
        ‖(c : ℂ)‖ * ‖sourceGaussianProfile lam (4 * t)‖ := by simp only [norm_mul]
    _ ≤ ‖A‖ * (D / t) + ‖(c : ℂ) / 2‖ * (E / (t / 4)) +
        ‖(c : ℂ)‖ * (D / (4 * t)) := by gcongr
    _ = _ := by ring

end RHTower.WeilSingularArithmetic
