import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticPolynomialGaussian
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticGaussianProfile

/-!
# The corrected polynomial profile in Mellin normalization

The half-scale term is the parity-twisted actual source. Full positivity
alone controls the signed combination, despite its negative coefficients.
-/

open Complex MeasureTheory Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic

open GaussZeroSum

def sourceAlternatingGaussianProfile (lam : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, sourceSquareCoeff lam n *
    ((Real.exp (-Real.pi * (n : ℝ) ^ 2 * t) * (-1) ^ n : ℝ) : ℂ)

def sourceTwoPointGaussianProfile (lam : ℕ → ℝ) (c t : ℝ) : ℂ :=
  (1 + (c : ℂ) ^ 2 / 2) * sourceGaussianProfile lam t -
    ((c : ℂ) / 2) * sourceAlternatingGaussianProfile lam (t / 4) -
    (c : ℂ) * sourceGaussianProfile lam (4 * t)

theorem hasSum_sourceAlternatingGaussianProfile {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => sourceSquareCoeff lam n *
      ((Real.exp (-Real.pi * (n : ℝ) ^ 2 * t) * (-1) ^ n : ℝ) : ℂ))
      (sourceAlternatingGaussianProfile lam t) := by
  have hs := (hasSum_sourceGaussianProfile hW ht).summable.norm
  have hf : Summable (fun n : ℕ => sourceSquareCoeff lam n *
      ((Real.exp (-Real.pi * (n : ℝ) ^ 2 * t) * (-1) ^ n : ℝ) : ℂ)) := by
    refine Summable.of_norm_bounded hs fun n => ?_
    simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg,
      Complex.ofReal_one, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one, le_refl]
  exact hf.hasSum

private theorem gaussW_polynomial_mellin_scale {t : ℝ} (ht : 0 < t) (y : ℝ) :
    gaussW (Real.sqrt (4 * Real.pi / t)) y = Real.exp (-Real.pi * y ^ 2 * t) := by
  rw [gaussW, Real.sq_sqrt (by positivity)]
  congr 1
  field_simp

theorem sourceTwoPointGaussianSum_mellin_scale (lam : ℕ → ℝ) (c : ℝ)
    {t : ℝ} (ht : 0 < t) :
    sourceTwoPointGaussianSum lam c (Real.sqrt (4 * Real.pi / t)) =
      sourceTwoPointGaussianProfile lam c t := by
  have hc (n : ℕ) : Real.cos (2 * Real.pi * (n : ℝ)) = 1 := by
    rw [mul_comm (2 * Real.pi)]
    exact Real.cos_nat_mul_two_pi n
  have hc2 (n : ℕ) : Real.cos (2 * Real.pi * ((n : ℝ) * 2)) = 1 := by
    have he : (n : ℝ) * 2 = ((n * 2 : ℕ) : ℝ) := by push_cast; ring
    rw [he]
    exact hc (n * 2)
  have h1 : sourceTwistedGaussianSum lam (Real.sqrt (4 * Real.pi / t)) 1 =
      sourceGaussianProfile lam t := by
    unfold sourceTwistedGaussianSum sourceGaussianProfile
    simp_rw [mul_one, gaussW_polynomial_mellin_scale ht, hc, mul_one]
  have h2 : sourceTwistedGaussianSum lam (Real.sqrt (4 * Real.pi / t)) 2 =
      sourceGaussianProfile lam (4 * t) := by
    have hg (n : ℕ) : gaussW (Real.sqrt (4 * Real.pi / t)) ((n : ℝ) * 2) =
        Real.exp (-Real.pi * (n : ℝ) ^ 2 * (4 * t)) := by
      rw [gaussW_polynomial_mellin_scale ht]
      congr 1
      ring
    unfold sourceTwistedGaussianSum sourceGaussianProfile
    simp_rw [hg, hc2, mul_one]
  have hh : sourceTwistedGaussianSum lam (Real.sqrt (4 * Real.pi / t)) (1 / 2) =
      sourceAlternatingGaussianProfile lam (t / 4) := by
    have hg (n : ℕ) : gaussW (Real.sqrt (4 * Real.pi / t)) ((n : ℝ) / 2) =
        Real.exp (-Real.pi * (n : ℝ) ^ 2 * (t / 4)) := by
      rw [gaussW_polynomial_mellin_scale ht]
      congr 1
      ring
    unfold sourceTwistedGaussianSum
    rw [source_twisted_gaussW_half_eq]
    simp_rw [hg]
    rfl
  rw [sourceTwoPointGaussianSum, h1, h2, hh, sourceTwoPointGaussianProfile]
  ring

/-- The actual parity-weighted three-scale profile obeys a subcritical upper bound. -/
theorem exists_re_sourceTwoPointGaussianProfile_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (c : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      (sourceTwoPointGaussianProfile lam c t).re ≤ C * t ^ (-5 / 12 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := exists_re_sourceTwoPointGaussianSum_le hW c
  refine ⟨C * (4 * Real.pi) ^ (5 / 12 : ℝ), by positivity, fun t ht ht1 => ?_⟩
  have hscale : 1 ≤ Real.sqrt (4 * Real.pi / t) := by
    apply Real.one_le_sqrt.mpr
    apply (le_div_iff₀ ht).mpr
    nlinarith [Real.pi_gt_three]
  have h := hC (Real.sqrt (4 * Real.pi / t)) hscale
  rw [sourceTwoPointGaussianSum_mellin_scale lam c ht] at h
  have he : Real.sqrt (4 * Real.pi / t) ^ (5 / 6 : ℝ) =
      (4 * Real.pi) ^ (5 / 12 : ℝ) * t ^ (-5 / 12 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
    norm_num only [show (1 / 2 : ℝ) * (5 / 6) = 5 / 12 by norm_num]
    rw [Real.div_rpow (by positivity) ht.le, div_eq_mul_inv, Real.rpow_neg ht.le]
  rw [he] at h
  simpa only [mul_assoc] using h

end RHTower.WeilSingularArithmetic
