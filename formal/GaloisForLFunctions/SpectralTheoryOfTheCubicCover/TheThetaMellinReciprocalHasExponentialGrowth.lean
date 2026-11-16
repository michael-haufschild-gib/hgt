import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheUntwistedContinuationHasNoMellinPoles
import GaloisForLFunctions.HTGeometry.GammaGaussianEnvelopeDecay
import GaloisForLFunctions.HTGeometry.GammaReciprocalExpBound
import GaloisForLFunctions.HTGeometry.GammaVerticalStripDecay

/-!
# Exponential growth of the reciprocal theta Mellin factor

The Gamma quotient for the two-Bessel Mellin transform has four reciprocal
Gamma factors. Uniform reciprocal Gamma bounds and the positive-real-part
bound for `Gamma(2w)` give an exponential majorant on each closed strip
inside `Re w>1/3`. A Gaussian in the Mellin variable absorbs this growth.
-/

noncomputable section
namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

/-- The inverse theta-square Mellin factor has at most exponential vertical growth. -/
theorem besselSqMellin_inv_vertical_bound (a b : ℝ) (ha : 1 / 3 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, a ≤ w.re → w.re ≤ b → 1 ≤ |w.im| →
      ‖(besselSqMellin (2 * w))⁻¹‖ ≤ C * Real.exp (4 * Real.pi * |w.im|) := by
  obtain ⟨D, hD, hd⟩ := HTGeometry.exists_bound_Real_Gamma_Icc
    (a := 2 * a) (b := 2 * b) (by linarith)
  obtain ⟨G, hG, hg⟩ := GaloisForLFunctions.exists_bound_norm_inv_Gamma_strip
    (a - 1 / 3) (b + 1 / 3)
  refine ⟨D * (2 : ℝ) ^ (3 - 2 * a) * G ^ 4, by positivity, ?_⟩
  intro w hwa hwb hwt
  have hw : 2 / 3 < (2 * w).re := by simp; linarith
  have hΓ : ‖Complex.Gamma (2 * w)‖ ≤ D := by
    refine (HTGeometry.norm_Gamma_le_Gamma_re (by simp; linarith : 0 < (2 * w).re)).trans ?_
    exact hd (2 * w).re (by simp; linarith) (by simp; linarith)
  have hp := hg (w + 1 / 3) (by simp; linarith) (by simp; linarith) (by simpa using hwt)
  have hm := hg (w - 1 / 3) (by simp; linarith) (by simp; linarith) (by simpa using hwt)
  have h0 := hg w (by linarith) (by linarith) hwt
  have hip : (w + 1 / 3).im = w.im := by simp
  have him : (w - 1 / 3).im = w.im := by simp
  rw [hip] at hp
  rw [him] at hm
  have hpow : ‖(2 : ℂ) ^ (3 - 2 * w)‖ ≤ (2 : ℝ) ^ (3 - 2 * a) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    simp
    linarith
  have heq : (besselSqMellin (2 * w))⁻¹ =
      Complex.Gamma (2 * w) * (2 : ℂ) ^ (3 - 2 * w) *
        (Complex.Gamma (w + 1 / 3))⁻¹ * ((Complex.Gamma w)⁻¹) ^ 2 *
          (Complex.Gamma (w - 1 / 3))⁻¹ := by
    rw [besselSqMellin_eq_gamma (2 * w) hw,
      show 2 * w / 2 = w by ring,
      show (3 : ℂ) - 2 * w = -(2 * w - 3) by ring,
      Complex.cpow_neg]
    simp only [mul_inv_rev, inv_pow, div_eq_mul_inv, inv_inv]
    ring
  have he : (Real.exp (Real.pi * |w.im|)) ^ 4 = Real.exp (4 * Real.pi * |w.im|) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [heq, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow]
  calc
    _ ≤ D * (2 : ℝ) ^ (3 - 2 * a) * (G * Real.exp (Real.pi * |w.im|)) *
        (G * Real.exp (Real.pi * |w.im|)) ^ 2 * (G * Real.exp (Real.pi * |w.im|)) := by gcongr
    _ = D * (2 : ℝ) ^ (3 - 2 * a) * G ^ 4 * (Real.exp (Real.pi * |w.im|)) ^ 4 := by ring
    _ = _ := by rw [he]

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
