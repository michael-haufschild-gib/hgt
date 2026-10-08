import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticPolynomialShift
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticTwistedExtraction

/-!
# A polynomial-weighted Gaussian inequality for the actual arithmetic source

The negative coefficients are handled by the positive spectral pairing,
not by combining scalar upper bounds. The half-scale term retains its
cosine and therefore the parity twist of the actual coefficients.
-/

open Complex MeasureTheory Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic

open GaussZeroSum

def sourceTwistedGaussianSum (lam : ℕ → ℝ) (T r : ℝ) : ℂ :=
  ∑' n : ℕ, sourceSquareCoeff lam n *
    ((gaussW T (n * r) * Real.cos (2 * Real.pi * (n * r)) : ℝ) : ℂ)

def sourceTwoPointGaussianSum (lam : ℕ → ℝ) (c T : ℝ) : ℂ :=
  (1 + (c : ℂ) ^ 2 / 2) * sourceTwistedGaussianSum lam T 1 -
    c * sourceTwistedGaussianSum lam T 2 -
    ((c : ℂ) / 2) * sourceTwistedGaussianSum lam T (1 / 2)

theorem integral_sourceZetaPairing_polynomial_eq_scaled {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (c : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    let J : ℝ → ℂ := fun r => ∫ t : ℝ, sourceZetaPairing hW ((3 / 2 : ℂ) + t * I) *
      ((r : ℂ) ^ (1 - ((3 / 2 : ℂ) + t * I)) * gaussWeight T ((3 / 2 : ℂ) + t * I))
    (∫ t : ℝ, sourceZetaPairing hW ((3 / 2 : ℂ) + t * I) *
      gaussWeight T ((3 / 2 : ℂ) + t * I) * sourceTwoPointWeight c ((3 / 2 : ℂ) + t * I)) =
      (1 + (c : ℂ) ^ 2 / 2) * J 1 - ((c : ℂ) / 2) * J 2 - (c : ℂ) * J (1 / 2) := by
  dsimp only
  have h1 := integrable_sourceZetaPairing_scaled_gaussian hW hT (r := 1) (by norm_num)
  have h2 := integrable_sourceZetaPairing_scaled_gaussian hW hT (r := 2) (by norm_num)
  have hh := integrable_sourceZetaPairing_scaled_gaussian hW hT (r := 1 / 2) (by norm_num)
  have he (t : ℝ) : sourceZetaPairing hW ((3 / 2 : ℂ) + t * I) *
      gaussWeight T ((3 / 2 : ℂ) + t * I) * sourceTwoPointWeight c ((3 / 2 : ℂ) + t * I) =
      (1 + (c : ℂ) ^ 2 / 2) * (sourceZetaPairing hW ((3 / 2 : ℂ) + t * I) *
        (((1 : ℝ) : ℂ) ^ (1 - ((3 / 2 : ℂ) + t * I)) * gaussWeight T ((3 / 2 : ℂ) + t * I))) -
      ((c : ℂ) / 2) * (sourceZetaPairing hW ((3 / 2 : ℂ) + t * I) *
        (((2 : ℝ) : ℂ) ^ (1 - ((3 / 2 : ℂ) + t * I)) * gaussWeight T ((3 / 2 : ℂ) + t * I))) -
      (c : ℂ) * (sourceZetaPairing hW ((3 / 2 : ℂ) + t * I) *
        (((1 / 2 : ℝ) : ℂ) ^ (1 - ((3 / 2 : ℂ) + t * I)) * gaussWeight T ((3 / 2 : ℂ) + t * I))) := by
    rw [sourceTwoPointWeight_expansion]
    norm_num only [Complex.ofReal_one, Complex.one_cpow, one_mul, Complex.ofReal_ofNat,
      Complex.ofReal_div]
    ring
  simp_rw [he]
  have hs := integral_sub ((h1.const_mul (1 + (c : ℂ) ^ 2 / 2)).sub
      (h2.const_mul ((c : ℂ) / 2))) (hh.const_mul (c : ℂ))
  simp only [Pi.sub_apply] at hs
  rw [hs, integral_sub (h1.const_mul (1 + (c : ℂ) ^ 2 / 2)) (h2.const_mul ((c : ℂ) / 2)), integral_const_mul,
    integral_const_mul, integral_const_mul]

theorem exists_norm_source_polynomial_contour_sub_gaussian_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (c : ℝ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ T : ℝ, 1 ≤ T →
      ‖(∫ t : ℝ, sourceZetaPairing hW ((3 / 2 : ℂ) + t * I) *
        gaussWeight T ((3 / 2 : ℂ) + t * I) * sourceTwoPointWeight c ((3 / 2 : ℂ) + t * I)) -
        (4 * Real.pi : ℂ) * sourceTwoPointGaussianSum lam c T‖ ≤ E * T ^ (5 / 6 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_source_scaled_contour_sub_gaussian_le hW
  let A : ℂ := 1 + (c : ℂ) ^ 2 / 2
  refine ⟨‖A‖ * C + ‖(c : ℂ) / 2‖ * C * (2 : ℝ) ^ (-1 / 8 : ℝ) +
    ‖(c : ℂ)‖ * C * (1 / 2 : ℝ) ^ (-1 / 8 : ℝ), by positivity, fun T hT => ?_⟩
  let J : ℝ → ℂ := fun r => ∫ t : ℝ, sourceZetaPairing hW ((3 / 2 : ℂ) + t * I) *
    ((r : ℂ) ^ (1 - ((3 / 2 : ℂ) + t * I)) * gaussWeight T ((3 / 2 : ℂ) + t * I))
  let e : ℝ → ℂ := fun r => J r - (4 * Real.pi * r : ℂ) * sourceTwistedGaussianSum lam T r
  have he (r : ℝ) (hr : 0 < r) : ‖e r‖ ≤ C * r ^ (-1 / 8 : ℝ) * T ^ (5 / 6 : ℝ) :=
    hC r hr T hT
  have he1 : ‖e 1‖ ≤ C * T ^ (5 / 6 : ℝ) := by simpa only [Real.one_rpow, mul_one] using he 1 (by norm_num)
  have he2 := he 2 (by norm_num)
  have heh := he (1 / 2) (by norm_num)
  have hI := integral_sourceZetaPairing_polynomial_eq_scaled hW c hT
  change _ = A * J 1 - ((c : ℂ) / 2) * J 2 - (c : ℂ) * J (1 / 2) at hI
  have hid : (∫ t : ℝ, sourceZetaPairing hW ((3 / 2 : ℂ) + t * I) *
      gaussWeight T ((3 / 2 : ℂ) + t * I) * sourceTwoPointWeight c ((3 / 2 : ℂ) + t * I)) -
      (4 * Real.pi : ℂ) * sourceTwoPointGaussianSum lam c T =
      A * e 1 - ((c : ℂ) / 2) * e 2 - (c : ℂ) * e (1 / 2) := by
    rw [hI]
    dsimp only [e, sourceTwoPointGaussianSum, A]
    push_cast
    ring
  rw [hid]
  calc
    _ ≤ ‖A * e 1 - ((c : ℂ) / 2) * e 2‖ + ‖(c : ℂ) * e (1 / 2)‖ := norm_sub_le _ _
    _ ≤ (‖A * e 1‖ + ‖((c : ℂ) / 2) * e 2‖) + ‖(c : ℂ) * e (1 / 2)‖ := by
      gcongr
      exact norm_sub_le _ _
    _ = ‖A‖ * ‖e 1‖ + ‖(c : ℂ) / 2‖ * ‖e 2‖ + ‖(c : ℂ)‖ * ‖e (1 / 2)‖ := by
      simp only [norm_mul]
    _ ≤ ‖A‖ * (C * T ^ (5 / 6 : ℝ)) +
        ‖(c : ℂ) / 2‖ * (C * (2 : ℝ) ^ (-1 / 8 : ℝ) * T ^ (5 / 6 : ℝ)) +
        ‖(c : ℂ)‖ * (C * (1 / 2 : ℝ) ^ (-1 / 8 : ℝ) * T ^ (5 / 6 : ℝ)) := by gcongr
    _ = _ := by ring

/-- Every full-positive source obeys the corrected three-scale Gaussian inequality. -/
theorem exists_re_sourceTwoPointGaussianSum_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (c : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      (sourceTwoPointGaussianSum lam c T).re ≤ C * T ^ (5 / 6 : ℝ) := by
  obtain ⟨B, hB0, hB⟩ := exists_re_integral_sourceZetaPairing_polynomial_right_le hW c
  obtain ⟨E, hE0, hE⟩ := exists_norm_source_polynomial_contour_sub_gaussian_le hW c
  refine ⟨(B + E) / (4 * Real.pi), by positivity, fun T hT => ?_⟩
  let I : ℂ := ∫ t : ℝ, sourceZetaPairing hW ((3 / 2 : ℂ) + t * Complex.I) *
    gaussWeight T ((3 / 2 : ℂ) + t * Complex.I) * sourceTwoPointWeight c ((3 / 2 : ℂ) + t * Complex.I)
  let e : ℂ := I - (4 * Real.pi : ℂ) * sourceTwoPointGaussianSum lam c T
  have hb : I.re ≤ B := hB T hT
  have he : -e.re ≤ E * T ^ (5 / 6 : ℝ) :=
    (neg_le_abs e.re).trans ((Complex.abs_re_le_norm e).trans (hE T hT))
  have hid : e.re = I.re - 4 * Real.pi * (sourceTwoPointGaussianSum lam c T).re := by
    simp only [e, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.re_ofNat,
      Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul,
      add_zero, sub_zero]
  have hp : 1 ≤ T ^ (5 / 6 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hT (show (0 : ℝ) ≤ 5 / 6 by norm_num)
  have hBp := mul_le_mul_of_nonneg_left hp hB0
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < 4 * Real.pi)).mpr
  nlinarith

end RHTower.WeilSingularArithmetic
