import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorCosineMellin
import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorPrimitiveMellin
import GaloisForLFunctions.HTGeometry.GammaMonomialAnalytic

/-!
# The explicit Mellin factor of the actual boundary primitive

The original cubic datum pays absolute convergence on `1 < re s < 2`.
The normalized scalar factor is holomorphic and nonzero on `0 < re s < 2`,
so it cannot hide an interior quotient pole. These statements identify the
actual primitive; no local regularity of its inversion defect is presumed.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology
namespace RHTower.WeilHigherDenominator

/-- The scalar regularization has an explicit Gamma factor on its full strip. -/
theorem cosineDifferenceMellin_eq_gamma {s : ℂ} (hs0 : 0 < s.re) (hs2 : s.re < 2) :
    cosineDifferenceMellin s =
      -((2 * Real.pi : ℝ) : ℂ) ^ (2 - s) * (Real.pi : ℂ) /
        (2 * Complex.Gamma (3 - s) * Complex.sin ((Real.pi : ℂ) * ((2 - s) / 2))) := by
  have hα0 : 0 < (2 - s).re := by
    simp only [Complex.sub_re, Complex.re_ofNat]
    linarith
  have hα2 : (2 - s).re < 2 := by
    simp only [Complex.sub_re, Complex.re_ofNat]
    linarith
  have hcos : mellin (fun x : ℝ => (Real.cos x : ℂ) - 1) (s - 2) =
      -(∫ x in Ioi (0 : ℝ), cosineFractionalKernel (2 - s) x) := by
    rw [mellin, ← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [smul_eq_mul, cosineFractionalKernel]
    rw [show s - 2 - 1 = -1 - (2 - s) by ring]
    ring
  have hm := mellin_comp_mul_left (fun x : ℝ => (Real.cos x : ℂ) - 1) (s - 2)
    (mul_pos (zero_lt_two : (0 : ℝ) < 2) Real.pi_pos)
  rw [hcos, integral_cosineFractionalKernel hα0 hα2] at hm
  rw [show -(s - 2) = 2 - s by ring, show (2 - s) + 1 = 3 - s by ring] at hm
  simpa only [cosineDifferenceMellin, smul_eq_mul, mul_neg, neg_mul, neg_div, mul_div_assoc] using hm

/-- The Gamma factor of the twice-integrated actual boundary distribution. -/
def primitiveMellinGammaFactor (s : ℂ) : ℂ :=
  -((2 * Real.pi : ℝ) : ℂ) ^ (2 - s) /
    (2 * (Real.pi : ℂ) * Complex.Gamma (3 - s) *
      Complex.sin ((Real.pi : ℂ) * ((2 - s) / 2)))

/-- Removing the Fourier primitive's normalization gives the explicit factor. -/
theorem cosineDifferenceMellin_div_pi_sq {s : ℂ}
    (hs0 : 0 < s.re) (hs2 : s.re < 2) :
    cosineDifferenceMellin s / (Real.pi : ℂ) ^ 2 = primitiveMellinGammaFactor s := by
  rw [cosineDifferenceMellin_eq_gamma hs0 hs2]
  dsimp [primitiveMellinGammaFactor]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [div_eq_mul_inv, mul_inv_rev]
  field_simp

private lemma primitiveMellinGamma_denominator_ne_zero {s : ℂ}
    (hs0 : 0 < s.re) (hs2 : s.re < 2) :
    2 * (Real.pi : ℂ) * Complex.Gamma (3 - s) *
      Complex.sin ((Real.pi : ℂ) * ((2 - s) / 2)) ≠ 0 := by
  have hw : 0 < ((2 - s) / 2).re := by
    simp only [Complex.div_ofNat_re, Complex.sub_re, Complex.re_ofNat]
    linarith
  have hw' : 0 < (1 - (2 - s) / 2).re := by
    simp only [Complex.div_ofNat_re, Complex.sub_re, Complex.re_ofNat, Complex.one_re]
    linarith
  have hsin : Complex.sin ((Real.pi : ℂ) * ((2 - s) / 2)) ≠ 0 := by
    intro hz
    have h := Complex.Gamma_mul_Gamma_one_sub ((2 - s) / 2)
    rw [hz, div_zero] at h
    exact mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos hw)
      (Complex.Gamma_ne_zero_of_re_pos hw') h
  have hG : Complex.Gamma (3 - s) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by
      simp only [Complex.sub_re, Complex.re_ofNat]
      linarith)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) hG) hsin

/-- The normalization cannot cancel an interior pole of the actual quotient. -/
theorem primitiveMellinGammaFactor_ne_zero {s : ℂ} (hs0 : 0 < s.re) (hs2 : s.re < 2) :
    primitiveMellinGammaFactor s ≠ 0 := by
  apply div_ne_zero _ (primitiveMellinGamma_denominator_ne_zero hs0 hs2)
  apply neg_ne_zero.mpr
  apply Complex.cpow_ne_zero_iff.mpr
  exact Or.inl (Complex.ofReal_ne_zero.mpr (mul_ne_zero two_ne_zero Real.pi_ne_zero))

/-- The explicit normalization is holomorphic across the interior critical strip. -/
theorem analyticAt_primitiveMellinGammaFactor {s : ℂ}
    (hs0 : 0 < s.re) (hs2 : s.re < 2) :
    AnalyticAt ℂ primitiveMellinGammaFactor s := by
  have hd : Differentiable ℂ (fun z : ℂ => 2 - z) := by fun_prop
  have hp : Differentiable ℂ (fun z : ℂ => ((2 * Real.pi : ℝ) : ℂ) ^ (2 - z)) :=
    hd.const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr (mul_ne_zero two_ne_zero Real.pi_ne_zero)))
  have hG : AnalyticAt ℂ (fun z : ℂ => Complex.Gamma (3 - z)) s :=
    (GaloisForLFunctions.HTGeometry.analyticAt_Gamma_of_re_pos (by
      simp only [Complex.sub_re, Complex.re_ofNat]
      linarith)).comp (analyticAt_const.sub analyticAt_id)
  have hsin : AnalyticAt ℂ (fun z : ℂ =>
      Complex.sin ((Real.pi : ℂ) * ((2 - z) / 2))) s := by
    apply Differentiable.analyticAt
    fun_prop
  exact (hp.analyticAt s).neg.div ((analyticAt_const.mul hG).mul hsin)
    (primitiveMellinGamma_denominator_ne_zero hs0 hs2)

/-- Absolute Mellin evaluation from the original cubic datum, with no extra decay premise. -/
theorem hasMellin_degreeTwoQuotient_primitive_gamma {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) {s : ℂ} (hs1 : 1 < s.re) (hs2 : s.re < 2) :
    HasMellin (fun x : ℝ => fourierBoundaryPrimitive (degreeTwoQuotientCoeff g) x -
      fourierBoundaryPrimitive (degreeTwoQuotientCoeff g) 0) (s - 2)
      ((LSeries g s / riemannZeta s) * primitiveMellinGammaFactor s) := by
  have h := hasMellin_degreeTwoQuotient_primitive hD hs1 hs2
  rwa [mul_div_assoc, cosineDifferenceMellin_div_pi_sq (by linarith) hs2] at h

end RHTower.WeilHigherDenominator
