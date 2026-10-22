import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicHypergeometricAnalyticODE

/-!
# Full BM complementary second-harmonic solution jet

The leading Frobenius power is multiplied by the convergent transformed hypergeometric factor.
Exact first and second real derivatives are proved on `0 < z < 1`. Frobenius transformation then
reduces the original BM radial jet to the analytic transformed Gauss equation, proving the full
complementary solution and every Xi specialization without additional premises.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- Exact second derivative of the leading complementary Frobenius power on the positive ray. -/
def d4BMPlusPlusLeadingComplementaryFrobeniusBranchSecondDerivative
    (n : ℕ) (chi : ℂ) (z : ℝ) : ℂ :=
  d4BMPlusPlusComplementaryFrobeniusExponent n chi *
      (d4BMPlusPlusComplementaryFrobeniusExponent n chi - 1) *
    d4BMPlusPlusLeadingComplementaryFrobeniusBranch n chi z / (z : ℂ) ^ 2

/-- The algebraic second Frobenius derivative is the actual derivative of the first one. -/
theorem hasDerivAt_d4BMPlusPlusLeadingComplementaryFrobeniusBranchDerivative
    (n : ℕ) (chi : ℂ) {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt (d4BMPlusPlusLeadingComplementaryFrobeniusBranchDerivative n chi)
      (d4BMPlusPlusLeadingComplementaryFrobeniusBranchSecondDerivative n chi z) z := by
  let lam := d4BMPlusPlusComplementaryFrobeniusExponent n chi
  let h := d4BMPlusPlusLeadingComplementaryFrobeniusBranch n chi
  have hh : HasDerivAt h (lam * h z / (z : ℂ)) z := by
    simpa [h, lam, d4BMPlusPlusLeadingComplementaryFrobeniusBranchDerivative] using
      hasDerivAt_d4BMPlusPlusLeadingComplementaryFrobeniusBranch n chi hz
  have hzderiv : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 z :=
    (hasDerivAt_id z).ofReal_comp
  have hzC : (z : ℂ) ≠ 0 := by exact_mod_cast hz
  have hquot := (hh.const_mul lam).div hzderiv hzC
  change HasDerivAt (fun x : ℝ => lam * h x / (x : ℂ))
    (lam * (lam - 1) * h z / (z : ℂ) ^ 2) z
  apply hquot.congr_deriv
  field_simp [hzC]

/-- Full complementary `++` solution `z^(1-c) ₂F₁(a-c+1,b-c+1;2-c;z)` on the positive ray. -/
def d4BMPlusPlusComplementaryHypergeometricSolution
    (n : ℕ) (chi : ℂ) (z : ℝ) : ℂ :=
  d4BMPlusPlusLeadingComplementaryFrobeniusBranch n chi z *
    d4BMPlusPlusComplementaryHypergeometricFactor n chi (z : ℂ)

/-- Exact first jet of the full complementary solution. -/
def d4BMPlusPlusComplementaryHypergeometricSolutionDerivative
    (n : ℕ) (chi : ℂ) (z : ℝ) : ℂ :=
  d4BMPlusPlusLeadingComplementaryFrobeniusBranchDerivative n chi z *
      d4BMPlusPlusComplementaryHypergeometricFactor n chi (z : ℂ) +
    d4BMPlusPlusLeadingComplementaryFrobeniusBranch n chi z *
      d4BMPlusPlusComplementaryHypergeometricFirstDerivative n chi (z : ℂ)

/-- Exact second jet of the full complementary solution. -/
def d4BMPlusPlusComplementaryHypergeometricSolutionSecondDerivative
    (n : ℕ) (chi : ℂ) (z : ℝ) : ℂ :=
  d4BMPlusPlusLeadingComplementaryFrobeniusBranchSecondDerivative n chi z *
      d4BMPlusPlusComplementaryHypergeometricFactor n chi (z : ℂ) +
    2 * d4BMPlusPlusLeadingComplementaryFrobeniusBranchDerivative n chi z *
      d4BMPlusPlusComplementaryHypergeometricFirstDerivative n chi (z : ℂ) +
    d4BMPlusPlusLeadingComplementaryFrobeniusBranch n chi z *
      d4BMPlusPlusComplementaryHypergeometricSecondDerivative n chi (z : ℂ)

/-- Positive real points below one lie in the complex open unit disk. -/
theorem enorm_ofReal_lt_one {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    ‖(z : ℂ)‖ₑ < 1 := by
  rw [← ENNReal.coe_one, enorm_lt_coe]
  rw [Complex.nnnorm_real, Real.nnnorm_of_nonneg hz0.le]
  exact_mod_cast hz1

/-- The exact first solution jet is the actual derivative on `0<z<1`. -/
theorem hasDerivAt_d4BMPlusPlusComplementaryHypergeometricSolution
    (n : ℕ) (chi : ℂ) {z : ℝ} (hchi : chi.re ≠ 0)
    (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt (d4BMPlusPlusComplementaryHypergeometricSolution n chi)
      (d4BMPlusPlusComplementaryHypergeometricSolutionDerivative n chi z) z := by
  have hL := hasDerivAt_d4BMPlusPlusLeadingComplementaryFrobeniusBranch
    n chi (ne_of_gt hz0)
  have hF :=
    (hasDerivAt_d4BMPlusPlusComplementaryHypergeometricFactor
      n chi (z : ℂ) hchi (enorm_ofReal_lt_one hz0 hz1)).comp_ofReal
  simpa [d4BMPlusPlusComplementaryHypergeometricSolution,
    d4BMPlusPlusComplementaryHypergeometricSolutionDerivative] using! hL.mul hF

/-- The exact second solution jet differentiates the first jet on `0<z<1`. -/
theorem hasDerivAt_d4BMPlusPlusComplementaryHypergeometricSolutionDerivative
    (n : ℕ) (chi : ℂ) {z : ℝ} (hchi : chi.re ≠ 0)
    (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt (d4BMPlusPlusComplementaryHypergeometricSolutionDerivative n chi)
      (d4BMPlusPlusComplementaryHypergeometricSolutionSecondDerivative n chi z) z := by
  have hL := hasDerivAt_d4BMPlusPlusLeadingComplementaryFrobeniusBranch
    n chi (ne_of_gt hz0)
  have hL' := hasDerivAt_d4BMPlusPlusLeadingComplementaryFrobeniusBranchDerivative
    n chi (ne_of_gt hz0)
  have hF :=
    (hasDerivAt_d4BMPlusPlusComplementaryHypergeometricFactor
      n chi (z : ℂ) hchi (enorm_ofReal_lt_one hz0 hz1)).comp_ofReal
  have hF' :=
    (hasDerivAt_d4BMPlusPlusComplementaryHypergeometricFirstDerivative
      n chi (z : ℂ) hchi (enorm_ofReal_lt_one hz0 hz1)).comp_ofReal
  have h := (hL'.mul hF).add (hL.mul hF')
  change HasDerivAt
    (fun x : ℝ =>
      d4BMPlusPlusLeadingComplementaryFrobeniusBranchDerivative n chi x *
          d4BMPlusPlusComplementaryHypergeometricFactor n chi (x : ℂ) +
        d4BMPlusPlusLeadingComplementaryFrobeniusBranch n chi x *
          d4BMPlusPlusComplementaryHypergeometricFirstDerivative n chi (x : ℂ))
    (d4BMPlusPlusComplementaryHypergeometricSolutionSecondDerivative n chi z) z
  have hcompat : HasDerivAt
      (fun x : ℝ =>
        d4BMPlusPlusLeadingComplementaryFrobeniusBranchDerivative n chi x *
            d4BMPlusPlusComplementaryHypergeometricFactor n chi (x : ℂ) +
          d4BMPlusPlusLeadingComplementaryFrobeniusBranch n chi x *
            d4BMPlusPlusComplementaryHypergeometricFirstDerivative n chi (x : ℂ))
      (d4BMPlusPlusLeadingComplementaryFrobeniusBranchSecondDerivative n chi z *
          d4BMPlusPlusComplementaryHypergeometricFactor n chi (z : ℂ) +
        d4BMPlusPlusLeadingComplementaryFrobeniusBranchDerivative n chi z *
            d4BMPlusPlusComplementaryHypergeometricFirstDerivative n chi (z : ℂ) +
        (d4BMPlusPlusLeadingComplementaryFrobeniusBranchDerivative n chi z *
            d4BMPlusPlusComplementaryHypergeometricFirstDerivative n chi (z : ℂ) +
          d4BMPlusPlusLeadingComplementaryFrobeniusBranch n chi z *
            d4BMPlusPlusComplementaryHypergeometricSecondDerivative n chi (z : ℂ))) z := by
    simpa only using! h
  apply hcompat.congr_deriv
  rw [d4BMPlusPlusComplementaryHypergeometricSolutionSecondDerivative]
  ring

/-- Algebraic Frobenius transformation from the transformed Gauss operator to the original one. -/
theorem complementaryGaussJet_factor
    (a b c z h F dF ddF : ℂ) (hz : z ≠ 0) :
    z * (1 - z) *
          (((1 - c) * ((1 - c) - 1) * h / z ^ 2) * F +
            2 * ((1 - c) * h / z) * dF + h * ddF) +
        (c - (a + b + 1) * z) *
          (((1 - c) * h / z) * F + h * dF) -
      a * b * (h * F) =
        h *
          (z * (1 - z) * ddF +
            ((2 - c) -
              ((a - c + 1) + (b - c + 1) + 1) * z) * dF -
            (a - c + 1) * (b - c + 1) * F) := by
  field_simp [hz]
  ring

/-- The full complementary branch solves the original `++` BM hypergeometric radial equation. -/
theorem d4BMPlusPlusComplementaryHypergeometricSolution_jet_eq_zero
    (n : ℕ) (chi : ℂ) {z : ℝ} (hchi : chi.re ≠ 0)
    (hz0 : 0 < z) (hz1 : z < 1) :
    d4BMPlusPlusHypergeometricJet n chi z
      (d4BMPlusPlusComplementaryHypergeometricSolution n chi z)
      (d4BMPlusPlusComplementaryHypergeometricSolutionDerivative n chi z)
      (d4BMPlusPlusComplementaryHypergeometricSolutionSecondDerivative n chi z) = 0 := by
  have hode := d4BMPlusPlusComplementaryHypergeometric_standardGaussODE
    n chi (z : ℂ) hchi (enorm_ofReal_lt_one hz0 hz1)
  have hzC : (z : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hz0
  simp only [d4BMPlusPlusHypergeometricJet,
    d4BMPlusPlusComplementaryHypergeometricSolution,
    d4BMPlusPlusComplementaryHypergeometricSolutionDerivative,
    d4BMPlusPlusComplementaryHypergeometricSolutionSecondDerivative,
    d4BMPlusPlusLeadingComplementaryFrobeniusBranchDerivative,
    d4BMPlusPlusLeadingComplementaryFrobeniusBranchSecondDerivative,
    d4BMPlusPlusComplementaryFrobeniusExponent,
    d4BMPlusPlusComplementaryHypergeometricA,
    d4BMPlusPlusComplementaryHypergeometricB,
    d4BMPlusPlusComplementaryHypergeometricC] at hode ⊢
  push_cast at hode ⊢
  rw [complementaryGaussJet_factor _ _ _ _ _ _ _ _ hzC, hode, mul_zero]

/-- Every Xi fibre carries the exact full complementary BM solution jet on `0<z<1`. -/
theorem d4BMXiPlusPlusComplementaryHypergeometricSolution_jet_eq_zero
    (n : ℕ) (q : XiZeroCopy) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    d4BMPlusPlusHypergeometricJet n (d4BMXiMixedHorizonAngularMomentum q) z
      (d4BMPlusPlusComplementaryHypergeometricSolution n
        (d4BMXiMixedHorizonAngularMomentum q) z)
      (d4BMPlusPlusComplementaryHypergeometricSolutionDerivative n
        (d4BMXiMixedHorizonAngularMomentum q) z)
      (d4BMPlusPlusComplementaryHypergeometricSolutionSecondDerivative n
        (d4BMXiMixedHorizonAngularMomentum q) z) = 0 := by
  exact d4BMPlusPlusComplementaryHypergeometricSolution_jet_eq_zero n _
    (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q) hz0 hz1

end

end RHTower
