import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedParticularCuspFlux
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCyclicPeierlsAffineCuspIncidence

/-!
The literal complementary clock-`−6` source has a candidate renormalized cusp
residue.  This leaf closes its arithmetic/algebraic nonvanishing: the leading
three-power response coefficient survives on both branches, and its clock-20
Euler multiplier cannot vanish.  The analytic averaging identity that identifies
this coefficient with the actual full-response source remains open.
-/

open Complex Real Set
open RHTower
open RHTower.D4BMGlobalAngularResponse
open RHTower.D4BMLiteralCyclicPeierlsAffineCuspIncidence
open RHTower.D4BMMixedParticularCuspFlux

namespace RHTower.D4BMCrossClockResidueCore
noncomputable section
set_option autoImplicit false

def extremeIndex (q : XiZeroCopy) : Fin 3 :=
  if (q.1 : ℂ).re < (2 : ℝ)⁻¹ then 2 else 0

private theorem leading_weyl_ne_zero (q : XiZeroCopy) :
    weylCoefficient q (if (q.1 : ℂ).re < (2 : ℝ)⁻¹ then false else true) ≠ 0 := by
  by_cases hleft : (q.1 : ℂ).re < (2 : ℝ)⁻¹
  · simp only [hleft, ite_true, weylCoefficient,
      d4BMCompletedEisensteinCuspConstantCoefficient]
    change reflectedCompletedLambda (2 * ((q.1 : ℂ) - 1/2)) ≠ 0
    have hleft' : (q.1 : ℂ).re < 1/2 := by simpa only [one_div] using hleft
    convert (fun h => affine_lower_lambda_zero_not_left q ⟨h,hleft'⟩) using 1
    congr 1
    ring
  · simp only [hleft, ite_false, weylCoefficient,
      d4BMCompletedEisensteinCuspConstantCoefficient]
    change reflectedCompletedLambda (1 + 2 * ((q.1 : ℂ) - 1/2)) ≠ 0
    have hleft' : ¬ (q.1 : ℂ).re < 1/2 := by simpa only [one_div] using hleft
    have hge : 1/2 ≤ (q.1 : ℂ).re := le_of_not_gt hleft'
    have he : 1 + 2 * ((q.1 : ℂ) - 1/2) = 2 * (q.1 : ℂ) := by ring
    rw [he]
    unfold reflectedCompletedLambda
    apply mul_ne_zero
    · apply Complex.Gammaℝ_ne_zero_of_re_pos
      norm_num [Complex.mul_re]
      linarith
    · apply riemannZeta_ne_zero_of_one_le_re
      norm_num [Complex.mul_re]
      linarith

theorem extreme_sourceCoefficient_ne_zero (q : XiZeroCopy) :
    sourceCoefficient q (extremeIndex q) ≠ 0 := by
  by_cases hleft : (q.1 : ℂ).re < (2 : ℝ)⁻¹
  · have h := leading_weyl_ne_zero q
    simp only [hleft, ite_true] at h
    have hi : extremeIndex q = 2 := by simp [extremeIndex, hleft]
    rw [hi]
    change weylCoefficient q false ^ (2 : ℕ) ≠ 0
    exact pow_ne_zero 2 h
  · have h := leading_weyl_ne_zero q
    simp only [hleft, ite_false] at h
    have hi : extremeIndex q = 0 := by simp [extremeIndex, hleft]
    rw [hi]
    change weylCoefficient q true ^ (2 : ℕ) ≠ 0
    exact pow_ne_zero 2 h

theorem extreme_responseCoefficient_ne_zero (q : XiZeroCopy) (b : Bool) :
    responseCoefficient q b (extremeIndex q) ≠ 0 := by
  unfold responseCoefficient
  have hparam : parameter q b ≠ 0 := by
    change RHTower.D4BMQuadraticMixedSource.branchParameter (q.1 : ℂ) b ≠ 0
    exact neg_ne_zero.mp (RHTower.D4BMQuadraticMixedSource.xi_cusp_denominators q b).2.1
  exact div_ne_zero
    (mul_ne_zero (div_ne_zero hparam (by norm_num))
      (extreme_sourceCoefficient_ne_zero q))
    (denominator_ne_zero q b (extremeIndex q))

def residueMultiplier (q : XiZeroCopy) : ℂ :=
  let r := 2 * sourcePower q (extremeIndex q)
  r * (r - 1) - 20

theorem residueMultiplier_ne_zero (q : XiZeroCopy) : residueMultiplier q ≠ 0 := by
  have hr : (2 * sourcePower q (extremeIndex q)).re < 4 := by
    by_cases hleft : (q.1 : ℂ).re < (2 : ℝ)⁻¹
    · have hi : extremeIndex q = 2 := by simp [extremeIndex, hleft]
      rw [hi]
      change (2 * (2 - 2 * (q.1 : ℂ))).re < 4
      norm_num [Complex.mul_re, Complex.sub_re]
      have hq := (xi_divisor_support_re_mem_open_unit q.1).1
      linarith
    · have hi : extremeIndex q = 0 := by simp [extremeIndex, hleft]
      rw [hi]
      change (2 * (2 * (q.1 : ℂ))).re < 4
      norm_num [Complex.mul_re]
      have hq := (xi_divisor_support_re_mem_open_unit q.1).2
      linarith
  have hl : 2 ≤ (2 * sourcePower q (extremeIndex q)).re := by
    by_cases hleft : (q.1 : ℂ).re < (2 : ℝ)⁻¹
    · have hi : extremeIndex q = 2 := by simp [extremeIndex, hleft]
      rw [hi]
      change 2 ≤ (2 * (2 - 2 * (q.1 : ℂ))).re
      norm_num [Complex.mul_re, Complex.sub_re]
      linarith
    · have hi : extremeIndex q = 0 := by simp [extremeIndex, hleft]
      rw [hi]
      change 2 ≤ (2 * (2 * (q.1 : ℂ))).re
      norm_num [Complex.mul_re]
      linarith
  intro h
  have hpoly : (2 * sourcePower q (extremeIndex q) - 5) *
      (2 * sourcePower q (extremeIndex q) + 4) = 0 := by
    dsimp [residueMultiplier] at h
    linear_combination h
  rcases mul_eq_zero.mp hpoly with h5 | hm4
  · have he := congrArg Complex.re (sub_eq_zero.mp h5)
    norm_num [Complex.mul_re] at he
    norm_num [Complex.mul_re] at hr
    linarith
  · have he := congrArg Complex.re hm4
    norm_num [Complex.mul_re, Complex.add_re] at he
    norm_num [Complex.mul_re] at hl
    linarith

theorem residueCoefficient_ne_zero (q : XiZeroCopy) :
    residueMultiplier q * responseCoefficient q true (extremeIndex q) *
      responseCoefficient q false (extremeIndex q) ≠ 0 := by
  exact mul_ne_zero
    (mul_ne_zero (residueMultiplier_ne_zero q)
      (extreme_responseCoefficient_ne_zero q true))
    (extreme_responseCoefficient_ne_zero q false)

end
end RHTower.D4BMCrossClockResidueCore
