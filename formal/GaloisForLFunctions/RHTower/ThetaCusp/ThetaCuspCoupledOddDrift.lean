import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddCompensationCoefficient
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspMiddleLikelihoodBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Canonical coupled odd-flux drift

The derivative cross term of the moving odd central coordinate has an
explicit normalization by the first-atom mass and fifth source scale.
Its complete-source coefficient is nonnegative and uniformly bounded
on the scale-five ray. The source mass and compensation coefficient
are the literal canonical quantities.
-/

namespace RHTower.ThetaCuspCoupledOddDrift
noncomputable section

private theorem tangent_coefficient : 5 ≤ Real.pi*Real.exp (93/200:ℝ) := by
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 93/200) 5
  norm_num [Finset.sum_range_succ] at he
  have hp := mul_le_mul (show (31415/10000:ℝ) ≤ Real.pi by linarith [Real.pi_gt_d4])
    he (by norm_num) Real.pi_pos.le
  norm_num at hp
  linarith only [hp]

private theorem center_tangent (x : ℝ) :
    10*x+107/40 ≤ thetaCuspSingleAtomReflectionScale 1 x := by
  have he := Real.add_one_le_exp (2*x-93/200)
  have hm := mul_le_mul_of_nonneg_right tangent_coefficient
    (Real.exp_pos (2*x-93/200)).le
  have hid : Real.pi*Real.exp (93/200)*Real.exp (2*x-93/200)=
      thetaCuspSingleAtomReflectionScale 1 x := by
    rw [mul_assoc, ← Real.exp_add]
    norm_num [thetaCuspSingleAtomReflectionScale]
  rw [hid] at hm
  linarith only [he, hm]

private theorem center_payment {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    1250000*x ≤ 93*thetaCuspSingleAtomReflectionScale 1 x^5 := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hq5 : 5 ≤ q := hq
  have ht := center_tangent x
  change 10*x+107/40 ≤ q at ht
  have hpow : 3125+3125*(q-5) ≤ q^5 := by
    have hp : 0 ≤ (q-5)^2*((q-5)^3+25*(q-5)^2+250*(q-5)+1250) := by positivity
    nlinarith only [hp]
  change 1250000*x ≤ 93*q^5
  nlinarith only [ht, hpow, hq5]

/-- Actual derivative cross coefficient in normalized odd central coordinates. -/
noncomputable def normalizedCanonicalDrift (x : ℝ) : ℝ :=
  thetaCuspNativeOddCompensationCoefficient*x*thetaCuspFullSource x^2 /
    (786432*thetaCuspSingleAtomReflectionScale 1 x^5*thetaCuspSourceTerm x 1^2)

/-- The canonical complete-source drift lies between zero and 29/100 on the scale-five ray. -/
theorem normalizedCanonicalDrift_bounds {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 ≤ normalizedCanonicalDrift x ∧ normalizedCanonicalDrift x ≤ 29/100 := by
  have hqm : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hqm
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1:ℕ))
  have hF := thetaCuspFullSource_pos_all x
  have hq0 : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hC := thetaCuspNativeOddCompensationCoefficient_bounds
  have hC0 : 0 ≤ thetaCuspNativeOddCompensationCoefficient := by linarith [hC.1]
  have hmass := pow_le_pow_left₀ hF.le (thetaCuspFullSource_mass_bounds_middle hqm).2 2
  have hcenter := center_payment hq
  constructor
  · unfold normalizedCanonicalDrift
    positivity
  · unfold normalizedCanonicalDrift
    apply (div_le_iff₀ (by positivity)).mpr
    have h1 := mul_le_mul_of_nonneg_right hC.2.le
      (show 0 ≤ x*thetaCuspFullSource x^2 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hmass (show (0:ℝ) ≤ 3000000000*x by positivity)
    have h3 := mul_le_mul_of_nonneg_right hcenter (sq_nonneg (thetaCuspSourceTerm x 1))
    have h4 : 0 ≤ thetaCuspSingleAtomReflectionScale 1 x^5*thetaCuspSourceTerm x 1^2 := by positivity
    nlinarith only [h1,h2,h3,h4]

end
end RHTower.ThetaCuspCoupledOddDrift
