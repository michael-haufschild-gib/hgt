import GaloisForLFunctions.RHTower.ThetaCuspEffectiveReflectionApproximation
import GaloisForLFunctions.RHTower.ThetaCuspNativeOddSchurFarTail

/-!
# Explicit error scale on the ray q >= 30

The calibrated exponential bound and polynomial-exponential monotonicity give
q^5 epsilon <= 10^(-30). Consequently every required signed Gaussian-scale
moment through order ten differs from its first-atom value by at most 10^(-10).
-/

namespace RHTower
noncomputable section

/-- The calibrated likelihood error at scale thirty has an exact rational ceiling. -/
theorem base_scale_thirty_le :
    Real.exp (3*Real.pi)/399 * Real.exp (-(3*(30 : ℝ))) ≤ 32/(10 : ℝ)^39 := by
  have h30 : (10 : ℝ)^13 < Real.exp 30 := by
    have h := exp_thirty_gt
    norm_num
    linarith
  have h90 : (10 : ℝ)^39 < Real.exp 90 := by
    have hp := pow_lt_pow_left₀ h30 (by positivity) (by norm_num : (3 : ℕ) ≠ 0)
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp ⊢
    exact hp
  rw [show -(3*(30 : ℝ)) = -90 by norm_num, Real.exp_neg]
  rw [show Real.exp (3*Real.pi)/399*(Real.exp 90)⁻¹ =
      Real.exp (3*Real.pi)/(399*Real.exp 90) by field_simp]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 399*Real.exp 90)).mpr
  nlinarith [exp_three_pi_lt_12704]

/-- Uniform polynomially weighted error bound at a concrete source-scale endpoint. -/
theorem pow_five_mul_regimeOneLikelihoodScale_le_of_thirty_le {x : ℝ}
    (hq : 30 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspSingleAtomReflectionScale 1 x^5 * regimeOneLikelihoodScale x ≤ 1/(10 : ℝ)^30 := by
  have h := pow_mul_regimeOneLikelihoodScale_le (k := 5) (A₁ := 30)
    (by norm_num) (by norm_num) hq
  calc
    thetaCuspSingleAtomReflectionScale 1 x^5 * regimeOneLikelihoodScale x ≤
        (30 : ℝ)^5 * (Real.exp (3*Real.pi)/399 * Real.exp (-(3*(30 : ℝ)))) := h
    _ ≤ (30 : ℝ)^5 * (32/(10 : ℝ)^39) :=
      mul_le_mul_of_nonneg_left base_scale_thirty_le (by positivity)
    _ ≤ 1/(10 : ℝ)^30 := by norm_num

/-- First-atom signed reflection moment in the same Gaussian normalization as the complete source. -/
def thetaCuspFirstAtomScaledEvenJet (k : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ)^k * thetaCuspFirstAtomReflectionJet (2*k) x /
    (thetaCuspSourceTerm x 1^2 * thetaCuspSingleAtomReflectionScale 1 x^k)

/-- All-order effective error after the Gaussian-scale normalization. -/
theorem abs_thetaCuspNativeScaledEvenJet_sub_first_le_effective
    (k : ℕ) {x : ℝ} (hx : 0 < x)
    (hq : ((2*k : ℕ) : ℝ)+6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspNativeScaledEvenJet k x-thetaCuspFirstAtomScaledEvenJet k x| ≤
      27*(24 : ℝ)^(2*k)*thetaCuspSingleAtomReflectionScale 1 x^k*regimeOneLikelihoodScale x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hqpos : 0 < q := by dsimp [q, thetaCuspSingleAtomReflectionScale]; positivity
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have heq : thetaCuspNativeScaledEvenJet k x-thetaCuspFirstAtomScaledEvenJet k x =
      (-1 : ℝ)^k * ((thetaCuspNativeReflectionJet (2*k) x-thetaCuspFirstAtomReflectionJet (2*k) x) /
        thetaCuspSourceTerm x 1^2) / q^k := by
    unfold thetaCuspNativeScaledEvenJet thetaCuspFirstAtomScaledEvenJet
    dsimp [q]
    field_simp [hf.ne', hqpos.ne'] <;> ring
  rw [heq, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (pow_nonneg hqpos.le k)]
  apply (div_le_iff₀ (pow_pos hqpos k)).mpr
  have hb := abs_thetaCuspNativeReflectionJet_relative_error_le_singleScale (2*k) hx hq
  calc
    |(thetaCuspNativeReflectionJet (2*k) x-thetaCuspFirstAtomReflectionJet (2*k) x) /
        thetaCuspSourceTerm x 1^2| ≤ (27*(24*q)^(2*k)*regimeOneLikelihoodScale x) := hb
    _ = (27*(24 : ℝ)^(2*k)*thetaCuspSingleAtomReflectionScale 1 x^k*
        regimeOneLikelihoodScale x)*q^k := by
      dsimp [q]
      simp only [mul_pow, Nat.two_mul, pow_add]
      ring

/-- Uniform effective accuracy for all five required signed moments on the scale-thirty ray. -/
theorem abs_thetaCuspNativeScaledEvenJet_sub_first_le_ten_neg_ten
    {k : ℕ} (hk : k ≤ 5) {x : ℝ}
    (hq : 30 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspNativeScaledEvenJet k x-thetaCuspFirstAtomScaledEvenJet k x| ≤ 1/(10 : ℝ)^10 := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hx : 0 < x := regimeOne_pos_of_six_le (by linarith)
  have hk10 : 2*k ≤ 10 := by omega
  have hk10r : ((2*k : ℕ) : ℝ) ≤ 10 := by exact_mod_cast hk10
  have hqe : ((2*k : ℕ) : ℝ)+6 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hb := abs_thetaCuspNativeScaledEvenJet_sub_first_le_effective k hx hqe
  have hq1 : 1 ≤ q := by dsimp [q]; linarith
  have he0 := (regimeOneLikelihoodScale_pos x).le
  have hp24 : (24 : ℝ)^(2*k) ≤ (24 : ℝ)^10 :=
    pow_le_pow_right₀ (by norm_num) hk10
  have hpq : q^k ≤ q^5 := pow_le_pow_right₀ hq1 hk
  have hprod := mul_le_mul hp24 hpq (pow_nonneg (by linarith : 0 ≤ q) k) (by positivity)
  have hs := mul_le_mul_of_nonneg_right hprod he0
  have hq5 := pow_five_mul_regimeOneLikelihoodScale_le_of_thirty_le hq
  calc
    |thetaCuspNativeScaledEvenJet k x-thetaCuspFirstAtomScaledEvenJet k x| ≤
        27*(24 : ℝ)^(2*k)*q^k*regimeOneLikelihoodScale x := hb
    _ ≤ 27*(24 : ℝ)^10*(q^5*regimeOneLikelihoodScale x) := by nlinarith only [hs]
    _ ≤ 27*(24 : ℝ)^10*(1/(10 : ℝ)^30) :=
      mul_le_mul_of_nonneg_left hq5 (by positivity)
    _ ≤ 1/(10 : ℝ)^10 := by norm_num

end
end RHTower
