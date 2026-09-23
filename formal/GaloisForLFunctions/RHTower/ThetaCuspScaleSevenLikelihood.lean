import GaloisForLFunctions.RHTower.ThetaCuspSharpFiniteCooling

/-! # Explicit polynomially weighted likelihood error on the scale-seven ray -/
namespace RHTower
noncomputable section

/-- Exact exponential comparison at the effective scale-seven endpoint. -/
theorem base_scale_seven_le :
    Real.exp (3*Real.pi)/399*Real.exp (-(3*(7 : ℝ))) ≤ 32/1300000000 := by
  have h1 : (2718/1000 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h21 : (1300000000 : ℝ) ≤ Real.exp 21 := by
    have h := pow_le_pow_left₀ (by norm_num) h1 21
    rw [← Real.exp_nat_mul] at h
    norm_num at h ⊢
    linarith
  rw [show -(3*(7 : ℝ)) = -21 by norm_num, Real.exp_neg]
  rw [show Real.exp (3*Real.pi)/399*(Real.exp 21)⁻¹ =
    Real.exp (3*Real.pi)/(399*Real.exp 21) by field_simp]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 399*Real.exp 21)).mpr
  nlinarith [exp_three_pi_lt_12704]

/-- Each polynomial weight required by the reflected tenth jet has an explicit endpoint ceiling. -/
theorem pow_mul_regimeOneLikelihoodScale_le_of_seven_le {k : ℕ} (hk : k ≤ 5) {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspSingleAtomReflectionScale 1 x^k*regimeOneLikelihoodScale x ≤
      (7 : ℝ)^k*(32/1300000000) := by
  have hkr : (k : ℝ) ≤ 5 := by exact_mod_cast hk
  have h := pow_mul_regimeOneLikelihoodScale_le (k := k) (A₁ := 7)
    (by norm_num) (by linarith) hq
  exact h.trans (mul_le_mul_of_nonneg_left base_scale_seven_le (by positivity))

/-- The quadratic likelihood error has the same explicit endpoint control. -/
theorem pow_mul_regimeOneLikelihoodScale_sq_le_of_seven_le {k : ℕ} (hk : k ≤ 5) {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspSingleAtomReflectionScale 1 x^k*regimeOneLikelihoodScale x^(2 : ℕ) ≤
      (7 : ℝ)^k*(32/1300000000)^(2 : ℕ) := by
  have h1 := pow_mul_regimeOneLikelihoodScale_le_of_seven_le hk hq
  have h0 := pow_mul_regimeOneLikelihoodScale_le_of_seven_le (k := 0) (by omega) hq
  simp only [pow_zero, one_mul] at h0
  have hm := mul_le_mul h1 h0 (regimeOneLikelihoodScale_pos x).le (by positivity)
  nlinarith only [hm]

end
end RHTower
