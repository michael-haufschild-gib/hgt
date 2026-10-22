import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspEffectiveTailScale

/-! # Effective complete-source accuracy for every even rank-four entry -/
namespace RHTower
noncomputable section

/-- The calibrated scale-thirty likelihood tail absorbs the sixth Gaussian power. -/
theorem pow_six_mul_regimeOneLikelihoodScale_le_of_thirty_le {x : ℝ}
    (hq : 30 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspSingleAtomReflectionScale 1 x^(6 : ℕ)*regimeOneLikelihoodScale x ≤ 3/(10 : ℝ)^(29 : ℕ) := by
  have h := pow_mul_regimeOneLikelihoodScale_le (k := 6) (A₁ := 30)
    (by norm_num) (by norm_num) hq
  calc
    _ ≤ (30 : ℝ)^(6 : ℕ)*(Real.exp (3*Real.pi)/399*Real.exp (-(3*(30 : ℝ)))) := h
    _ ≤ (30 : ℝ)^(6 : ℕ)*(32/(10 : ℝ)^(39 : ℕ)) :=
      mul_le_mul_of_nonneg_left base_scale_thirty_le (by positivity)
    _ ≤ _ := by norm_num

/-- Every one of the seven actual signed moments is within ten to the minus ten of its first atom. -/
theorem abs_thetaCuspNativeScaledEvenJet_sub_first_le_ten_neg_ten_six
    {k : ℕ} (hk : k ≤ 6) {x : ℝ}
    (hq : 30 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspNativeScaledEvenJet k x-thetaCuspFirstAtomScaledEvenJet k x| ≤ 1/(10 : ℝ)^(10 : ℕ) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hx : 0 < x := regimeOne_pos_of_six_le (by linarith)
  have hk12 : 2*k ≤ 12 := by omega
  have hk12r : ((2*k : ℕ) : ℝ) ≤ 12 := by exact_mod_cast hk12
  have hqe : ((2*k : ℕ) : ℝ)+6 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hb := abs_thetaCuspNativeScaledEvenJet_sub_first_le_effective k hx hqe
  have hq1 : 1 ≤ q := by dsimp [q]; linarith
  have he0 := (regimeOneLikelihoodScale_pos x).le
  have hp24 : (24 : ℝ)^(2*k) ≤ (24 : ℝ)^(12 : ℕ) :=
    pow_le_pow_right₀ (by norm_num) hk12
  have hpq : q^k ≤ q^(6 : ℕ) := pow_le_pow_right₀ hq1 hk
  have hprod := mul_le_mul hp24 hpq (pow_nonneg (by linarith : 0 ≤ q) k) (by positivity)
  have hs := mul_le_mul_of_nonneg_right hprod he0
  have hq6 := pow_six_mul_regimeOneLikelihoodScale_le_of_thirty_le hq
  calc
    _ ≤ 27*(24 : ℝ)^(2*k)*q^k*regimeOneLikelihoodScale x := hb
    _ ≤ 27*(24 : ℝ)^(12 : ℕ)*(q^(6 : ℕ)*regimeOneLikelihoodScale x) := by nlinarith only [hs]
    _ ≤ 27*(24 : ℝ)^(12 : ℕ)*(3/(10 : ℝ)^(29 : ℕ)) :=
      mul_le_mul_of_nonneg_left hq6 (by positivity)
    _ ≤ 1/(10 : ℝ)^(10 : ℕ) := by norm_num

end
end RHTower
