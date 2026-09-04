import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownCaseIIAbsorptionSchedule

namespace RHTower.Sieve

noncomputable section

open Filter

def menonHeathBrownCaseIIOrderFourHundredAbsorptionConstant : ℝ :=
  24 * 21 ^ (7 : ℕ) * 8 ^ (400 : ℕ)

theorem eventually_menonHeathBrownCaseIIAbsorptionEnvelope_fourHundred_lt_logPow_of_polynomial_support :
    ∀ᶠ a : ℕ in atTop, ∀ {L X : ℕ},
      1 ≤ L → 1 ≤ X → L ≤ X → (X : ℝ) ≤ (a : ℝ) ^ (3 : ℕ) →
      menonHeathBrownCaseIIAbsorptionEnvelope 400 L X a <
        (Real.log (a : ℝ)) ^ (-300 : ℝ) := by
  have hlog : Tendsto (fun a : ℕ => Real.log (a : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_gt_atTop
    (max 1 menonHeathBrownCaseIIOrderFourHundredAbsorptionConstant)] with a hlarge
  intro L X hL hX hLX hXa
  let la : ℝ := Real.log (a : ℝ)
  have hla1 : 1 < la := lt_of_le_of_lt (le_max_left _ _) hlarge
  have hla0 : 0 < la := zero_lt_one.trans hla1
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := by
    have : 1 < (a : ℝ) :=
      (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ (a : ℝ))).mp
        (by simpa only [la] using hla0)
    exact this.le
  have hlogX : Real.log (X : ℝ) ≤ 3 * la := by
    have hmono := Real.log_le_log (by positivity : 0 < (X : ℝ)) hXa
    rw [Real.log_pow] at hmono
    simpa only [la, Nat.cast_ofNat] using hmono
  have hlogL : Real.log (L : ℝ) ≤ 3 * la := by
    exact (Real.log_le_log (by positivity : 0 < (L : ℝ)) (by exact_mod_cast hLX)).trans hlogX
  have hlogCountX : ((Nat.log 2 X + 1 : ℕ) : ℝ) ≤ 21 * la := by
    calc
      ((Nat.log 2 X + 1 : ℕ) : ℝ) ≤ 1 + 2 * Real.log X :=
        natLogTwo_add_one_cast_le hX
      _ ≤ 21 * la := by dsimp only [la] at hlogX ⊢; nlinarith
  have hlogCountL : ((Nat.log 2 L + 1 : ℕ) : ℝ) ≤ 21 * la := by
    calc
      ((Nat.log 2 L + 1 : ℕ) : ℝ) ≤ 1 + 2 * Real.log L :=
        natLogTwo_add_one_cast_le hL
      _ ≤ 21 * la := by dsimp only [la] at hlogL ⊢; nlinarith
  have hcard : (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) ≤
      3 * (21 * la) ^ (6 : ℕ) := by
    have hcardNat := card_heathBrownBoxChoice_le L X 3
    have hcardCast : (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) ≤
        (3 : ℝ) * (((Nat.log 2 X + 1 : ℕ) : ℝ)) ^ (3 : ℕ) *
          (((Nat.log 2 L + 1 : ℕ) : ℝ)) ^ (3 : ℕ) := by
      exact_mod_cast hcardNat
    calc
      (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) ≤
          (3 : ℝ) * (((Nat.log 2 X + 1 : ℕ) : ℝ)) ^ (3 : ℕ) *
            (((Nat.log 2 L + 1 : ℕ) : ℝ)) ^ (3 : ℕ) := hcardCast
      _ ≤ 3 * (21 * la) ^ (3 : ℕ) * (21 * la) ^ (3 : ℕ) := by gcongr
      _ = 3 * (21 * la) ^ (6 : ℕ) := by ring
  have haCube : (1 : ℝ) ≤ (a : ℝ) ^ (3 : ℕ) := one_le_pow₀ ha1
  have henv : maynardLongPolylogEnvelope X ≤ 21 * la := by
    have harg : (((2 * (X + 1) : ℕ) : ℝ)) ≤ 4 * (a : ℝ) ^ (3 : ℕ) := by
      push_cast
      nlinarith
    have hlogArg := Real.log_le_log (by positivity :
      0 < (((2 * (X + 1) : ℕ) : ℝ))) harg
    have hlog4 : Real.log 4 ≤ 3 := by
      have hraw := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
      norm_num at hraw ⊢
      exact hraw
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by positivity),
      Real.log_pow] at hlogArg
    rw [maynardLongPolylogEnvelope]
    change Real.log (((2 * (X + 1) : ℕ) : ℝ)) ≤ Real.log 4 + 3 * la at hlogArg
    nlinarith
  have hrootLog : Real.log ((a : ℝ) ^ (1 / 8 : ℝ)) = la / 8 := by
    rw [Real.log_rpow (by positivity : 0 < (a : ℝ))]
    dsimp only [la]
    ring
  have hmajor : menonHeathBrownCaseIIAbsorptionEnvelope 400 L X a ≤
      menonHeathBrownCaseIIOrderFourHundredAbsorptionConstant / la ^ (393 : ℕ) := by
    rw [menonHeathBrownCaseIIAbsorptionEnvelope, hrootLog]
    have hroot0 : 0 < la / 8 := by positivity
    have henv0 : 0 ≤ maynardLongPolylogEnvelope X :=
      (one_le_maynardLongPolylogEnvelope X).trans' zero_le_one
    rw [Real.rpow_neg hroot0.le]
    rw [show (la / 8) ^ (400 : ℝ) = (la / 8) ^ (400 : ℕ) by
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast (la / 8) 400]
    calc
      (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) * 8 *
          (((la / 8) ^ (400 : ℕ))⁻¹ * maynardLongPolylogEnvelope X)
          ≤ (3 * (21 * la) ^ (6 : ℕ)) * 8 *
              (((la / 8) ^ (400 : ℕ))⁻¹ * (21 * la)) := by gcongr
      _ = menonHeathBrownCaseIIOrderFourHundredAbsorptionConstant / la ^ (393 : ℕ) := by
        rw [menonHeathBrownCaseIIOrderFourHundredAbsorptionConstant]
        field_simp [ne_of_gt hla0]
        ring
  have hconst : menonHeathBrownCaseIIOrderFourHundredAbsorptionConstant < la :=
    lt_of_le_of_lt (le_max_right _ _) hlarge
  have hconst13 : menonHeathBrownCaseIIOrderFourHundredAbsorptionConstant < la ^ (93 : ℕ) := by
    calc
      menonHeathBrownCaseIIOrderFourHundredAbsorptionConstant < la := hconst
      _ ≤ la ^ (93 : ℕ) := by
        simpa only [pow_one] using
          (pow_le_pow_right₀ hla1.le (by norm_num : 1 ≤ 93))
  have htarget : menonHeathBrownCaseIIOrderFourHundredAbsorptionConstant / la ^ (393 : ℕ) <
      la ^ (-300 : ℝ) := by
    rw [Real.rpow_neg hla0.le]
    rw [show la ^ (300 : ℝ) = la ^ (300 : ℕ) by
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast la 300]
    rw [inv_eq_one_div, div_lt_div_iff₀ (pow_pos hla0 393) (pow_pos hla0 300)]
    calc
      menonHeathBrownCaseIIOrderFourHundredAbsorptionConstant * la ^ (300 : ℕ) <
          la ^ (93 : ℕ) * la ^ (300 : ℕ) :=
        mul_lt_mul_of_pos_right hconst13 (pow_pos hla0 300)
      _ = 1 * la ^ (393 : ℕ) := by ring
  exact hmajor.trans_lt htarget

end

end RHTower.Sieve

