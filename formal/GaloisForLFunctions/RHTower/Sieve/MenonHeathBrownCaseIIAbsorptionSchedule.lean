import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownCaseIIAbsorption

/-!
# Paper-scale Case-II scalar absorption

On Menon's degree-three support, `X < (L+1)^(3 : ℕ)` and `L <= a^(1/3)` make every label cost a fixed
seventh power of `log a`.  The order-sixteen Möbius saving therefore places the uniform absorption
envelope below `(log a)^(-8)` for every sufficiently large `a`, uniformly in admissible `L,X`.
-/

namespace RHTower.Sieve

noncomputable section

open Filter

/-- Explicit constant in the uniform degree-three logarithmic envelope. -/
def menonHeathBrownCaseIIAbsorptionConstant : ℝ :=
  24 * 21 ^ (7 : ℕ) * 8 ^ (16 : ℕ)

/-- Menon's order-sixteen logarithmic saving absorbs every active Case-II label at the canonical
`(log a)^(-8)` threshold, uniformly over the paper's support scales. -/
theorem eventually_menonHeathBrownCaseIIAbsorptionEnvelope_lt_logPow :
    ∀ᶠ a : ℕ in atTop, ∀ {L X : ℕ},
      1 ≤ L → 1 ≤ X → a < X → X < (L + 1) ^ 3 →
      (L : ℝ) ≤ (a : ℝ) ^ (1 / 3 : ℝ) →
      menonHeathBrownCaseIIAbsorptionEnvelope 16 L X a <
        (Real.log (a : ℝ)) ^ (-8 : ℝ) := by
  have hlog : Tendsto (fun a : ℕ => Real.log (a : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_gt_atTop
    (max 1 menonHeathBrownCaseIIAbsorptionConstant)] with a hlarge
  intro L X hL hX haX hXL hcut
  let la : ℝ := Real.log (a : ℝ)
  have hla1 : 1 < la := lt_of_le_of_lt (le_max_left _ _) hlarge
  have hla0 : 0 < la := zero_lt_one.trans hla1
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := by
    have : 1 < (a : ℝ) :=
      (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ (a : ℝ))).mp
        (by simpa only [la] using hla0)
    exact this.le
  have hLleA : (L : ℝ) ≤ (a : ℝ) :=
    hcut.trans (Real.rpow_le_self_of_one_le ha1 (by norm_num))
  have hXle : (X : ℝ) ≤ 8 * (a : ℝ) ^ (3 : ℕ) := by
    have hcast : (X : ℝ) ≤ ((L + 1 : ℕ) : ℝ) ^ (3 : ℕ) := by
      exact_mod_cast (Nat.le_of_lt hXL)
    calc
      (X : ℝ) ≤ ((L + 1 : ℕ) : ℝ) ^ (3 : ℕ) := hcast
      _ = ((L : ℝ) + 1) ^ (3 : ℕ) := by push_cast; rfl
      _ ≤ (2 * (a : ℝ)) ^ (3 : ℕ) := by
        gcongr
        nlinarith
      _ = 8 * (a : ℝ) ^ (3 : ℕ) := by ring
  have hlogX : Real.log (X : ℝ) ≤ 10 * la := by
    have hlogMono := Real.log_le_log (by positivity : 0 < (X : ℝ)) hXle
    have hlog8 : Real.log 8 ≤ 7 := by
      have hraw := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
      norm_num at hraw ⊢
      exact hraw
    rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (by positivity),
      Real.log_pow] at hlogMono
    change Real.log (X : ℝ) ≤ Real.log 8 + 3 * la at hlogMono
    nlinarith
  have hlogL : Real.log (L : ℝ) ≤ 10 * la := by
    have hLX : L ≤ X := by
      have hLa : L ≤ a := by exact_mod_cast hLleA
      exact hLa.trans (Nat.le_of_lt haX)
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
  have henv : maynardLongPolylogEnvelope X ≤ 21 * la := by
    have haCube : (1 : ℝ) ≤ (a : ℝ) ^ (3 : ℕ) := one_le_pow₀ ha1
    have harg : (((2 * (X + 1) : ℕ) : ℝ)) ≤ 18 * (a : ℝ) ^ (3 : ℕ) := by
      push_cast
      nlinarith [hXle, haCube]
    have hlogArg := Real.log_le_log (by positivity :
      0 < (((2 * (X + 1) : ℕ) : ℝ))) harg
    have hlog18 : Real.log 18 ≤ 17 := by
      have hraw := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 18)
      norm_num at hraw ⊢
      exact hraw
    rw [Real.log_mul (by norm_num : (18 : ℝ) ≠ 0) (by positivity),
      Real.log_pow] at hlogArg
    rw [maynardLongPolylogEnvelope]
    change Real.log (((2 * (X + 1) : ℕ) : ℝ)) ≤ Real.log 18 + 3 * la at hlogArg
    nlinarith
  have hrootLog : Real.log ((a : ℝ) ^ (1 / 8 : ℝ)) = la / 8 := by
    rw [Real.log_rpow (by positivity : 0 < (a : ℝ))]
    dsimp only [la]
    ring
  have hmajor : menonHeathBrownCaseIIAbsorptionEnvelope 16 L X a ≤
      menonHeathBrownCaseIIAbsorptionConstant / la ^ (9 : ℕ) := by
    rw [menonHeathBrownCaseIIAbsorptionEnvelope, hrootLog]
    have hroot0 : 0 < la / 8 := by positivity
    have henv0 : 0 ≤ maynardLongPolylogEnvelope X :=
      (one_le_maynardLongPolylogEnvelope X).trans' zero_le_one
    rw [Real.rpow_neg hroot0.le]
    rw [show (la / 8) ^ (16 : ℝ) = (la / 8) ^ (16 : ℕ) by
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast (la / 8) 16]
    calc
      (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) * 8 *
          (((la / 8) ^ (16 : ℕ))⁻¹ * maynardLongPolylogEnvelope X)
          ≤ (3 * (21 * la) ^ (6 : ℕ)) * 8 *
              (((la / 8) ^ (16 : ℕ))⁻¹ * (21 * la)) := by gcongr
      _ = menonHeathBrownCaseIIAbsorptionConstant / la ^ (9 : ℕ) := by
        rw [menonHeathBrownCaseIIAbsorptionConstant]
        field_simp [ne_of_gt hla0]
        ring
  have hconst : menonHeathBrownCaseIIAbsorptionConstant < la :=
    lt_of_le_of_lt (le_max_right _ _) hlarge
  have htarget : menonHeathBrownCaseIIAbsorptionConstant / la ^ (9 : ℕ) <
      la ^ (-8 : ℝ) := by
    rw [Real.rpow_neg hla0.le]
    rw [show la ^ (8 : ℝ) = la ^ (8 : ℕ) by
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast la 8]
    rw [inv_eq_one_div, div_lt_div_iff₀ (pow_pos hla0 9) (pow_pos hla0 8)]
    calc
      menonHeathBrownCaseIIAbsorptionConstant * la ^ (8 : ℕ) <
          la * la ^ (8 : ℕ) := mul_lt_mul_of_pos_right hconst (pow_pos hla0 8)
      _ = 1 * la ^ (9 : ℕ) := by ring
  exact hmajor.trans_lt htarget

/-- The same order-sixteen absorption is uniform when the Heath--Brown cutoff and ambient support
are only polynomially bounded by the selected prime-block lower endpoint.  This is the actual
final-range regime: `L ≤ X ≤ a^(3 : ℕ)`, with no false requirement `L ≤ a^(1/3)`. -/
theorem eventually_menonHeathBrownCaseIIAbsorptionEnvelope_lt_logPow_of_polynomial_support :
    ∀ᶠ a : ℕ in atTop, ∀ {L X : ℕ},
      1 ≤ L → 1 ≤ X → L ≤ X → (X : ℝ) ≤ (a : ℝ) ^ (3 : ℕ) →
      menonHeathBrownCaseIIAbsorptionEnvelope 16 L X a <
        (Real.log (a : ℝ)) ^ (-8 : ℝ) := by
  have hlog : Tendsto (fun a : ℕ => Real.log (a : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_gt_atTop
    (max 1 menonHeathBrownCaseIIAbsorptionConstant)] with a hlarge
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
  have hmajor : menonHeathBrownCaseIIAbsorptionEnvelope 16 L X a ≤
      menonHeathBrownCaseIIAbsorptionConstant / la ^ (9 : ℕ) := by
    rw [menonHeathBrownCaseIIAbsorptionEnvelope, hrootLog]
    have hroot0 : 0 < la / 8 := by positivity
    have henv0 : 0 ≤ maynardLongPolylogEnvelope X :=
      (one_le_maynardLongPolylogEnvelope X).trans' zero_le_one
    rw [Real.rpow_neg hroot0.le]
    rw [show (la / 8) ^ (16 : ℝ) = (la / 8) ^ (16 : ℕ) by
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast (la / 8) 16]
    calc
      (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) * 8 *
          (((la / 8) ^ (16 : ℕ))⁻¹ * maynardLongPolylogEnvelope X)
          ≤ (3 * (21 * la) ^ (6 : ℕ)) * 8 *
              (((la / 8) ^ (16 : ℕ))⁻¹ * (21 * la)) := by gcongr
      _ = menonHeathBrownCaseIIAbsorptionConstant / la ^ (9 : ℕ) := by
        rw [menonHeathBrownCaseIIAbsorptionConstant]
        field_simp [ne_of_gt hla0]
        ring
  have hconst : menonHeathBrownCaseIIAbsorptionConstant < la :=
    lt_of_le_of_lt (le_max_right _ _) hlarge
  have htarget : menonHeathBrownCaseIIAbsorptionConstant / la ^ (9 : ℕ) <
      la ^ (-8 : ℝ) := by
    rw [Real.rpow_neg hla0.le]
    rw [show la ^ (8 : ℝ) = la ^ (8 : ℕ) by
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast la 8]
    rw [inv_eq_one_div, div_lt_div_iff₀ (pow_pos hla0 9) (pow_pos hla0 8)]
    calc
      menonHeathBrownCaseIIAbsorptionConstant * la ^ (8 : ℕ) <
          la * la ^ (8 : ℕ) := mul_lt_mul_of_pos_right hconst (pow_pos hla0 8)
      _ = 1 * la ^ (9 : ℕ) := by ring
  exact hmajor.trans_lt htarget

end

end RHTower.Sieve
