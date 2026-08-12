import GaloisForLFunctions.RHTower.Sieve.MaynardFixedPolylogEnergy
import GaloisForLFunctions.RHTower.Sieve.MaynardEnergyReady

/-!
# Fixed-polylog energy of a selected Maynard group

This file specializes fixed divisor moments to the literal selected group in Maynard's degree-60
decomposition.  It also transfers the raised upper length to the lower length through the fixed
width `2^6120`, leaving one explicit polylogarithm and no moving subpower constant.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- One uniform natural exponent dominating every fixed selected-factor energy loss.  It is kept
symbolic: no evaluation of this deliberately large fixed integer is needed. -/
def maynardFixedPolylogExponentBound : ℕ :=
  2 * 6120 + (2 ^ (2 * (121 * 51)) - 1)

/-- Every selected energy exponent is bounded independently of box, label, and raising order. -/
theorem heathBrownSelected_fixedPolylogExponent_le
    {L X : ℕ} (label : HeathBrownSelectionLabel L X 60)
    {ell : ℕ} (hell51 : ell ≤ 51) :
    2 * (Fintype.card (HeathBrownSelectedFactor label) * ell) +
        (2 ^ (2 * ((Fintype.card (HeathBrownSelectedFactor label) + 1) * ell)) - 1) ≤
      maynardFixedPolylogExponentBound := by
  let w : ℕ := Fintype.card (HeathBrownSelectedFactor label)
  have hw : w ≤ 120 := card_heathBrownSelectedFactor_sixty_le label
  have hwe : w * ell ≤ 6120 := by
    calc
      w * ell ≤ 120 * 51 := Nat.mul_le_mul hw hell51
      _ = 6120 := by norm_num
  have hplus : (w + 1) * ell ≤ 121 * 51 :=
    Nat.mul_le_mul (Nat.add_le_add_right hw 1) hell51
  have hdouble : 2 * ((w + 1) * ell) ≤ 2 * (121 * 51) :=
    Nat.mul_le_mul_left 2 hplus
  have hpow : 2 ^ (2 * ((w + 1) * ell)) ≤ 2 ^ (2 * (121 * 51)) :=
    Nat.pow_le_pow_right (by norm_num) hdouble
  have hsub : 2 ^ (2 * ((w + 1) * ell)) - 1 ≤
      2 ^ (2 * (121 * 51)) - 1 := Nat.sub_le_sub_right hpow 1
  dsimp only [maynardFixedPolylogExponentBound]
  change 2 * (w * ell) + (2 ^ (2 * ((w + 1) * ell)) - 1) ≤ _
  exact Nat.add_le_add (Nat.mul_le_mul_left 2 hwe) hsub

attribute [irreducible] maynardFixedPolylogExponentBound

/-- Exact upper-length fixed-polylog energy of a selected group. -/
theorem heathBrownSelectedRaisedEnergy_le_upper_fixed_polylog
    {L X : ℕ} (label : HeathBrownSelectionLabel L X 60)
    (ell : ℕ) (hell : 0 < ell) :
    heathBrownSelectedRaisedEnergy label ell ≤
      ((((groupedDyadicUpper (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)) *
        (1 + Real.log
          ((((groupedDyadicUpper (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ))) ^
            (2 * (Fintype.card (HeathBrownSelectedFactor label) * ell) +
              (2 ^ (2 * ((Fintype.card (HeathBrownSelectedFactor label) + 1) * ell)) - 1)) := by
  simpa [heathBrownSelectedRaisedEnergy] using
    (sum_normSq_convPow_heathBrownGrouped_le_fixed_polylog ell hell
      L X (heathBrownSelectedKind label) (heathBrownSelectedExponent label))

set_option maxHeartbeats 1000000 in
/-- **Selected lower-edge fixed-polylog energy.**  For every permitted raising order, energy is
linear in the raised lower length, up to one fixed-width scalar and a fixed log power. -/
theorem heathBrownSelectedRaisedEnergy_le_lower_fixed_polylog
    {L X : ℕ} (label : HeathBrownSelectionLabel L X 60)
    (ell : ℕ) (hell : 0 < ell) (hell51 : ell ≤ 51) :
    heathBrownSelectedRaisedEnergy label ell ≤
      maynardRaisedWidthConstant *
        ((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)) *
          (1 + Real.log
            (maynardRaisedWidthConstant *
              ((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)))) ^
                (2 * (Fintype.card (HeathBrownSelectedFactor label) * ell) +
                  (2 ^ (2 * ((Fintype.card (HeathBrownSelectedFactor label) + 1) * ell)) - 1)) := by
  let w : ℕ := Fintype.card (HeathBrownSelectedFactor label)
  let A : ℕ := groupedDyadicLower (heathBrownSelectedExponent label)
  let M : ℕ := groupedDyadicUpper (heathBrownSelectedExponent label)
  let Y : ℝ := ((A ^ ell : ℕ) : ℝ)
  let Z : ℝ := ((M ^ ell : ℕ) : ℝ)
  have hw : w ≤ 120 := card_heathBrownSelectedFactor_sixty_le label
  have hwe : w * ell ≤ 6120 := by
    calc
      w * ell ≤ 120 * 51 := Nat.mul_le_mul hw hell51
      _ = 6120 := by norm_num
  have hM : M = A * 2 ^ w := by
    dsimp [M, A, w]
    exact groupedDyadicUpper_eq_lower_mul_twoPow _
  have hZwidth : Z ≤ maynardRaisedWidthConstant * Y := by
    have hn : M ^ ell ≤ 2 ^ 6120 * A ^ ell := by
      rw [hM, mul_pow, ← pow_mul]
      have hp : 2 ^ (w * ell) ≤ 2 ^ 6120 :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) hwe
      calc
        A ^ ell * 2 ^ (w * ell) ≤ A ^ ell * 2 ^ 6120 :=
          Nat.mul_le_mul_left (A ^ ell) hp
        _ = 2 ^ 6120 * A ^ ell := by rw [mul_comm]
    have hn' : ((M ^ ell : ℕ) : ℝ) ≤ ((2 ^ 6120 * A ^ ell : ℕ) : ℝ) := by
      exact_mod_cast hn
    calc
      Z = ((M ^ ell : ℕ) : ℝ) := rfl
      _ ≤ ((2 ^ 6120 * A ^ ell : ℕ) : ℝ) := hn'
      _ = maynardRaisedWidthConstant * Y := by
        rw [Nat.cast_mul]
        rfl
  have hA1 : 1 ≤ A := one_le_groupedDyadicLower _
  have hY1 : (1 : ℝ) ≤ Y := by
    dsimp [Y]
    exact_mod_cast Nat.one_le_pow ell A (by omega)
  have hZ1 : (1 : ℝ) ≤ Z := by
    have hM1 : 1 ≤ M := by
      dsimp [M]
      exact one_le_groupedDyadicUpper _
    dsimp [Z]
    exact_mod_cast Nat.one_le_pow ell M (by omega)
  have hWYpos : 0 < maynardRaisedWidthConstant * Y := by
    exact mul_pos (lt_of_lt_of_le zero_lt_one maynardRaisedWidthConstant_one_le)
      (lt_of_lt_of_le zero_lt_one hY1)
  have hlog : 1 + Real.log Z ≤
      1 + Real.log (maynardRaisedWidthConstant * Y) := by
    simpa [add_comm] using add_le_add_left (Real.log_le_log (by positivity) hZwidth) 1
  have hlog0 : 0 ≤ 1 + Real.log Z := by
    have := Real.log_nonneg hZ1
    linarith
  let e : ℕ := 2 * (w * ell) + (2 ^ (2 * ((w + 1) * ell)) - 1)
  have hlogpow : (1 + Real.log Z) ^ e ≤
      (1 + Real.log (maynardRaisedWidthConstant * Y)) ^ e :=
    pow_le_pow_left₀ hlog0 hlog _
  have hraw := heathBrownSelectedRaisedEnergy_le_upper_fixed_polylog
    label ell hell
  calc
    heathBrownSelectedRaisedEnergy label ell
        ≤ Z * (1 + Real.log Z) ^ e := by
          simpa [Z, M, e, w] using hraw
    _ ≤ (maynardRaisedWidthConstant * Y) *
        (1 + Real.log (maynardRaisedWidthConstant * Y)) ^ e := by
          exact mul_le_mul hZwidth hlogpow (pow_nonneg hlog0 e) hWYpos.le
    _ = maynardRaisedWidthConstant * Y *
        (1 + Real.log (maynardRaisedWidthConstant * Y)) ^ e := by ring
    _ = _ := by rfl

end RHTower.Sieve
