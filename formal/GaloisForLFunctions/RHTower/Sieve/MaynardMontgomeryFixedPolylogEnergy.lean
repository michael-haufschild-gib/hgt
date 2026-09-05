import GaloisForLFunctions.RHTower.Sieve.MaynardFixedPolylogSelectedEnergy

/-!
# Fixed-polylog selected energy for the height-crossing Montgomery schedule

The Montgomery schedule raises at most `90` times, rather than Huxley's `51`.  Degree `60` still
makes every coefficient loss fixed: selected width is at most `120`, so the raised dyadic width is
bounded by `2^10800` and the divisor-moment logarithmic exponent is one fixed natural number.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- Uniform width ratio for a degree-`60` selected group raised at most `90` times. -/
def maynardMontgomeryRaisedWidthConstant : ℝ := ((2 ^ 10800 : ℕ) : ℝ)

theorem maynardMontgomeryRaisedWidthConstant_one_le :
    1 ≤ maynardMontgomeryRaisedWidthConstant := by
  dsimp [maynardMontgomeryRaisedWidthConstant]
  exact_mod_cast Nat.one_le_two_pow

/-- Uniform logarithmic exponent for every height-crossing selected energy. -/
def maynardMontgomeryFixedPolylogExponentBound : ℕ :=
  2 * 10800 + (2 ^ (2 * (121 * 90)) - 1)

theorem heathBrownSelected_montgomeryFixedPolylogExponent_le
    {L X : ℕ} (label : HeathBrownSelectionLabel L X 60)
    {ell : ℕ} (hell90 : ell ≤ 90) :
    2 * (Fintype.card (HeathBrownSelectedFactor label) * ell) +
        (2 ^ (2 * ((Fintype.card (HeathBrownSelectedFactor label) + 1) * ell)) - 1) ≤
      maynardMontgomeryFixedPolylogExponentBound := by
  let w : ℕ := Fintype.card (HeathBrownSelectedFactor label)
  have hw : w ≤ 120 := card_heathBrownSelectedFactor_sixty_le label
  have hwe : w * ell ≤ 10800 := by
    calc
      w * ell ≤ 120 * 90 := Nat.mul_le_mul hw hell90
      _ = 10800 := by norm_num
  have hplus : (w + 1) * ell ≤ 121 * 90 :=
    Nat.mul_le_mul (Nat.add_le_add_right hw 1) hell90
  have hdouble : 2 * ((w + 1) * ell) ≤ 2 * (121 * 90) :=
    Nat.mul_le_mul_left 2 hplus
  have hpow : 2 ^ (2 * ((w + 1) * ell)) ≤ 2 ^ (2 * (121 * 90)) :=
    Nat.pow_le_pow_right (by norm_num) hdouble
  have hsub : 2 ^ (2 * ((w + 1) * ell)) - 1 ≤
      2 ^ (2 * (121 * 90)) - 1 := Nat.sub_le_sub_right hpow 1
  dsimp only [maynardMontgomeryFixedPolylogExponentBound]
  change 2 * (w * ell) + (2 ^ (2 * ((w + 1) * ell)) - 1) ≤ _
  exact Nat.add_le_add (Nat.mul_le_mul_left 2 hwe) hsub

attribute [irreducible] maynardMontgomeryFixedPolylogExponentBound

/-- Exact fixed-width transfer from the raised upper edge to the raised lower edge. -/
theorem heathBrownSelected_raisedUpper_le_montgomeryWidth
    {L X : ℕ} (label : HeathBrownSelectionLabel L X 60)
    {ell : ℕ} (hell90 : ell ≤ 90) :
    (((groupedDyadicUpper
        (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ≤
      maynardMontgomeryRaisedWidthConstant *
        (((groupedDyadicLower
          (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) := by
  let w : ℕ := Fintype.card (HeathBrownSelectedFactor label)
  let A : ℕ := groupedDyadicLower (heathBrownSelectedExponent label)
  let M : ℕ := groupedDyadicUpper (heathBrownSelectedExponent label)
  have hw : w ≤ 120 := card_heathBrownSelectedFactor_sixty_le label
  have hwe : w * ell ≤ 10800 := by
    calc
      w * ell ≤ 120 * 90 := Nat.mul_le_mul hw hell90
      _ = 10800 := by norm_num
  have hM : M = A * 2 ^ w := by
    dsimp [M, A, w]
    exact groupedDyadicUpper_eq_lower_mul_twoPow _
  have hn : M ^ ell ≤ 2 ^ 10800 * A ^ ell := by
    rw [hM, mul_pow, ← pow_mul]
    have hp : 2 ^ (w * ell) ≤ 2 ^ 10800 :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) hwe
    calc
      A ^ ell * 2 ^ (w * ell) ≤ A ^ ell * 2 ^ 10800 :=
        Nat.mul_le_mul_left (A ^ ell) hp
      _ = 2 ^ 10800 * A ^ ell := by rw [mul_comm]
  have hn' : ((M ^ ell : ℕ) : ℝ) ≤ ((2 ^ 10800 * A ^ ell : ℕ) : ℝ) := by
    exact_mod_cast hn
  calc
    (((groupedDyadicUpper
        (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) =
        ((M ^ ell : ℕ) : ℝ) := rfl
    _ ≤ ((2 ^ 10800 * A ^ ell : ℕ) : ℝ) := hn'
    _ = maynardMontgomeryRaisedWidthConstant *
        (((groupedDyadicLower
          (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) := by
      rw [Nat.cast_mul]
      rfl

/-- **Lower-edge fixed-polylog energy for the Montgomery height crossing.** -/
theorem heathBrownSelectedRaisedEnergy_le_lower_montgomery_fixed_polylog
    {L X : ℕ} (label : HeathBrownSelectionLabel L X 60)
    (ell : ℕ) (hell : 0 < ell) (hell90 : ell ≤ 90) :
    heathBrownSelectedRaisedEnergy label ell ≤
      maynardMontgomeryRaisedWidthConstant *
        ((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)) *
          (1 + Real.log
            (maynardMontgomeryRaisedWidthConstant *
              ((((groupedDyadicLower
                (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)))) ^
              (2 * (Fintype.card (HeathBrownSelectedFactor label) * ell) +
                (2 ^ (2 * ((Fintype.card
                  (HeathBrownSelectedFactor label) + 1) * ell)) - 1)) := by
  let w : ℕ := Fintype.card (HeathBrownSelectedFactor label)
  let A : ℕ := groupedDyadicLower (heathBrownSelectedExponent label)
  let M : ℕ := groupedDyadicUpper (heathBrownSelectedExponent label)
  let Y : ℝ := ((A ^ ell : ℕ) : ℝ)
  let Z : ℝ := ((M ^ ell : ℕ) : ℝ)
  have hw : w ≤ 120 := card_heathBrownSelectedFactor_sixty_le label
  have hwe : w * ell ≤ 10800 := by
    calc
      w * ell ≤ 120 * 90 := Nat.mul_le_mul hw hell90
      _ = 10800 := by norm_num
  have hM : M = A * 2 ^ w := by
    dsimp [M, A, w]
    exact groupedDyadicUpper_eq_lower_mul_twoPow _
  have hZwidth : Z ≤ maynardMontgomeryRaisedWidthConstant * Y := by
    have hn : M ^ ell ≤ 2 ^ 10800 * A ^ ell := by
      rw [hM, mul_pow, ← pow_mul]
      have hp : 2 ^ (w * ell) ≤ 2 ^ 10800 :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) hwe
      calc
        A ^ ell * 2 ^ (w * ell) ≤ A ^ ell * 2 ^ 10800 :=
          Nat.mul_le_mul_left (A ^ ell) hp
        _ = 2 ^ 10800 * A ^ ell := by rw [mul_comm]
    have hn' : ((M ^ ell : ℕ) : ℝ) ≤ ((2 ^ 10800 * A ^ ell : ℕ) : ℝ) := by
      exact_mod_cast hn
    calc
      Z = ((M ^ ell : ℕ) : ℝ) := rfl
      _ ≤ ((2 ^ 10800 * A ^ ell : ℕ) : ℝ) := hn'
      _ = maynardMontgomeryRaisedWidthConstant * Y := by
        rw [Nat.cast_mul]
        rfl
  have hA1 : 1 ≤ A := one_le_groupedDyadicLower _
  have hY1 : (1 : ℝ) ≤ Y := by
    dsimp [Y]
    exact_mod_cast Nat.one_le_pow ell A hA1
  have hZ1 : (1 : ℝ) ≤ Z := by
    have hM1 : 1 ≤ M := by
      dsimp [M]
      exact one_le_groupedDyadicUpper _
    dsimp [Z]
    exact_mod_cast Nat.one_le_pow ell M hM1
  have hWYpos : 0 < maynardMontgomeryRaisedWidthConstant * Y := by
    exact mul_pos
      (lt_of_lt_of_le zero_lt_one maynardMontgomeryRaisedWidthConstant_one_le)
      (lt_of_lt_of_le zero_lt_one hY1)
  have hlog : 1 + Real.log Z ≤
      1 + Real.log (maynardMontgomeryRaisedWidthConstant * Y) := by
    simpa [add_comm] using
      add_le_add_left (Real.log_le_log (by positivity) hZwidth) 1
  have hlog0 : 0 ≤ 1 + Real.log Z := by
    linarith [Real.log_nonneg hZ1]
  let e : ℕ := 2 * (w * ell) + (2 ^ (2 * ((w + 1) * ell)) - 1)
  have hlogpow : (1 + Real.log Z) ^ e ≤
      (1 + Real.log (maynardMontgomeryRaisedWidthConstant * Y)) ^ e :=
    pow_le_pow_left₀ hlog0 hlog _
  have hraw := heathBrownSelectedRaisedEnergy_le_upper_fixed_polylog label ell hell
  calc
    heathBrownSelectedRaisedEnergy label ell ≤ Z * (1 + Real.log Z) ^ e := by
      simpa [Z, M, e, w] using hraw
    _ ≤ (maynardMontgomeryRaisedWidthConstant * Y) *
        (1 + Real.log (maynardMontgomeryRaisedWidthConstant * Y)) ^ e := by
      exact mul_le_mul hZwidth hlogpow (pow_nonneg hlog0 e) hWYpos.le
    _ = maynardMontgomeryRaisedWidthConstant * Y *
        (1 + Real.log (maynardMontgomeryRaisedWidthConstant * Y)) ^ e := by ring
    _ = _ := by rfl

end RHTower.Sieve
