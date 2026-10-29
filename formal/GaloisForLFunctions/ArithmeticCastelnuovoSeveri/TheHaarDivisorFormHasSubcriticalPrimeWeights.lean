import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHaarPrimeSourceRetainsItsDivisorSquares

/-!
# Subcritical coordinates of the actual Haar divisor form

Dividing the coefficient at the odd boundary `n` by `sqrt n` changes each
prime edge into `Lambda(m) * (n M_n) * (x_parent / m - x_child)^2`.
The exact cell weight is at least one half. Its excess remains a positive
form, including the charge at the absent odd root.
-/

noncomputable section
open Finset

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open ArithmeticFunction BiarithmeticGaugeGeometry

private theorem logCellWidth_ge_midpoint {a : ℕ} (ha : 1 ≤ a) :
    2 / (2 * (a : ℝ) + 1) ≤ logCellWidth a := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < a := by positivity
  have ht0 : 0 ≤ 1 / (2 * (a : ℝ) + 1) := by positivity
  have ht1 : 1 / (2 * (a : ℝ) + 1) < 1 := by
    rw [div_lt_iff₀ (by positivity)]
    linarith only [haR]
  have h := Real.sum_range_le_log_div ht0 ht1 1
  norm_num only [Finset.sum_range_one, Nat.cast_zero, mul_zero, zero_add,
    pow_one, Nat.cast_one, div_one] at h
  have he : (1 + 1 / (2 * (a : ℝ) + 1)) /
      (1 - 1 / (2 * (a : ℝ) + 1)) = ((a : ℝ) + 1) / a := by
    field_simp
    ring
  rw [he, Real.log_div (by positivity) ha0.ne'] at h
  change 2 / (2 * (a : ℝ) + 1) ≤ Real.log ((a : ℝ) + 1) - Real.log a
  simp only [div_eq_mul_inv] at h ⊢
  linarith only [h]

/-- The exact mass dominates the reciprocal midpoint weight. -/
theorem haarMass_ge_midpoint {a : ℕ} (ha : 1 ≤ a) :
    1 / (2 * ((2 * a + 1 : ℕ) : ℝ)) ≤ haarMass a := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hu := logCellWidth_pos (show 1 ≤ 2 * a by omega)
  have hv := logCellWidth_pos (show 1 ≤ 2 * a + 1 by omega)
  have hl := logCellWidth_ge_midpoint (show 1 ≤ 2 * a by omega)
  have hr := logCellWidth_ge_midpoint (show 1 ≤ 2 * a + 1 by omega)
  have hl' : 2 ≤ (4 * (a : ℝ) + 1) * logCellWidth (2 * a) := by
    calc
      2 ≤ logCellWidth (2 * a) * (2 * ((2 * a : ℕ) : ℝ) + 1) :=
        (div_le_iff₀ (by positivity)).mp hl
      _ = _ := by push_cast; ring
  have hr' : 2 ≤ (4 * (a : ℝ) + 3) * logCellWidth (2 * a + 1) := by
    calc
      2 ≤ logCellWidth (2 * a + 1) * (2 * ((2 * a + 1 : ℕ) : ℝ) + 1) :=
        (div_le_iff₀ (by positivity)).mp hr
      _ = _ := by push_cast; ring
  unfold haarMass
  apply (div_le_div_iff₀ (by positivity) (add_pos hu hv)).mpr
  have h₁ := mul_le_mul_of_nonneg_right hl' hv.le
  have h₂ := mul_le_mul_of_nonneg_right hr' hu.le
  push_cast
  nlinarith only [h₁, h₂]

/-- The density relative to inverse-square odd-boundary measure. -/
def haarBoundaryWeight (a : ℕ) : ℝ := ((2 * a + 1 : ℕ) : ℝ) * haarMass a

theorem haarBoundaryWeight_ge_half {a : ℕ} (ha : 1 ≤ a) :
    1 / 2 ≤ haarBoundaryWeight a := by
  have h := mul_le_mul_of_nonneg_left (haarMass_ge_midpoint ha)
    (show (0 : ℝ) ≤ ((2 * a + 1 : ℕ) : ℝ) by positivity)
  have hn : (((2 * a + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  change 1 / 2 ≤ ((2 * a + 1 : ℕ) : ℝ) * haarMass a
  calc
    1 / 2 = ((2 * a + 1 : ℕ) : ℝ) * (1 / (2 * ((2 * a + 1 : ℕ) : ℝ))) := by
      field_simp
    _ ≤ _ := h

/-- Square-summable coordinates for a finite Haar coefficient family. -/
def haarArithmeticCoordinate (d : ℕ → ℝ) (a : ℕ) : ℝ :=
  d a / Real.sqrt ((2 * a + 1 : ℕ) : ℝ)

theorem haarBoundaryWeight_coordinate_sq (d : ℕ → ℝ) (a : ℕ) :
    haarBoundaryWeight a * haarArithmeticCoordinate d a ^ 2 = haarMass a * d a ^ 2 := by
  have hn : (((2 * a + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [haarBoundaryWeight, haarArithmeticCoordinate, div_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)]
  field_simp

private theorem haarEdge_coordinate {a b m : ℕ} (hm : 2 ≤ m)
    (he : (2 * a + 1) * m = 2 * b + 1) (d : ℕ → ℝ) :
    haarMass b * (d a / Real.sqrt m - d b) ^ 2 =
      haarBoundaryWeight b *
        (haarArithmeticCoordinate d a / (m : ℝ) - haarArithmeticCoordinate d b) ^ 2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hna : (0 : ℝ) < ((2 * a + 1 : ℕ) : ℝ) := by positivity
  have hnb : (0 : ℝ) < ((2 * b + 1 : ℕ) : ℝ) := by positivity
  have heR : (((2 * a + 1 : ℕ) : ℝ)) * (m : ℝ) = ((2 * b + 1 : ℕ) : ℝ) :=
    by exact_mod_cast he
  have hs : Real.sqrt ((2 * b + 1 : ℕ) : ℝ) =
      Real.sqrt ((2 * a + 1 : ℕ) : ℝ) * Real.sqrt m := by
    rw [← heR, Real.sqrt_mul hna.le]
  have hsm := Real.sq_sqrt hm0.le
  have hlin : Real.sqrt ((2 * b + 1 : ℕ) : ℝ) *
      (haarArithmeticCoordinate d a / (m : ℝ) - haarArithmeticCoordinate d b) =
        d a / Real.sqrt m - d b := by
    rw [mul_sub, haarArithmeticCoordinate, haarArithmeticCoordinate,
      mul_div_cancel₀ _ (Real.sqrt_pos.mpr hnb).ne']
    congr 1
    rw [hs]
    field_simp [(Real.sqrt_pos.mpr hna).ne', (Real.sqrt_pos.mpr hm0).ne', hm0.ne']
    simp only [hsm, mul_comm]
  rw [← hlin, mul_pow, Real.sq_sqrt hnb.le, haarBoundaryWeight]
  ring

/-- The complete finite divisor graph, including its missing-root charge. -/
def oddDivisorForm (w x : ℕ → ℝ) (X : ℕ) : ℝ :=
  (∑ m ∈ Icc 2 (2 * X + 1), ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
    if (2 * a + 1) * m = 2 * b + 1 then
      vonMangoldt m * w b * (x a / (m : ℝ) - x b) ^ 2 else 0) +
    ∑ a ∈ Icc 1 X, vonMangoldt (2 * a + 1) * w a * x a ^ 2

private theorem oddDivisorForm_nonneg (w x : ℕ → ℝ) (X : ℕ)
    (hw : ∀ a ∈ Icc 1 X, 0 ≤ w a) : 0 ≤ oddDivisorForm w x X := by
  apply add_nonneg
  · apply sum_nonneg
    intro m _
    apply sum_nonneg
    intro a _
    apply sum_nonneg
    intro b hb
    split_ifs
    · exact mul_nonneg (mul_nonneg vonMangoldt_nonneg (hw b hb)) (sq_nonneg _)
    · exact le_rfl
  · exact sum_nonneg fun a ha =>
      mul_nonneg (mul_nonneg vonMangoldt_nonneg (hw a ha)) (sq_nonneg _)

/-- Every original edge and every charged root survive the coordinate change. -/
theorem haarPrimeLogDefect_eq_oddDivisorForm (d : ℕ → ℝ) (X : ℕ) :
    haarPrimeLogDefect d X = oddDivisorForm haarBoundaryWeight
      (haarArithmeticCoordinate d) X := by
  rw [haarPrimeLogDefect_eq, oddDivisorForm]
  congr 1
  · unfold haarPrimeDivisorSquares
    apply sum_congr rfl
    intro m hm
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    split_ifs with he
    · simpa only [mul_assoc] using congrArg (fun y : ℝ => vonMangoldt m * y)
        (haarEdge_coordinate (mem_Icc.mp hm).1 he d)
    · rfl
  · exact sum_congr rfl fun a _ => by
      rw [mul_assoc, mul_assoc, haarBoundaryWeight_coordinate_sq]

/-- The cell-mass excess is a retained nonnegative divisor form. -/
theorem haarPrimeLogDefect_subcritical_decomposition (d : ℕ → ℝ) (X : ℕ) :
    haarPrimeLogDefect d X =
      (1 / 2 : ℝ) * oddDivisorForm (fun _ => 1) (haarArithmeticCoordinate d) X +
        oddDivisorForm (fun a => haarBoundaryWeight a - 1 / 2)
          (haarArithmeticCoordinate d) X := by
  rw [haarPrimeLogDefect_eq_oddDivisorForm]
  simp only [oddDivisorForm, mul_add, mul_sum]
  rw [add_add_add_comm, ← sum_add_distrib, ← sum_add_distrib]
  congr 1
  · apply sum_congr rfl
    intro m _
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro a _
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro b _
    split_ifs <;> ring
  · exact sum_congr rfl fun a _ => by ring

/-- The actual signed source pays the entire subcritical graph energy.
Its positive cell-weight correction is displayed in the preceding identity. -/
theorem haarPrimeLogDefect_ge_subcritical_form (d : ℕ → ℝ) (X : ℕ) :
    (1 / 2 : ℝ) * oddDivisorForm (fun _ => 1) (haarArithmeticCoordinate d) X ≤
      haarPrimeLogDefect d X := by
  rw [haarPrimeLogDefect_subcritical_decomposition]
  exact le_add_of_nonneg_right (oddDivisorForm_nonneg _ _ X fun a ha =>
    sub_nonneg.mpr (haarBoundaryWeight_ge_half (mem_Icc.mp ha).1))

/-- The outgoing inverse-square charge of the finite odd divisor graph. -/
def oddDivisorOutgoing (X a : ℕ) : ℝ :=
  ∑ m ∈ Icc 2 (2 * X + 1), ∑ b ∈ Icc 1 X,
    if (2 * a + 1) * m = 2 * b + 1 then vonMangoldt m / (m : ℝ) ^ 2 else 0

/-- The prime kernel in the unweighted odd-boundary coordinates. -/
def oddSubcriticalPrimeForm (x : ℕ → ℝ) (X : ℕ) : ℝ :=
  ∑ m ∈ Icc 2 (2 * X + 1), ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
    if (2 * a + 1) * m = 2 * b + 1 then
      2 * vonMangoldt m / (m : ℝ) * x a * x b else 0

/-- Incoming divisors give the logarithmic number operator; outgoing edges
retain precisely the inverse-square potential. -/
theorem oddDivisorForm_one_add_prime (x : ℕ → ℝ) (X : ℕ) :
    oddDivisorForm (fun _ => 1) x X + oddSubcriticalPrimeForm x X =
      ∑ a ∈ Icc 1 X,
        (Real.log ((2 * a + 1 : ℕ) : ℝ) + oddDivisorOutgoing X a) * x a ^ 2 := by
  classical
  let Q : ℝ := ∑ m ∈ Icc 2 (2 * X + 1), ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
    if (2 * a + 1) * m = 2 * b + 1 then
      vonMangoldt m * (x a / (m : ℝ) - x b) ^ 2 else 0
  have hsplit : Q + oddSubcriticalPrimeForm x X =
      (∑ m ∈ Icc 2 (2 * X + 1), ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
        if (2 * a + 1) * m = 2 * b + 1 then
          vonMangoldt m / (m : ℝ) ^ 2 * x a ^ 2 else 0) +
      ∑ m ∈ Icc 2 (2 * X + 1), ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
        if (2 * a + 1) * m = 2 * b + 1 then vonMangoldt m * x b ^ 2 else 0 := by
    dsimp only [Q, oddSubcriticalPrimeForm]
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro m _
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro a _
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro b _
    split_ifs <;> ring
  have hout : (∑ m ∈ Icc 2 (2 * X + 1), ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
      if (2 * a + 1) * m = 2 * b + 1 then
        vonMangoldt m / (m : ℝ) ^ 2 * x a ^ 2 else 0) =
        ∑ a ∈ Icc 1 X, oddDivisorOutgoing X a * x a ^ 2 := by
    rw [sum_comm]
    simp only [oddDivisorOutgoing, sum_mul, ite_mul, zero_mul]
  have hin : (∑ m ∈ Icc 2 (2 * X + 1), ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
      if (2 * a + 1) * m = 2 * b + 1 then vonMangoldt m * x b ^ 2 else 0) =
        ∑ b ∈ Icc 1 X,
          (Real.log ((2 * b + 1 : ℕ) : ℝ) - vonMangoldt (2 * b + 1)) * x b ^ 2 := by
    calc
      _ = ∑ m ∈ Icc 2 (2 * X + 1), ∑ b ∈ Icc 1 X, ∑ a ∈ Icc 1 X,
          if (2 * a + 1) * m = 2 * b + 1 then vonMangoldt m * x b ^ 2 else 0 :=
        sum_congr rfl fun _ _ => sum_comm
      _ = ∑ b ∈ Icc 1 X, ∑ m ∈ Icc 2 (2 * X + 1), ∑ a ∈ Icc 1 X,
          if (2 * a + 1) * m = 2 * b + 1 then vonMangoldt m * x b ^ 2 else 0 := sum_comm
      _ = _ := by
        apply sum_congr rfl
        intro b hb
        rw [← haarPrime_incoming_divisor_charge (mem_Icc.mp hb).1 (mem_Icc.mp hb).2]
        simp only [sum_mul, ite_mul, zero_mul]
  have hform : oddDivisorForm (fun _ => 1) x X = Q +
      ∑ a ∈ Icc 1 X, vonMangoldt (2 * a + 1) * x a ^ 2 := by
    simp only [oddDivisorForm, mul_one, Q]
  rw [hout, hin] at hsplit
  rw [hform, add_right_comm, hsplit, ← sum_add_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun _ _ => by ring

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
