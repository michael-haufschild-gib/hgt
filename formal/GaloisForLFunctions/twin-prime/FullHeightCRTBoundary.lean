import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# The full-height CRT kernel

When both divisors exceed half the physical horizon by two, the
simultaneous-divisor kernel is exactly the gap-two shift. An explicit
odd block has a linear discrepancy from its compatible period mean.
-/

namespace TwinPrime

open Finset

noncomputable section

/-- The literal gap-two incidence count on the physical interval. -/
def physicalCrtCount (X d e : ℕ) : ℕ :=
  ((Icc 2 X).filter fun n => d ∣ n ∧ e ∣ n + 2).card

/-- Divisors for which both complementary quotients must equal one. -/
def upperHalfDivisorCarrier (X : ℕ) : Finset ℕ := Icc (X / 2 + 2) X

private theorem large_divisor_eq {a b : ℕ} (hb : 0 < b) (hab : a ∣ b)
    (hba : b < 2 * a) : b = a := by
  obtain ⟨k, rfl⟩ := hab
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp only [mul_zero, Nat.lt_irrefl] at hb
  have hk2 : ¬ 2 ≤ k := by
    intro hk
    have hmul := Nat.mul_le_mul_left a hk
    omega
  have hk : k = 1 := by omega
  simp only [hk, mul_one]

private theorem physicalCrtCount_upper (X d e : ℕ)
    (hd : d ∈ upperHalfDivisorCarrier X) (he : e ∈ upperHalfDivisorCarrier X) :
    physicalCrtCount X d e = if e = d + 2 then 1 else 0 := by
  have hdI := mem_Icc.mp hd
  have heI := mem_Icc.mp he
  have hfilter : (Icc 2 X).filter (fun n => d ∣ n ∧ e ∣ n + 2) =
      if e = d + 2 then {d} else ∅ := by
    by_cases heq : e = d + 2
    · rw [if_pos heq]
      ext n
      simp only [mem_filter, mem_Icc, mem_singleton]
      constructor
      · rintro ⟨⟨hn2, hnX⟩, hdn, _⟩
        exact large_divisor_eq (by omega) hdn (by omega)
      · intro hnd
        subst n
        exact ⟨⟨by omega, hdI.2⟩, dvd_refl d, by simpa only [heq] using dvd_refl (d + 2)⟩
    · rw [if_neg heq]
      ext n
      simp only [mem_filter]
      constructor
      · rintro ⟨hnI, hdn, hen⟩
        obtain ⟨hn2, hnX⟩ := mem_Icc.mp hnI
        have hnd : n = d := large_divisor_eq (by omega) hdn (by omega)
        have hne : n + 2 = e := large_divisor_eq (by omega) hen (by omega)
        exact False.elim (heq (by omega))
      · simp
  rw [physicalCrtCount, hfilter]
  split_ifs <;> simp only [card_singleton, card_empty]

/-- The incidence kernel restricted to the full-height divisor carrier. -/
def upperHalfCrtKernel (X d e : ℕ) : ℕ :=
  if d ∈ upperHalfDivisorCarrier X ∧ e ∈ upperHalfDivisorCarrier X then
    physicalCrtCount X d e else 0

/-- The full-height kernel is exactly the shift, including every empty-carrier case. -/
theorem upperHalfCrtKernel_eq_shift (X d e : ℕ) :
    upperHalfCrtKernel X d e =
      if d ∈ upperHalfDivisorCarrier X ∧ e ∈ upperHalfDivisorCarrier X ∧ e = d + 2
      then 1 else 0 := by
  by_cases hd : d ∈ upperHalfDivisorCarrier X
  · by_cases he : e ∈ upperHalfDivisorCarrier X
    · simp only [upperHalfCrtKernel, hd, he, and_self, if_true, true_and,
        physicalCrtCount_upper X d e hd he]
    · simp only [upperHalfCrtKernel, hd, he, and_false, false_and, if_false]
  · simp only [upperHalfCrtKernel, hd, false_and, if_false]

/-- Every full-height bilinear test is its literal shifted scalar correlation. -/
theorem upperHalfCrtForm_eq_shift (X : ℕ) (a b : ℕ → ℝ) :
    (∑ d ∈ upperHalfDivisorCarrier X, ∑ e ∈ upperHalfDivisorCarrier X,
      a d * b e * physicalCrtCount X d e) =
      ∑ d ∈ upperHalfDivisorCarrier X,
        if d + 2 ∈ upperHalfDivisorCarrier X then a d * b (d + 2) else 0 := by
  apply sum_congr rfl
  intro d hd
  calc
    _ = ∑ e ∈ upperHalfDivisorCarrier X, if e = d + 2 then a d * b e else 0 := by
      apply sum_congr rfl
      intro e he
      rw [physicalCrtCount_upper X d e hd he]
      split_ifs <;> simp only [Nat.cast_one, Nat.cast_zero, mul_one, mul_zero]
    _ = _ := by rw [sum_ite_eq']

/-- A uniform parametrization of the odd full-height block. -/
def fullHeightOddDivisor (T i : ℕ) : ℕ := 4 * T + 3 + 2 * i

theorem fullHeightOddDivisor_odd (T i : ℕ) : Odd (fullHeightOddDivisor T i) := by
  refine ⟨2 * T + 1 + i, ?_⟩
  unfold fullHeightOddDivisor
  ring

/-- The exact discrepancy from the compatible odd period mean. -/
def fullHeightOddCrtDefect (T : ℕ) : ℝ :=
  ∑ i ∈ range (2 * T), ∑ j ∈ range (2 * T),
    ((physicalCrtCount (8 * T + 2) (fullHeightOddDivisor T i)
        (fullHeightOddDivisor T j) : ℝ) -
      (8 * (T : ℝ) + 1) *
        (if (fullHeightOddDivisor T i).Coprime (fullHeightOddDivisor T j) then
          1 / ((fullHeightOddDivisor T i : ℝ) * (fullHeightOddDivisor T j : ℝ)) else 0))

private theorem fullHeightOddDivisor_mem (T i : ℕ) (hi : i < 2 * T) :
    fullHeightOddDivisor T i ∈ upperHalfDivisorCarrier (8 * T + 2) := by
  simp only [upperHalfDivisorCarrier, mem_Icc, fullHeightOddDivisor]
  omega

private theorem fullHeightOddIncidence (T i j : ℕ) (hi : i < 2 * T) (hj : j < 2 * T) :
    physicalCrtCount (8 * T + 2) (fullHeightOddDivisor T i) (fullHeightOddDivisor T j) =
      if j = i + 1 then 1 else 0 := by
  rw [physicalCrtCount_upper _ _ _ (fullHeightOddDivisor_mem T i hi)
    (fullHeightOddDivisor_mem T j hj)]
  have he : fullHeightOddDivisor T j = fullHeightOddDivisor T i + 2 ↔ j = i + 1 := by
    unfold fullHeightOddDivisor
    omega
  simp only [he]

private theorem fullHeightOddIncidence_sum (T : ℕ) (hT : 0 < T) :
    (∑ i ∈ range (2 * T), ∑ j ∈ range (2 * T),
      (physicalCrtCount (8 * T + 2) (fullHeightOddDivisor T i)
        (fullHeightOddDivisor T j) : ℝ)) = 2 * (T : ℝ) - 1 := by
  have hsum : (∑ i ∈ range (2 * T - 1), if i + 1 < 2 * T then (1 : ℝ) else 0) =
      ((2 * T - 1 : ℕ) : ℝ) := by
    calc
      _ = ∑ _i ∈ range (2 * T - 1), (1 : ℝ) := by
        apply sum_congr rfl
        intro i hi
        rw [if_pos (by have := mem_range.mp hi; omega)]
      _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  calc
    _ = ∑ i ∈ range (2 * T), if i + 1 < 2 * T then (1 : ℝ) else 0 := by
      apply sum_congr rfl
      intro i hi
      calc
        _ = ∑ j ∈ range (2 * T), if j = i + 1 then (1 : ℝ) else 0 := by
          apply sum_congr rfl
          intro j hj
          rw [fullHeightOddIncidence T i j (mem_range.mp hi) (mem_range.mp hj)]
          split_ifs <;> simp only [Nat.cast_one, Nat.cast_zero]
        _ = _ := by simp only [sum_ite_eq', mem_range]
    _ = _ := by
      rw [show range (2 * T) = range ((2 * T - 1) + 1) by congr 1; omega,
        sum_range_succ, hsum, if_neg (by omega)]
      have hn : 2 * T - 1 + 1 = 2 * T := by omega
      have hc := congrArg (fun n : ℕ => (n : ℝ)) hn
      push_cast at hc
      linarith

private theorem fullHeightOddReciprocal_le (T : ℕ) :
    (∑ i ∈ range (2 * T), 1 / (fullHeightOddDivisor T i : ℝ)) ≤ 5 / 12 := by
  by_cases hT : T = 0
  · subst T
    simp only [mul_zero, range_zero, sum_empty]
    norm_num
  have hTpos : (0 : ℝ) < T := by exact_mod_cast Nat.pos_of_ne_zero hT
  have hfirst : (∑ i ∈ range T, 1 / (fullHeightOddDivisor T i : ℝ)) ≤ 1 / 4 := by
    calc
      _ ≤ ∑ _i ∈ range T, 1 / (4 * (T : ℝ)) := by
        apply sum_le_sum
        intro i _
        apply one_div_le_one_div_of_le (by positivity)
        simp only [fullHeightOddDivisor, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
        linarith [Nat.cast_nonneg (α := ℝ) i]
      _ = _ := by
        simp only [sum_const, card_range, nsmul_eq_mul]
        field_simp [hTpos.ne']
  have hsecond : (∑ i ∈ range T, 1 / (fullHeightOddDivisor T (T + i) : ℝ)) ≤ 1 / 6 := by
    calc
      _ ≤ ∑ _i ∈ range T, 1 / (6 * (T : ℝ)) := by
        apply sum_le_sum
        intro i _
        apply one_div_le_one_div_of_le (by positivity)
        simp only [fullHeightOddDivisor, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
        linarith [Nat.cast_nonneg (α := ℝ) i]
      _ = _ := by
        simp only [sum_const, card_range, nsmul_eq_mul]
        field_simp [hTpos.ne']
  rw [show 2 * T = T + T by omega, sum_range_add]
  linarith

private theorem fullHeightOddPeriod_le (T : ℕ) :
    (∑ i ∈ range (2 * T), ∑ j ∈ range (2 * T),
      if (fullHeightOddDivisor T i).Coprime (fullHeightOddDivisor T j) then
        (1 : ℝ) / ((fullHeightOddDivisor T i : ℝ) * (fullHeightOddDivisor T j : ℝ))
      else 0) ≤ 25 / 144 := by
  have hs0 : 0 ≤ ∑ i ∈ range (2 * T), 1 / (fullHeightOddDivisor T i : ℝ) :=
    sum_nonneg fun i _ => by positivity
  have hs2 := pow_le_pow_left₀ hs0 (fullHeightOddReciprocal_le T) 2
  calc
    _ ≤ ∑ i ∈ range (2 * T), ∑ j ∈ range (2 * T),
        (1 / (fullHeightOddDivisor T i : ℝ)) * (1 / (fullHeightOddDivisor T j : ℝ)) := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro j _
      split_ifs
      · rw [one_div_mul_one_div]
      · positivity
    _ = (∑ i ∈ range (2 * T), 1 / (fullHeightOddDivisor T i : ℝ)) ^ 2 := by
      rw [← sum_mul_sum, pow_two]
    _ ≤ _ := by norm_num at hs2 ⊢; exact hs2

/-- Even positive constant weights retain a linear discrepancy at full divisor height. -/
theorem fullHeightOddCrtDefect_lower (N : ℕ) :
    ((N + 12 : ℕ) : ℝ) / 2 ≤ fullHeightOddCrtDefect (N + 12) := by
  have hperiod := mul_le_mul_of_nonneg_left (fullHeightOddPeriod_le (N + 12))
    (show 0 ≤ 8 * ((N + 12 : ℕ) : ℝ) + 1 by positivity)
  unfold fullHeightOddCrtDefect
  simp only [sum_sub_distrib, ← mul_sum]
  rw [fullHeightOddIncidence_sum (N + 12) (by omega)]
  have hN : (12 : ℝ) ≤ (N + 12 : ℕ) := by exact_mod_cast (show 12 ≤ N + 12 by omega)
  nlinarith only [hperiod, hN]

/-- The period-transfer error stays positive after normalization by the physical horizon. -/
theorem fullHeightOddCrtDefect_normalized_lower (N : ℕ) :
    (1 : ℝ) / 20 ≤
      fullHeightOddCrtDefect (N + 12) / ((8 * (N + 12) + 2 : ℕ) : ℝ) := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (8 * (N + 12) + 2 : ℕ))).mpr
  have hb := fullHeightOddCrtDefect_lower N
  have hN : (1 : ℝ) ≤ (N + 12 : ℕ) := by exact_mod_cast (show 1 ≤ N + 12 by omega)
  push_cast
  push_cast at hb hN
  nlinarith only [hb, hN]

end

end TwinPrime
