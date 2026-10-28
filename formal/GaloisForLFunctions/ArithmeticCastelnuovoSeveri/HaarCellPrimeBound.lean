import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HaarCellPrimeCompression
import GaloisForLFunctions.ArithmeticOrientationTheory.HorizonUniformSchurDominanceOfThePrimeTowers

/-!
# A uniform prime bound on balanced complete-cell sections

Young's inequality assigns each surviving prime edge to its two endpoints.
Outgoing mass contracts by the multiplier and has a convergent von Mangoldt
sum. Incoming edges form a divisor sum with coefficient strictly below one.
No sign condition is imposed on the source coefficients.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open ArithmeticFunction

private theorem sum_unique_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (p : ι → Prop) [DecidablePred p] (f : ι → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ i ∈ s, ∀ j ∈ s, p i → p j → i = j)
    (hf : ∀ i ∈ s, p i → f i ≤ C) :
    ∑ i ∈ s, (if p i then f i else 0) ≤ C := by
  classical
  by_cases h : ∃ i ∈ s, p i
  · obtain ⟨i, hi, hp⟩ := h
    calc
      ∑ j ∈ s, (if p j then f j else 0) = f i := by
        rw [sum_eq_single i]
        · exact if_pos hp
        · intro j hj hji
          exact if_neg (fun hpj => hji (hu j hj i hi hpj hp))
        · exact fun hn => False.elim (hn hi)
      _ ≤ C := hf i hi hp
  · have hz : ∀ i ∈ s, (if p i then f i else 0) = 0 := by
      intro i hi
      exact if_neg (fun hp => h ⟨i, hi, hp⟩)
    rw [sum_eq_zero hz]
    exact hC

/-- One directed prime edge between odd middle boundaries. -/
def haarPrimeEntry (a b m : ℕ) : ℝ :=
  if (2 * a + 1) * m = 2 * b + 1 then
    vonMangoldt m / Real.sqrt m * haarMass b else 0

/-- The finite matrix of all directed prime edges through a specified horizon. -/
def haarPrimeMatrix (M a b : ℕ) : ℝ := ∑ m ∈ Icc 2 M, haarPrimeEntry a b m

theorem haarPrimeEntry_nonneg (a m : ℕ) {b : ℕ} (hb : 1 ≤ b) :
    0 ≤ haarPrimeEntry a b m := by
  unfold haarPrimeEntry
  split_ifs
  · exact mul_nonneg (div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _))
      (haarMass_pos hb).le
  · exact le_rfl

theorem haarPrimeMatrix_nonneg (M a : ℕ) {b : ℕ} (hb : 1 ≤ b) :
    0 ≤ haarPrimeMatrix M a b :=
  sum_nonneg fun m _ => haarPrimeEntry_nonneg a m hb

private theorem outgoing_entry_sum_le {a m : ℕ} (ha : 1 ≤ a) (hm : 2 ≤ m) (X : ℕ) :
    ∑ b ∈ Icc 1 X, haarPrimeEntry a b m ≤
      2 * (vonMangoldt m / ((m : ℝ) * Real.sqrt m)) * haarMass a := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmR
  unfold haarPrimeEntry
  apply sum_unique_le
  · exact mul_nonneg (mul_nonneg (by norm_num)
      (div_nonneg vonMangoldt_nonneg (mul_nonneg hmR.le hs.le))) (haarMass_pos ha).le
  · intro b _hb b' _hb' he he'
    omega
  · intro b hb he
    have hmass : haarMass b ≤ 2 * haarMass a / (m : ℝ) := by
      apply (le_div_iff₀ hmR).mpr
      simpa only [mul_comm] using haarMass_mul_le ha (mem_Icc.mp hb).1 hm he
    calc
      vonMangoldt m / Real.sqrt m * haarMass b ≤
          vonMangoldt m / Real.sqrt m * (2 * haarMass a / (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hmass (div_nonneg vonMangoldt_nonneg hs.le)
      _ = 2 * (vonMangoldt m / ((m : ℝ) * Real.sqrt m)) * haarMass a := by
        field_simp

/-- Outgoing prime mass has a bound independent of both source and prime horizons. -/
theorem haarPrimeMatrix_row_le {a : ℕ} (ha : 1 ≤ a) (X M : ℕ) :
    ∑ b ∈ Icc 1 X, haarPrimeMatrix M a b ≤ 16 * haarMass a := by
  unfold haarPrimeMatrix
  rw [sum_comm]
  calc
    ∑ m ∈ Icc 2 M, ∑ b ∈ Icc 1 X, haarPrimeEntry a b m ≤
        ∑ m ∈ Icc 2 M,
          2 * (vonMangoldt m / ((m : ℝ) * Real.sqrt m)) * haarMass a :=
      sum_le_sum fun m hm => outgoing_entry_sum_le ha (mem_Icc.mp hm).1 X
    _ = 2 * (∑ m ∈ Icc 2 M,
        vonMangoldt m / ((m : ℝ) * Real.sqrt m)) * haarMass a := by
      rw [← sum_mul, ← mul_sum]
    _ ≤ 16 * haarMass a := by
      have h := ArithmeticOrientationTheory.sum_Icc_vonMangoldt_div_mul_sqrt_le_eight M
      have hmul := mul_le_mul_of_nonneg_right h (haarMass_pos ha).le
      linarith only [hmul]

private theorem incoming_entry_sum_le {b m : ℕ} (hb : 1 ≤ b) (hm : 2 ≤ m) (X : ℕ) :
    ∑ a ∈ Icc 1 X, haarPrimeEntry a b m ≤
      if m ∣ 2 * b + 1 then vonMangoldt m / Real.sqrt m * haarMass b else 0 := by
  unfold haarPrimeEntry
  by_cases hd : m ∣ 2 * b + 1
  · rw [if_pos hd]
    apply sum_unique_le
    · exact mul_nonneg (div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _))
        (haarMass_pos hb).le
    · intro a _ha a' _ha' he he'
      have h := Nat.eq_of_mul_eq_mul_right (by omega : 0 < m) (he.trans he'.symm)
      omega
    · intro a _ha _he
      exact le_rfl
  · rw [if_neg hd]
    apply le_of_eq
    apply sum_eq_zero
    intro a _ha
    apply if_neg
    intro he
    exact hd ⟨2 * a + 1, by simpa only [Nat.mul_comm] using he.symm⟩

/-- Incoming prime edges are paid by the exact von Mangoldt divisor identity. -/
theorem haarPrimeMatrix_column_le {b : ℕ} (hb : 1 ≤ b) (X M : ℕ) :
    ∑ a ∈ Icc 1 X, haarPrimeMatrix M a b ≤
      (Real.log ((2 * b + 1 : ℕ) : ℝ) / Real.sqrt 2) * haarMass b := by
  classical
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  let D := (Icc 2 M).filter (fun m => m ∣ 2 * b + 1)
  have hD : D ⊆ (2 * b + 1).divisors := by
    intro m hm
    exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hm).2, by omega⟩
  have hsum : ∑ m ∈ D, vonMangoldt m ≤ Real.log ((2 * b + 1 : ℕ) : ℝ) := by
    rw [← ArithmeticFunction.vonMangoldt_sum]
    exact sum_le_sum_of_subset_of_nonneg hD fun _ _ _ => vonMangoldt_nonneg
  unfold haarPrimeMatrix
  rw [sum_comm]
  calc
    ∑ m ∈ Icc 2 M, ∑ a ∈ Icc 1 X, haarPrimeEntry a b m ≤
        ∑ m ∈ Icc 2 M,
          if m ∣ 2 * b + 1 then vonMangoldt m / Real.sqrt m * haarMass b else 0 :=
      sum_le_sum fun m hm => incoming_entry_sum_le hb (mem_Icc.mp hm).1 X
    _ = ∑ m ∈ D, vonMangoldt m / Real.sqrt m * haarMass b := by
      simp only [D, sum_filter]
    _ ≤ ∑ m ∈ D, (vonMangoldt m / Real.sqrt 2) * haarMass b := by
      apply sum_le_sum
      intro m hm
      have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hm).1).1
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left vonMangoldt_nonneg hs (Real.sqrt_le_sqrt hm2))
        (haarMass_pos hb).le
    _ = ((∑ m ∈ D, vonMangoldt m) / Real.sqrt 2) * haarMass b := by
      rw [← sum_mul, ← sum_div]
    _ ≤ (Real.log ((2 * b + 1 : ℕ) : ℝ) / Real.sqrt 2) * haarMass b :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hsum hs.le) (haarMass_pos hb).le

/-- The prime matrix is the complete prime energy of the actual signed section. -/
theorem haarPrimeEnergy_matrix (c : ℕ → ℝ) (X : ℕ) :
    haarPrimeEnergy c X = ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
      2 * haarPrimeMatrix (2 * X + 1) a b * c a * c b := by
  classical
  rw [haarPrimeEnergy_eq]
  calc
    ∑ m ∈ Icc 2 (2 * X + 1),
        (2 * vonMangoldt m / Real.sqrt m) *
          ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
            c a * c b * (if (2 * a + 1) * m = 2 * b + 1 then haarMass b else 0) =
        ∑ m ∈ Icc 2 (2 * X + 1), ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
          2 * haarPrimeEntry a b m * c a * c b := by
      apply sum_congr rfl
      intro m _hm
      rw [mul_sum]
      apply sum_congr rfl
      intro a _ha
      rw [mul_sum]
      apply sum_congr rfl
      intro b _hb
      unfold haarPrimeEntry
      split_ifs <;> ring
    _ = ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, ∑ m ∈ Icc 2 (2 * X + 1),
        2 * haarPrimeEntry a b m * c a * c b := by
      rw [sum_comm]
      apply sum_congr rfl
      intro a _ha
      rw [sum_comm]
    _ = ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
        2 * haarPrimeMatrix (2 * X + 1) a b * c a * c b := by
      apply sum_congr rfl
      intro a _ha
      apply sum_congr rfl
      intro b _hb
      simp only [haarPrimeMatrix, sum_mul, mul_sum]

private theorem quadratic_le_rows (s : Finset ℕ) (K : ℕ → ℕ → ℝ) (c : ℕ → ℝ)
    (hK : ∀ a ∈ s, ∀ b ∈ s, 0 ≤ K a b) :
    ∑ a ∈ s, ∑ b ∈ s, 2 * K a b * c a * c b ≤
      ∑ a ∈ s, ((∑ b ∈ s, K a b) + (∑ b ∈ s, K b a)) * c a ^ 2 := by
  calc
    ∑ a ∈ s, ∑ b ∈ s, 2 * K a b * c a * c b ≤
        ∑ a ∈ s, ∑ b ∈ s, (K a b * c a ^ 2 + K a b * c b ^ 2) := by
      apply sum_le_sum
      intro a ha
      apply sum_le_sum
      intro b hb
      have h := mul_nonneg (hK a ha b hb) (sq_nonneg (c a - c b))
      nlinarith only [h]
    _ = (∑ a ∈ s, (∑ b ∈ s, K a b) * c a ^ 2) +
        ∑ b ∈ s, (∑ a ∈ s, K a b) * c b ^ 2 := by
      simp only [sum_add_distrib]
      congr 1
      · simp only [sum_mul]
      · rw [sum_comm]
        simp only [sum_mul]
    _ = ∑ a ∈ s, ((∑ b ∈ s, K a b) + (∑ b ∈ s, K b a)) * c a ^ 2 := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro a _ha
      ring

/-- Full prime charge of every signed balanced section, with no upper-horizon loss. -/
theorem haarPrimeEnergy_le (c : ℕ → ℝ) (X : ℕ) :
    haarPrimeEnergy c X ≤ ∑ a ∈ Icc 1 X,
      (16 + Real.log ((2 * a + 1 : ℕ) : ℝ) / Real.sqrt 2) * haarMass a * c a ^ 2 := by
  rw [haarPrimeEnergy_matrix]
  apply (quadratic_le_rows (Icc 1 X) (haarPrimeMatrix (2 * X + 1)) c
    (fun a _ha b hb => haarPrimeMatrix_nonneg _ a (mem_Icc.mp hb).1)).trans
  apply sum_le_sum
  intro a ha
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have ha1 := (mem_Icc.mp ha).1
  have h := add_le_add (haarPrimeMatrix_row_le ha1 X (2 * X + 1))
    (haarPrimeMatrix_column_le ha1 X (2 * X + 1))
  exact h.trans_eq (by ring)

theorem haarPrime_log_coefficient_lt_one : (1 : ℝ) / Real.sqrt 2 < 1 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  apply (div_lt_one hp).mpr
  nlinarith only [hs, hp]

#print axioms haarPrimeMatrix_row_le
#print axioms haarPrimeMatrix_column_le
#print axioms haarPrimeEnergy_le

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
