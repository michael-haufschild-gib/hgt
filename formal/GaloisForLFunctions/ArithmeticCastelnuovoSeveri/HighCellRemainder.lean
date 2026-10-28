import GaloisForLFunctions.BiarithmeticGaugeGeometry.EuclideanCellRemainderAndPolarNeutralCollapse

/-!
# The successor remainder on high logarithmic cells

Multiplicative translation subdivides an integer logarithmic cell into consecutive cells.
Replacing the translated profile by its value on the first subcell has a signed remainder.
On cells with index at least `A`, this remainder is bounded by `1/A` times the product of
the first profile's square-mass norm and the second profile's discrete derivative norm.
The estimate is uniform in the multiplier and retains every successor subcell.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells

open BiarithmeticGaugeGeometry

/-- Square mass on a finite interval of logarithmic cells. -/
def cellMass (c : ℕ → ℝ) (A X : ℕ) : ℝ :=
  ∑ a ∈ Icc A X, logCellWidth a * c a ^ 2

/-- Mixed correlation with every subcell produced by multiplication retained. -/
def cellShiftCorr (c d : ℕ → ℝ) (A X m : ℕ) : ℝ :=
  ∑ a ∈ Icc A X, c a * ∑ r ∈ range m, logCellWidth (a * m + r) * d (a * m + r)

/-- The exact-divisibility part of a mixed cell correlation. -/
def cellSpine (c d : ℕ → ℝ) (A X m : ℕ) : ℝ :=
  ∑ a ∈ Icc A X, logCellWidth a * c a * d (a * m)

/-- Successor subcells measured relative to the divisible endpoint. -/
def mixedCellRemainder (c d : ℕ → ℝ) (A X m : ℕ) : ℝ :=
  ∑ a ∈ Icc A X, c a * ∑ r ∈ range m,
    logCellWidth (a * m + r) * (d (a * m + r) - d (a * m))

theorem cellMass_nonneg (c : ℕ → ℝ) {A : ℕ} (hA : 1 ≤ A) (X : ℕ) :
    0 ≤ cellMass c A X :=
  sum_nonneg fun a ha => mul_nonneg (logCellWidth_pos (hA.trans (mem_Icc.mp ha).1)).le
    (sq_nonneg (c a))

theorem cellShiftCorr_eq_spine_add_remainder (c d : ℕ → ℝ) {A : ℕ} (hA : 1 ≤ A)
    (X : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    cellShiftCorr c d A X m = cellSpine c d A X m + mixedCellRemainder c d A X m := by
  unfold cellShiftCorr cellSpine mixedCellRemainder
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro a ha
  have hsum := sum_logCellWidth_mul_add_eq (hA.trans (mem_Icc.mp ha).1) hm
  rw [show logCellWidth a * c a * d (a * m) =
    c a * (logCellWidth a * d (a * m)) by ring, ← mul_add, ← hsum, sum_mul]
  congr 1
  rw [← sum_add_distrib]
  exact sum_congr rfl fun r _ => by ring

/-- Derivative energy on one quotient-remainder block. -/
def blockEnergy (d : ℕ → ℝ) (a m : ℕ) : ℝ :=
  ∑ j ∈ range m, ((a * m + j : ℕ) : ℝ) * (d (a * m + j + 1) - d (a * m + j)) ^ 2

theorem blockEnergy_nonneg (d : ℕ → ℝ) (a m : ℕ) : 0 ≤ blockEnergy d a m :=
  sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg (a * m + j)) (sq_nonneg _)

private theorem sub_eq_sum_diff (d : ℕ → ℝ) (n r : ℕ) :
    d (n + r) - d n = ∑ j ∈ range r, (d (n + j + 1) - d (n + j)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ← ih]
    rw [show n + (r + 1) = n + r + 1 by omega]
    ring

/-- Telescoping inside one block costs the inverse of its quotient index. -/
theorem sub_mul_add_sq_le (d : ℕ → ℝ) {a m r : ℕ} (ha : 1 ≤ a) (hr : r < m) :
    (d (a * m + r) - d (a * m)) ^ 2 ≤ (1 / (a : ℝ)) * blockEnergy d a m := by
  rw [sub_eq_sum_diff]
  have hcs := sq_sum_le_card_mul_sum_sq (s := range r)
    (f := fun j => d (a * m + j + 1) - d (a * m + j))
  simp only [card_range] at hcs
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hrm : (r : ℝ) ≤ m := by exact_mod_cast hr.le
  calc (∑ j ∈ range r, (d (a * m + j + 1) - d (a * m + j))) ^ 2
      ≤ (r : ℝ) * ∑ j ∈ range r, (d (a * m + j + 1) - d (a * m + j)) ^ 2 := hcs
    _ = ∑ j ∈ range r, (r : ℝ) * (d (a * m + j + 1) - d (a * m + j)) ^ 2 := mul_sum _ _ _
    _ ≤ ∑ j ∈ range r, ((1 / (a : ℝ)) * ((a * m + j : ℕ) : ℝ)) *
        (d (a * m + j + 1) - d (a * m + j)) ^ 2 := by
      apply sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply hrm.trans
      have h : (a : ℝ) * m ≤ ((a * m + j : ℕ) : ℝ) := by
        exact_mod_cast (Nat.le_add_right (a * m) j)
      have hh := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 1 / (a : ℝ))
      have he : (1 / (a : ℝ)) * ((a : ℝ) * m) = (m : ℝ) := by field_simp
      rwa [he] at hh
    _ ≤ ∑ j ∈ range m, ((1 / (a : ℝ)) * ((a * m + j : ℕ) : ℝ)) *
        (d (a * m + j + 1) - d (a * m + j)) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (range_mono hr.le) fun j _ _ => by positivity
    _ = (1 / (a : ℝ)) * blockEnergy d a m := by
      simp only [blockEnergy, mul_assoc, mul_sum]

/-- Disjoint quotient-remainder blocks never charge a derivative edge twice. -/
theorem sum_blockEnergy_le (d : ℕ → ℝ) {A : ℕ} (hA : 1 ≤ A) (X : ℕ)
    {m : ℕ} (hm : 1 ≤ m) :
    (∑ a ∈ Icc A X, blockEnergy d a m) ≤ biarithmeticSobolevEnergy d (X * m + m) := by
  let term : ℕ → ℝ := fun k => (k : ℝ) * (d (k + 1) - d k) ^ 2
  let P := Icc A X ×ˢ range m
  let f : ℕ × ℕ → ℕ := fun p => p.1 * m + p.2
  have hinj : Set.InjOn f P := by
    intro ⟨a, i⟩ ha ⟨b, j⟩ hb he
    simp only [P, mem_coe, mem_product, mem_Icc, mem_range] at ha hb
    dsimp only [f] at he
    have hdiv := congrArg (· / m) he
    rw [Nat.mul_comm a m, Nat.mul_comm b m, Nat.mul_add_div (by omega : 0 < m),
      Nat.mul_add_div (by omega : 0 < m), Nat.div_eq_of_lt ha.2,
      Nat.div_eq_of_lt hb.2, add_zero, add_zero] at hdiv
    subst b
    exact Prod.ext rfl (Nat.add_left_cancel he)
  have hsub : P.image f ⊆ Icc 1 (X * m + m) := by
    intro k hk
    obtain ⟨⟨a, j⟩, ha, rfl⟩ := mem_image.mp hk
    simp only [P, mem_product, mem_Icc, mem_range] at ha
    dsimp only [f]
    have hlow : 1 ≤ a * m := Nat.mul_le_mul (hA.trans ha.1.1) hm
    have hhigh : a * m ≤ X * m := Nat.mul_le_mul_right m ha.1.2
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  calc (∑ a ∈ Icc A X, blockEnergy d a m) = ∑ p ∈ P, term (f p) :=
      (sum_product (Icc A X) (range m) (fun p => term (f p))).symm
    _ = ∑ k ∈ P.image f, term k := (sum_image hinj).symm
    _ ≤ ∑ k ∈ Icc 1 (X * m + m), term k :=
      sum_le_sum_of_subset_of_nonneg hsub fun k _ _ =>
        mul_nonneg (Nat.cast_nonneg k) (sq_nonneg _)
    _ = biarithmeticSobolevEnergy d (X * m + m) := rfl

/-- The small cell width and the inverse quotient index both survive the row estimate. -/
theorem row_remainder_sq_le (d : ℕ → ℝ) {A a m : ℕ}
    (hA : 1 ≤ A) (hAa : A ≤ a) (hm : 1 ≤ m) :
    (∑ r ∈ range m, logCellWidth (a * m + r) * (d (a * m + r) - d (a * m))) ^ 2 ≤
      logCellWidth a * ((1 / (A : ℝ) ^ 2) * blockEnergy d a m) := by
  have ha := hA.trans hAa
  have hwa := (logCellWidth_pos ha).le
  have hw : ∀ r : ℕ, 0 ≤ logCellWidth (a * m + r) := fun r =>
    (logCellWidth_pos (by have h := Nat.mul_le_mul ha hm; omega)).le
  have hcs : (∑ r ∈ range m, logCellWidth (a * m + r) * (d (a * m + r) - d (a * m))) ^ 2 ≤
      (∑ r ∈ range m, logCellWidth (a * m + r)) *
        ∑ r ∈ range m, logCellWidth (a * m + r) * (d (a * m + r) - d (a * m)) ^ 2 := by
    refine sum_sq_le_sum_mul_sum_of_sq_le_mul (range m) (fun r _ => hw r)
      (fun r _ => mul_nonneg (hw r) (sq_nonneg _)) ?_
    intro r _
    exact le_of_eq (by ring)
  rw [sum_logCellWidth_mul_add_eq ha hm] at hcs
  have hinner : (∑ r ∈ range m,
      logCellWidth (a * m + r) * (d (a * m + r) - d (a * m)) ^ 2) ≤
      logCellWidth a * ((1 / (a : ℝ)) * blockEnergy d a m) := by
    calc _ ≤ ∑ r ∈ range m,
          logCellWidth (a * m + r) * ((1 / (a : ℝ)) * blockEnergy d a m) :=
        sum_le_sum fun r hr => mul_le_mul_of_nonneg_left
          (sub_mul_add_sq_le d ha (mem_range.mp hr)) (hw r)
      _ = _ := by rw [← sum_mul, sum_logCellWidth_mul_add_eq ha hm]
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hinv : 1 / (a : ℝ) ≤ 1 / (A : ℝ) :=
    one_div_le_one_div_of_le hA0 (by exact_mod_cast hAa)
  have hsmall : logCellWidth a * (1 / (a : ℝ)) ≤ 1 / (A : ℝ) ^ 2 := by
    calc logCellWidth a * (1 / (a : ℝ)) ≤ (1 / (A : ℝ)) * (1 / (A : ℝ)) :=
        mul_le_mul ((logCellWidth_le_inv ha).trans hinv) hinv (by positivity) (by positivity)
      _ = 1 / (A : ℝ) ^ 2 := by ring
  calc _ ≤ logCellWidth a * (logCellWidth a * ((1 / (a : ℝ)) * blockEnergy d a m)) :=
      hcs.trans (mul_le_mul_of_nonneg_left hinner hwa)
    _ = logCellWidth a * ((logCellWidth a * (1 / (a : ℝ))) * blockEnergy d a m) := by ring
    _ ≤ logCellWidth a * ((1 / (A : ℝ) ^ 2) * blockEnergy d a m) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hsmall (blockEnergy_nonneg d a m)) hwa

/-- Mixed successor error decays with the lowest occupied integer scale. -/
theorem mixedCellRemainder_sq_le (c d : ℕ → ℝ) {A : ℕ} (hA : 1 ≤ A) (X : ℕ)
    {m : ℕ} (hm : 1 ≤ m) :
    mixedCellRemainder c d A X m ^ 2 ≤
      cellMass c A X * ((1 / (A : ℝ) ^ 2) * biarithmeticSobolevEnergy d (X * m + m)) := by
  have hcs : mixedCellRemainder c d A X m ^ 2 ≤
      cellMass c A X * ∑ a ∈ Icc A X, (1 / (A : ℝ) ^ 2) * blockEnergy d a m := by
    refine sum_sq_le_sum_mul_sum_of_sq_le_mul (Icc A X)
      (fun a ha => mul_nonneg (logCellWidth_pos (hA.trans (mem_Icc.mp ha).1)).le (sq_nonneg _))
      (fun a _ => mul_nonneg (by positivity) (blockEnergy_nonneg d a m)) ?_
    intro a ha
    have h := mul_le_mul_of_nonneg_left
      (row_remainder_sq_le d hA (mem_Icc.mp ha).1 hm) (sq_nonneg (c a))
    convert h using 1 <;> ring
  rw [← mul_sum] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (sum_blockEnergy_le d hA X hm) (by positivity))
    (cellMass_nonneg c hA X))

/-- A supported profile pays no derivative energy beyond its actual horizon. -/
theorem sobolevEnergy_eq_of_supported (d : ℕ → ℝ) {X Y : ℕ} (hXY : X ≤ Y)
    (hs : ∀ n, X < n → d n = 0) :
    biarithmeticSobolevEnergy d Y = biarithmeticSobolevEnergy d X := by
  unfold biarithmeticSobolevEnergy
  symm
  apply sum_subset (Icc_subset_Icc_right hXY)
  intro k hk hnot
  have hkX : X < k := by simp only [mem_Icc] at hk hnot; omega
  rw [hs (k + 1) (by omega), hs k hkX, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]

theorem abs_mixedCellRemainder_le (c d : ℕ → ℝ) {A : ℕ} (hA : 1 ≤ A) (X : ℕ)
    {m : ℕ} (hm : 1 ≤ m) (hs : ∀ n, X < n → d n = 0) :
    |mixedCellRemainder c d A X m| ≤
      Real.sqrt (cellMass c A X) * Real.sqrt (biarithmeticSobolevEnergy d X) / A := by
  have hsq := mixedCellRemainder_sq_le c d hA X hm
  have hXY : X ≤ X * m + m := by
    have h := Nat.mul_le_mul_left X hm
    omega
  rw [sobolevEnergy_eq_of_supported d hXY hs] at hsq
  have hmass := cellMass_nonneg c hA X
  have henergy : 0 ≤ biarithmeticSobolevEnergy d X :=
    sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg k) (sq_nonneg _)
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have he : (Real.sqrt (cellMass c A X) * Real.sqrt (biarithmeticSobolevEnergy d X) / A) ^ 2 =
      cellMass c A X * ((1 / (A : ℝ) ^ 2) * biarithmeticSobolevEnergy d X) := by
    rw [div_pow, mul_pow, Real.sq_sqrt hmass, Real.sq_sqrt henergy]
    ring
  have hrhs : 0 ≤ Real.sqrt (cellMass c A X) * Real.sqrt (biarithmeticSobolevEnergy d X) / A :=
    by positivity
  rw [← he] at hsq
  nlinarith only [hsq, sq_abs (mixedCellRemainder c d A X m),
    abs_nonneg (mixedCellRemainder c d A X m), hrhs]

/-- Total positive prime weight through a multiplier horizon. -/
def primeWeightSum (M : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 M, 2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m

/-- Every signed successor contribution is retained in the prime-weighted remainder. -/
def primeCellRemainder (c d : ℕ → ℝ) (A X M : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 M, (2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m) *
    mixedCellRemainder c d A X m

theorem abs_primeCellRemainder_le (c d : ℕ → ℝ) {A : ℕ} (hA : 1 ≤ A) (X M : ℕ)
    (hs : ∀ n, X < n → d n = 0) :
    |primeCellRemainder c d A X M| ≤
      primeWeightSum M * (Real.sqrt (cellMass c A X) *
        Real.sqrt (biarithmeticSobolevEnergy d X) / A) := by
  unfold primeCellRemainder primeWeightSum
  rw [sum_mul]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro m hm
  have hw : 0 ≤ 2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m :=
    div_nonneg (mul_nonneg (by norm_num) (ArithmeticFunction.vonMangoldt_nonneg (n := m)))
      (Real.sqrt_nonneg m)
  rw [abs_mul, abs_of_nonneg hw]
  exact mul_le_mul_of_nonneg_left (abs_mixedCellRemainder_le c d hA X (mem_Icc.mp hm).1 hs) hw

#print axioms mixedCellRemainder_sq_le
#print axioms abs_primeCellRemainder_le

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
