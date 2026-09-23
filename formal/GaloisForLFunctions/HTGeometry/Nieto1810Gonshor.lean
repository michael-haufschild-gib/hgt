import GaloisForLFunctions.QECLean.Foundations.Basic
import GaloisForLFunctions.HTGeometry.ConstitutiveEquivariantArityGenesis
import GaloisForLFunctions.RHTower.EulerSquarefreeWickBinaryGaugeTower

/-!
# Nieto 1810 mechanical applications: finite Gonshor sign strings

This file implements the finite sign-sequence formula in equations (40)--(44), proves its dyadic
closure and complement symmetry, connects it to QECLean basis labels, and identifies its local sign
with the existing Euler--Wick Walsh gauge sign. No claim about transfinite surreal infrastructure or
the paper's speculative dyadic-spin interpretation is made.
-/

open Finset
open scoped BigOperators

namespace GaloisForLFunctions.Nieto1810

noncomputable section

/-- Paper convention `0 ↦ +`, `1 ↦ -`, interpreted rationally. -/
def gonshorSign (b : Fin 2) : ℚ := if b = 0 then 1 else -1

/-- Fractional suffix after the first sign change: weights `1/2, 1/4, ...`. -/
def gonshorDyadicTail : List (Fin 2) → ℚ
  | [] => 0
  | b :: bs => gonshorSign b / 2 + gonshorDyadicTail bs / 2

/-- Gonshor value once the first sign of the sequence is fixed. -/
def gonshorFrom (initial : Fin 2) : List (Fin 2) → ℚ
  | [] => 0
  | b :: bs =>
      if b = initial then gonshorSign b + gonshorFrom initial bs
      else gonshorDyadicTail (b :: bs)

/-- Finite Gonshor sign-sequence value from equations (40)--(44). -/
def gonshorValue : List (Fin 2) → ℚ
  | [] => 0
  | b :: bs => gonshorFrom b (b :: bs)

@[simp] theorem gonshorSign_rev (b : Fin 2) :
    gonshorSign (Fin.rev b) = -gonshorSign b := by
  fin_cases b <;> norm_num [gonshorSign, Fin.rev]

theorem gonshorDyadicTail_complement (xs : List (Fin 2)) :
    gonshorDyadicTail (xs.map Fin.rev) = -gonshorDyadicTail xs := by
  induction xs with
  | nil => simp [gonshorDyadicTail]
  | cons b bs ih =>
      simp only [List.map_cons, gonshorDyadicTail, gonshorSign_rev, ih]
      ring

theorem gonshorFrom_complement (initial : Fin 2) (xs : List (Fin 2)) :
    gonshorFrom (Fin.rev initial) (xs.map Fin.rev) = -gonshorFrom initial xs := by
  induction xs with
  | nil => simp [gonshorFrom]
  | cons b bs ih =>
      by_cases h : b = initial
      · subst b
        simp [gonshorFrom, ih]
        ring
      · have hr : Fin.rev b ≠ Fin.rev initial := fun e => h (Fin.rev_injective e)
        change (if Fin.rev b = Fin.rev initial then
              gonshorSign (Fin.rev b) + gonshorFrom (Fin.rev initial) (bs.map Fin.rev)
            else gonshorDyadicTail (Fin.rev b :: bs.map Fin.rev)) =
          -(if b = initial then gonshorSign b + gonshorFrom initial bs
            else gonshorDyadicTail (b :: bs))
        rw [if_neg hr, if_neg h]
        simpa using gonshorDyadicTail_complement (b :: bs)

/-- Complementing every sign negates every finite Gonshor value. -/
theorem gonshorValue_complement (xs : List (Fin 2)) :
    gonshorValue (xs.map Fin.rev) = -gonshorValue xs := by
  cases xs with
  | nil => simp [gonshorValue]
  | cons b bs => simpa [gonshorValue] using gonshorFrom_complement b (b :: bs)

/-- Dyadic rational predicate used by equation (37). -/
def IsDyadicRational (q : ℚ) : Prop :=
  ∃ m : ℤ, ∃ n : ℕ, q = (m : ℚ) / (2 : ℚ) ^ n

/-- Real image of all signed dyadic fractions. -/
def dyadicRealSet : Set ℝ :=
  {x | ∃ m : ℤ, ∃ n : ℕ, x = (m : ℝ) / (2 : ℝ) ^ n}

/-- Equation (37)'s density claim, with an explicit floor approximation at every scale. -/
theorem dyadicRealSet_dense : Dense dyadicRealSet := by
  rw [Metric.dense_iff]
  intro x r hr
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < r :=
    exists_pow_lt_of_lt_one hr (by norm_num)
  let d : ℝ := (2 : ℝ) ^ n
  let m : ℤ := ⌊x * d⌋
  have hdpos : 0 < d := by positivity
  have hlow : (m : ℝ) ≤ x * d := by
    exact Int.floor_le (x * d)
  have hupp : x * d < (m : ℝ) + 1 := by
    exact Int.lt_floor_add_one (x * d)
  have hy_le : (m : ℝ) / d ≤ x := by
    exact (div_le_iff₀ hdpos).2 hlow
  have hx_lt : x < (m : ℝ) / d + 1 / d := by
    rw [← add_div]
    exact (lt_div_iff₀ hdpos).2 hupp
  refine ⟨(m : ℝ) / d, ?_, ⟨m, n, rfl⟩⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hy_le)]
  have hgap : x - (m : ℝ) / d < 1 / d :=
    sub_lt_iff_lt_add.2 (by simpa [add_comm] using hx_lt)
  calc
    -((m : ℝ) / d - x) = x - (m : ℝ) / d := by ring
    _ < 1 / d := hgap
    _ = (1 / 2 : ℝ) ^ n := by simp [d, one_div, inv_pow]
    _ < r := hn

theorem isDyadicRational_zero : IsDyadicRational 0 := by
  exact ⟨0, 0, by norm_num⟩

theorem isDyadicRational_int (m : ℤ) : IsDyadicRational (m : ℚ) := by
  exact ⟨m, 0, by simp⟩

theorem IsDyadicRational.add {x y : ℚ}
    (hx : IsDyadicRational x) (hy : IsDyadicRational y) : IsDyadicRational (x + y) := by
  rcases hx with ⟨m, r, rfl⟩
  rcases hy with ⟨k, s, rfl⟩
  refine ⟨m * (2 : ℤ) ^ s + k * (2 : ℤ) ^ r, r + s, ?_⟩
  push_cast
  field_simp
  ring

theorem IsDyadicRational.half {x : ℚ} (hx : IsDyadicRational x) :
    IsDyadicRational (x / 2) := by
  rcases hx with ⟨m, n, rfl⟩
  refine ⟨m, n + 1, ?_⟩
  rw [pow_succ]
  ring

theorem gonshorDyadicTail_isDyadic (xs : List (Fin 2)) :
    IsDyadicRational (gonshorDyadicTail xs) := by
  induction xs with
  | nil => exact isDyadicRational_zero
  | cons b bs ih =>
      rw [gonshorDyadicTail, show gonshorSign b / 2 + gonshorDyadicTail bs / 2 =
        (gonshorSign b + gonshorDyadicTail bs) / 2 by ring]
      apply IsDyadicRational.half
      apply IsDyadicRational.add
      · cases b using Fin.cases with
        | zero => simpa [gonshorSign] using isDyadicRational_int 1
        | succ b =>
            fin_cases b
            simpa [gonshorSign] using isDyadicRational_int (-1)
      · exact ih

theorem gonshorFrom_isDyadic (initial : Fin 2) (xs : List (Fin 2)) :
    IsDyadicRational (gonshorFrom initial xs) := by
  induction xs with
  | nil => exact isDyadicRational_zero
  | cons b bs ih =>
      rw [gonshorFrom]
      split
      · apply IsDyadicRational.add
        · cases b using Fin.cases with
          | zero => simpa [gonshorSign] using isDyadicRational_int 1
          | succ b =>
              fin_cases b
              simpa [gonshorSign] using isDyadicRational_int (-1)
        · exact ih
      · exact gonshorDyadicTail_isDyadic _

/-- Every finite Gonshor/qubit string denotes a dyadic rational. -/
theorem gonshorValue_isDyadic (xs : List (Fin 2)) :
    IsDyadicRational (gonshorValue xs) := by
  cases xs with
  | nil => exact isDyadicRational_zero
  | cons b bs => exact gonshorFrom_isDyadic b (b :: bs)

theorem gonshor_day_one :
    gonshorValue [1] = -1 ∧ gonshorValue [0] = 1 := by
  norm_num [gonshorValue, gonshorFrom, gonshorSign]

theorem gonshor_day_two :
    gonshorValue [1, 1] = -2 ∧ gonshorValue [1, 0] = -1 / 2 ∧
      gonshorValue [0, 1] = 1 / 2 ∧ gonshorValue [0, 0] = 2 := by
  norm_num [gonshorValue, gonshorFrom, gonshorDyadicTail, gonshorSign]

theorem gonshor_day_three :
    gonshorValue [1, 1, 1] = -3 ∧ gonshorValue [1, 1, 0] = -3 / 2 ∧
      gonshorValue [1, 0, 1] = -3 / 4 ∧ gonshorValue [1, 0, 0] = -1 / 4 ∧
      gonshorValue [0, 1, 1] = 1 / 4 ∧ gonshorValue [0, 1, 0] = 3 / 4 ∧
      gonshorValue [0, 0, 1] = 3 / 2 ∧ gonshorValue [0, 0, 0] = 3 := by
  norm_num [gonshorValue, gonshorFrom, gonshorDyadicTail, gonshorSign]

theorem gonshor_paper_example :
    gonshorValue [0, 0, 1, 0, 1, 0] = 27 / 16 := by
  norm_num [gonshorValue, gonshorFrom, gonshorDyadicTail, gonshorSign]

/-- Literal strict form of equation (56) fails at the constant-sign endpoint already on day one. -/
theorem gonshor_strict_day_bound_counterexample :
    ¬ (-(1 : ℚ) < gonshorValue [0] ∧ gonshorValue [0] < (1 : ℚ)) := by
  norm_num [gonshorValue, gonshorFrom, gonshorSign]

/-- No rational number squares to two. -/
theorem rational_square_ne_two (q : ℚ) : q ^ (2 : ℕ) ≠ 2 := by
  intro hq
  have hr : (q : ℝ) ^ (2 : ℕ) = (Real.sqrt 2) ^ (2 : ℕ) := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    exact_mod_cast hq
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hr with h | h
  · exact irrational_sqrt_two.ne_rat q h.symm
  · exact irrational_sqrt_two.ne_rat (-q) (by
      simpa using (congrArg Neg.neg h).symm)

/-- Finite Gonshor values cannot yet supply the algebraic number `√2`. -/
theorem gonshorValue_square_ne_two (xs : List (Fin 2)) :
    gonshorValue xs ^ (2 : ℕ) ≠ 2 :=
  rational_square_ne_two _

/-- Exactly `2^n` length-`n` sign strings occur on day `n`. -/
theorem gonshorDay_card (n : ℕ) :
    Fintype.card (Quantum.NQubitBasis n) = 2 ^ n := by
  simp [Quantum.NQubitBasis]

/-- Through day `j`, the finite construction contains `2^(j+1)-1` strings. -/
theorem gonshorCumulativeDay_card (j : ℕ) :
    (∑ n ∈ Finset.range (j + 1), 2 ^ n) = 2 ^ (j + 1) - 1 := by
  induction j with
  | zero => norm_num
  | succ j ih =>
      rw [show j + 1 + 1 = (j + 1) + 1 by omega, Finset.sum_range_succ, ih]
      rw [pow_succ, pow_succ]
      omega

/-- Interpret a QECLean basis label as its finite Gonshor sign string. -/
def qecGonshorValue {n : ℕ} (a : Quantum.NQubitBasis n) : ℚ :=
  gonshorValue (List.ofFn a)

/-- Qubit bit-complement is surreal sign negation. -/
theorem qecGonshorValue_complement {n : ℕ} (a : Quantum.NQubitBasis n) :
    qecGonshorValue (fun i => Fin.rev (a i)) = -qecGonshorValue a := by
  rw [qecGonshorValue, qecGonshorValue, List.ofFn_comp']
  exact gonshorValue_complement _

/-- Affine normalization sends Gonshor sign negation to the corpus rational binary swap. -/
def gonshorProbability (xs : List (Fin 2)) : ℚ := (gonshorValue xs + 1) / 2

theorem gonshorProbability_complement (xs : List (Fin 2)) :
    gonshorProbability (xs.map Fin.rev) = rationalBinarySwap (gonshorProbability xs) := by
  rw [gonshorProbability, gonshorProbability, gonshorValue_complement]
  simp only [rationalBinarySwap]
  ring

theorem gonshorProbability_fixed_iff_zero (xs : List (Fin 2)) :
    rationalBinarySwap (gonshorProbability xs) = gonshorProbability xs ↔
      gonshorValue xs = 0 := by
  rw [rationalBinarySwap_fixed_iff_half_closed]
  simp only [gonshorProbability]
  constructor <;> intro h
  · linarith
  · rw [h]
    norm_num

/-- Boolean form of a qubit bit, for comparison with the corpus Walsh cube. -/
def finBitBool (b : Fin 2) : Bool := decide (b = 1)

theorem gonshorSign_eq_binaryGaugeSign (b : Fin 2) :
    (gonshorSign b : ℝ) = RHTower.binaryGaugeSign (finBitBool b) := by
  fin_cases b <;> norm_num [gonshorSign, finBitBool, RHTower.binaryGaugeSign]

end

end GaloisForLFunctions.Nieto1810
