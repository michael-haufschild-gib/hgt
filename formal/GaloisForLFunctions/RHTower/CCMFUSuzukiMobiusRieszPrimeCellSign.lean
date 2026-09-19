import GaloisForLFunctions.RHTower.CCMFUSuzukiMobiusDivisorDilationChannels

/-!
# Exact signs of prime-paired Möbius–Riesz source coefficients

Zero extension preserves the literal clipped tail, including its endpoint. A single prime
pairing produces a nonnegative clipped increment. For two distinct primes the exact sign wall
is `sqrt (n*p) + sqrt (n*q) - sqrt n`; multiplicative square-root curvature makes the
cell negative beyond that wall.

The complete signed tail is homogeneous under integral dilation and has both positive and
negative families at every scale. The local divisor increment at one is positive, so one
channel of the completed source pairing is strictly negative as well. These source sign laws
do not determine the sign or boundedness of the joint completed sum.
-/

open Finset
noncomputable section
namespace RHTower.MobiusRieszCancellation

/-- Literal tail coefficient, extended by zero across the physical cutoff. -/
def atom (M n d : ℕ) : ℝ :=
  if n * d < M then Real.sqrt M - Real.sqrt (n * d : ℕ) else 0

theorem atom_eq_positivePart (M n d : ℕ) :
    atom M n d = max (Real.sqrt M - Real.sqrt (n * d : ℕ)) 0 := by
  by_cases h : n * d < M
  · have hs : Real.sqrt (n * d : ℕ) ≤ Real.sqrt M :=
      Real.sqrt_le_sqrt (by exact_mod_cast h.le)
    rw [atom, if_pos h, max_eq_left (sub_nonneg.mpr hs)]
  · have hs : Real.sqrt M ≤ Real.sqrt (n * d : ℕ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast (Nat.le_of_not_gt h))
    rw [atom, if_neg h, max_eq_right (sub_nonpos.mpr hs)]

/-- No tail term or endpoint correction is lost in the zero extension. -/
theorem tail_eq_zeroExtended (M n : ℕ) (hn : 1 ≤ n) :
    mobiusDilationRieszTail M n =
      ∑ d ∈ Icc 1 (M - 1), ((ArithmeticFunction.moebius d : ℤ) : ℝ) * atom M n d := by
  have hsub : Icc 1 ((M - 1) / n) ⊆ Icc 1 (M - 1) := by
    intro d hd
    exact mem_Icc.mpr ⟨(mem_Icc.mp hd).1,
      (mem_Icc.mp hd).2.trans (Nat.div_le_self _ _)⟩
  unfold mobiusDilationRieszTail
  calc
    (∑ d ∈ Icc 1 ((M - 1) / n),
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        (Real.sqrt M - Real.sqrt (n * d : ℕ))) =
      ∑ d ∈ Icc 1 ((M - 1) / n),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * atom M n d := by
      apply sum_congr rfl
      intro d hd
      have hdpos := (mem_Icc.mp hd).1
      have hmul : d * n ≤ M - 1 :=
        (Nat.le_div_iff_mul_le (by omega : 0 < n)).mp (mem_Icc.mp hd).2
      have hprod : 0 < d * n := Nat.mul_pos (by omega) (by omega)
      have hactive : n * d < M := by rw [Nat.mul_comm]; omega
      rw [atom, if_pos hactive]
    _ = _ := sum_subset hsub (by
      intro d hd hnot
      have hdpos := (mem_Icc.mp hd).1
      have hinactive : ¬n * d < M := by
        intro hlt
        apply hnot
        apply mem_Icc.mpr
        refine ⟨hdpos, ?_⟩
        apply (Nat.le_div_iff_mul_le (by omega : 0 < n)).mpr
        rw [Nat.mul_comm]
        omega
      simp [atom, hinactive])

private def hinge (x a : ℝ) : ℝ := max (x - a) 0

/-- A first pairing cancels the common cutoff and leaves a nonnegative clipped increment. -/
private theorem first_pair (x a b : ℝ) (hab : a ≤ b) :
    hinge x a - hinge x b = min (max (x - a) 0) (b - a) := by
  simp only [hinge, max_def, min_def]
  split_ifs <;> linarith

/-- Exact nonnegative remainder after one literal prime pairing. -/
theorem literal_firstPrime_cancellation (M n p : ℕ) (hp : p.Prime) :
    (atom M n 1 + ((ArithmeticFunction.moebius p : ℤ) : ℝ) * atom M n p =
      min (max (Real.sqrt M - Real.sqrt n) 0)
        (Real.sqrt (n * p : ℕ) - Real.sqrt n)) ∧
    0 ≤ atom M n 1 + ((ArithmeticFunction.moebius p : ℤ) : ℝ) * atom M n p := by
  have hnp : n ≤ n * p := Nat.le_mul_of_pos_right n (by have := hp.one_lt; omega)
  have hroot : Real.sqrt n ≤ Real.sqrt (n * p : ℕ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hnp)
  have heq : atom M n 1 + ((ArithmeticFunction.moebius p : ℤ) : ℝ) * atom M n p =
      min (max (Real.sqrt M - Real.sqrt n) 0)
        (Real.sqrt (n * p : ℕ) - Real.sqrt n) := by
    simpa [atom_eq_positivePart, ArithmeticFunction.moebius_apply_prime hp, hinge,
      sub_eq_add_neg] using
      first_pair (Real.sqrt M) (Real.sqrt n) (Real.sqrt (n * p : ℕ)) hroot
  refine ⟨heq, ?_⟩
  rw [heq]
  exact le_min (le_max_right _ _) (sub_nonneg.mpr hroot)

private def fourHinge (x a b c d : ℝ) : ℝ :=
  hinge x a - hinge x b - hinge x c + hinge x d

private theorem fourHinge_signs (x a b c d : ℝ)
    (hab : a < b) (hac : a < c) (hwall : b + c - a < d) :
    (fourHinge x a b c d < 0 ↔ b + c - a < x) ∧
    (0 < fourHinge x a b c d ↔ a < x ∧ x < b + c - a) := by
  constructor
  · simp only [fourHinge, hinge, max_def]
    split_ifs <;> constructor <;> intro h <;> linarith
  · simp only [fourHinge, hinge, max_def]
    split_ifs <;> constructor
    all_goals intro h
    all_goals first | (constructor <;> linarith) | (rcases h with ⟨h₁,h₂⟩; linarith)

/-- The four literal Möbius coefficients on a two-prime divisor cell. -/
def primeCell (M n p q : ℕ) : ℝ :=
  ∑ d ∈ ({1, p, q, p * q} : Finset ℕ),
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) * atom M n d

private theorem primeCell_eq_fourHinge (M n p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    primeCell M n p q = fourHinge (Real.sqrt M) (Real.sqrt n)
      (Real.sqrt (n * p : ℕ)) (Real.sqrt (n * q : ℕ))
      (Real.sqrt (n * (p * q) : ℕ)) := by
  have hcop : p.Coprime q := hp.coprime_iff_not_dvd.mpr
    (fun h => hpq ((Nat.dvd_prime hq).mp h |>.resolve_left hp.ne_one))
  have hmu : ArithmeticFunction.moebius (p * q) = 1 := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      ArithmeticFunction.moebius_apply_prime hp, ArithmeticFunction.moebius_apply_prime hq]
    ring
  have hppq : p ≠ p * q := by nlinarith [hp.one_lt, hq.one_lt]
  have hqpq : q ≠ p * q := by nlinarith [hp.one_lt, hq.one_lt]
  have hone : 1 ≠ p * q := by nlinarith [hp.one_lt, hq.one_lt]
  simp [primeCell, Ne.symm hp.ne_one, Ne.symm hq.ne_one,
    hpq, hppq, hqpq, hone, hmu, ArithmeticFunction.moebius_apply_prime hp,
    ArithmeticFunction.moebius_apply_prime hq, atom_eq_positivePart, fourHinge, hinge]
  ring

private theorem sqrt_cell_geometry (n p q : ℕ) (hn : 1 ≤ n)
    (hp : 1 < p) (hq : 1 < q) :
    Real.sqrt n < Real.sqrt (n * p : ℕ) ∧
    Real.sqrt n < Real.sqrt (n * q : ℕ) ∧
    Real.sqrt (n * p : ℕ) + Real.sqrt (n * q : ℕ) - Real.sqrt n <
      Real.sqrt (n * (p * q) : ℕ) := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hnroot : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hpr : (1 : ℝ) < Real.sqrt p := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)
      (by exact_mod_cast hp : (1 : ℝ) < p)
    simpa using h
  have hqr : (1 : ℝ) < Real.sqrt q := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)
      (by exact_mod_cast hq : (1 : ℝ) < q)
    simpa using h
  have hcurv : 0 < Real.sqrt n * ((Real.sqrt p - 1) * (Real.sqrt q - 1)) :=
    mul_pos hnroot (mul_pos (sub_pos.mpr hpr) (sub_pos.mpr hqr))
  push_cast
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ n),
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ n),
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ n),
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ p)]
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- Exact sign wall for the actual Möbius two-prime cell, including its clipped boundary. -/
theorem literal_primeCell_sign_wall :
    ∀ M n p q : ℕ, 1 ≤ n → p.Prime → q.Prime → p ≠ q →
      (primeCell M n p q < 0 ↔
        Real.sqrt (n * p : ℕ) + Real.sqrt (n * q : ℕ) - Real.sqrt n < Real.sqrt M) ∧
      (0 < primeCell M n p q ↔
        Real.sqrt n < Real.sqrt M ∧
        Real.sqrt M < Real.sqrt (n * p : ℕ) + Real.sqrt (n * q : ℕ) - Real.sqrt n) := by
  intro M n p q hn hp hq hpq
  rw [primeCell_eq_fourHinge M n p q hp hq hpq]
  obtain ⟨ha, hb, hc⟩ := sqrt_cell_geometry n p q hn hp.one_lt hq.one_lt
  exact fourHinge_signs _ _ _ _ _ ha hb hc

/-- Exact dilation of the complete signed tail, not of a selected subcell. -/
theorem tail_dilate (M n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    mobiusDilationRieszTail (k * M) (k * n) =
      Real.sqrt k * mobiusDilationRieszTail M n := by
  by_cases hM : M = 0
  · subst M
    simp [mobiusDilationRieszTail]
  have hM0 : 0 < M := by omega
  have hk0 : 0 < k := by omega
  have hn0 : 0 < n := by omega
  have hkn : 0 < k * n := Nat.mul_pos hk0 hn0
  have hkM : 0 < k * M := Nat.mul_pos hk0 hM0
  have hcut (d : ℕ) : d ≤ (k * M - 1) / (k * n) ↔ d ≤ (M - 1) / n := by
    rw [Nat.le_div_iff_mul_le hkn, Nat.le_div_iff_mul_le hn0]
    constructor
    · intro h
      have hmul : k * (d * n) < k * M := by
        calc k * (d * n) = d * (k * n) := by ring
             _ < k * M := by omega
      have hsmall : d * n < M := (Nat.mul_lt_mul_left hk0).mp hmul
      omega
    · intro h
      have hsmall : d * n < M := by omega
      have hmul := Nat.mul_lt_mul_of_pos_left hsmall hk0
      have hprod : d * (k * n) < k * M := by
        calc d * (k * n) = k * (d * n) := by ring
             _ < k * M := hmul
      omega
  have hquot : (k * M - 1) / (k * n) = (M - 1) / n :=
    Nat.le_antisymm ((hcut _).mp le_rfl) ((hcut _).mpr le_rfl)
  unfold mobiusDilationRieszTail
  rw [hquot, Finset.mul_sum]
  apply sum_congr rfl
  intro d _
  rw [show k * n * d = k * (n * d) by ring]
  push_cast
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ k),
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ k)]
  ring

private theorem tail_two_positive : 0 < mobiusDilationRieszTail 2 1 := by
  have hroot : (1 : ℝ) < Real.sqrt 2 := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (1 : ℝ) < 2)
    simpa using h
  norm_num [mobiusDilationRieszTail]
  linarith

private theorem tail_six_negative : mobiusDilationRieszTail 6 1 < 0 := by
  have hfour : ArithmeticFunction.moebius 4 = 0 := by
    have h := ArithmeticFunction.moebius_apply_prime_pow Nat.prime_two
      (by norm_num : (2 : ℕ) ≠ 0)
    norm_num at h
    exact h
  have hprod : Real.sqrt (2 : ℝ) * Real.sqrt 3 = Real.sqrt 6 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hs6 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)
  have h23 : Real.sqrt (2 : ℝ) + Real.sqrt 3 < 1 + Real.sqrt 6 := by
    nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ),
      Real.sqrt_nonneg (6 : ℝ)]
  have h56 : Real.sqrt (5 : ℝ) < Real.sqrt 6 :=
    Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  norm_num [mobiusDilationRieszTail, Finset.sum_Icc_succ_top, hfour,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime Nat.prime_three,
    ArithmeticFunction.moebius_apply_prime Nat.prime_five]
  linarith

/-- Both signs persist at every integral dilation of the literal tail. -/
theorem literal_tail_both_signs_on_every_scale :
    ∀ n : ℕ, 1 ≤ n →
      0 < mobiusDilationRieszTail (2 * n) n ∧
      mobiusDilationRieszTail (6 * n) n < 0 := by
  intro n hn
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by positivity)
  constructor
  · have h := tail_dilate 2 1 n (by omega) hn
    have heq : mobiusDilationRieszTail (2 * n) n =
        Real.sqrt n * mobiusDilationRieszTail 2 1 := by
      simpa only [mul_one, Nat.mul_comm n 2] using h
    rw [heq]
    exact mul_pos hr tail_two_positive
  · have h := tail_dilate 6 1 n (by omega) hn
    have heq : mobiusDilationRieszTail (6 * n) n =
        Real.sqrt n * mobiusDilationRieszTail 6 1 := by
      simpa only [mul_one, Nat.mul_comm n 6] using h
    rw [heq]
    exact mul_neg_of_pos_of_neg hr tail_six_negative

/-- A literal coefficient of the completed source pairing is negative. -/
theorem literal_primeFreeDivisor_source_channel_negative :
    primeFreeDivisorIncrement 1 * mobiusDilationRieszTail 6 1 < 0 := by
  have hs : 0 < primeFreeDivisorIncrement 1 := by
    simp only [primeFreeDivisorIncrement, Nat.cast_one, Real.log_one,
      Nat.divisors_one, Finset.card_singleton]
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  exact mul_neg_of_pos_of_neg hs tail_six_negative


end RHTower.MobiusRieszCancellation
