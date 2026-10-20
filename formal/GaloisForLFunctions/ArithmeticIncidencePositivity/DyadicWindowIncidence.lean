import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimePowerIncidenceDominance
import GaloisForLFunctions.SquareRootThreshold.LargeDyadicPrimeWindowsDecideTheCriticalLine

/-!
# Incidence inside a dyadic window

The single-window criteria of the square-root threshold programme read the primes of one dyadic
window `(X/2, 2X)` per test. Inside one such window the incidence structure of the integers is
very restricted:

* two elements `a < b` of the window have ratio `b/a < 4`, so a divisor relation `a ∣ b` inside the
  window is a doubling or a tripling: the same-side prime atoms inside a window are only
  `Λ(2)/√2` and `Λ(3)/√3`;
* a crossing pair `a < b` inside the window with `ab` a prime power consists of two consecutive
  powers of `2` or of `3`; a prime `p ≥ 5` has at most one power in any dyadic window, and `2` and
  `3` have at most two;
* every crossing prime atom inside the window at scale `X` is below `2 log 3 / X`.

So within a single window the negative prime atoms are few (at most one pair for `2` and one for
`3`) and small, while the same-side atoms are of size one. The arithmetic coupling between
different windows, through the same-side atoms `Λ(m)/√m` at ratios `m ≥ 4` and the crossing atoms
at products, is where the window problem leaves the window.
-/

open ArithmeticFunction RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-- The open dyadic window `(X/2, 2X)` of integers at scale `X`. -/
def InDyadicWindow (X : ℝ) (n : ℕ) : Prop := X / 2 < n ∧ (n : ℝ) < 2 * X

/-- Two elements of one window have ratio below `4`. -/
theorem lt_four_mul_of_inDyadicWindow {X : ℝ} {a b : ℕ} (ha : InDyadicWindow X a)
    (hb : InDyadicWindow X b) : (b : ℝ) < 4 * a := by
  obtain ⟨ha1, -⟩ := ha
  obtain ⟨-, hb2⟩ := hb
  linarith

/-- **Window divisibility.** A proper divisor relation inside a dyadic window is a doubling or a
tripling. -/
theorem eq_two_mul_or_three_mul_of_dvd {X : ℝ} {a b : ℕ} (ha : InDyadicWindow X a)
    (hb : InDyadicWindow X b) (hab : a < b) (hdvd : a ∣ b) : b = 2 * a ∨ b = 3 * a := by
  obtain ⟨k, rfl⟩ := hdvd
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h; simp at hab
    · exact h
  have hk4 : k < 4 := by
    have h := lt_four_mul_of_inDyadicWindow ha hb
    push_cast at h
    have h' : a * k < a * 4 := by
      exact_mod_cast (by linarith : (a : ℝ) * k < (a : ℝ) * 4)
    exact Nat.lt_of_mul_lt_mul_left h'
  have hk1 : 1 < k := by
    by_contra hk
    have : a * k ≤ a * 1 := Nat.mul_le_mul_left a (by omega)
    omega
  interval_cases k
  · left; ring
  · right; ring

/-- Inside a window the same-side atom is `0`, `Λ(2)/√2` or `Λ(3)/√3`. -/
theorem ratioAtom_inDyadicWindow {X : ℝ} {a b : ℕ} (ha : InDyadicWindow X a)
    (hb : InDyadicWindow X b) (hab : a < b) :
    ratioAtom a b = 0 ∨ ratioAtom a b = vonMangoldtAtom 2 ∨ ratioAtom a b = vonMangoldtAtom 3 := by
  unfold ratioAtom
  split_ifs with h
  · have ha0 : 0 < a := by
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · subst h0
        rw [zero_dvd_iff] at h
        omega
      · exact h0
    rcases eq_two_mul_or_three_mul_of_dvd ha hb hab h with rfl | rfl
    · right; left; rw [Nat.mul_div_cancel 2 ha0]
    · right; right; rw [Nat.mul_div_cancel 3 ha0]
  · left; rfl

/-- Two powers of one prime in a common window have exponents at distance at most one. -/
theorem exponent_sub_le_one_of_inDyadicWindow {X : ℝ} {p i j : ℕ} (hp : p.Prime)
    (hi : InDyadicWindow X (p ^ i)) (hj : InDyadicWindow X (p ^ j)) : j ≤ i + 1 := by
  by_contra hc
  have h2 : i + 2 ≤ j := by omega
  have h := lt_four_mul_of_inDyadicWindow hi hj
  push_cast at h
  have h' : p ^ j < p ^ i * 4 := by
    exact_mod_cast (by linarith : (p : ℝ) ^ j < (p : ℝ) ^ i * 4)
  have hpow : p ^ i * 4 ≤ p ^ j := by
    calc p ^ i * 4 ≤ p ^ i * p ^ 2 := Nat.mul_le_mul_left _ (by nlinarith [hp.two_le])
      _ = p ^ (i + 2) := by rw [← pow_add]
      _ ≤ p ^ j := Nat.pow_le_pow_right hp.pos h2
  omega

/-- A prime `p ≥ 5` has at most one power in a dyadic window. -/
theorem exponent_eq_of_inDyadicWindow_of_five_le {X : ℝ} {p i j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hi : InDyadicWindow X (p ^ i)) (hj : InDyadicWindow X (p ^ j)) : i = j := by
  wlog hij : i ≤ j generalizing i j
  · exact (this hj hi (by omega)).symm
  have h1 := exponent_sub_le_one_of_inDyadicWindow hp hi hj
  by_contra hne
  have hj' : j = i + 1 := by omega
  subst hj'
  have h := lt_four_mul_of_inDyadicWindow hi hj
  push_cast at h
  have h' : p ^ (i + 1) < p ^ i * 4 := by
    exact_mod_cast (by linarith : (p : ℝ) ^ (i + 1) < (p : ℝ) ^ i * 4)
  rw [pow_succ] at h'
  have hpi : 0 < p ^ i := pow_pos hp.pos i
  have : p < 4 := Nat.lt_of_mul_lt_mul_left h'
  omega

/-- **Window crossing pairs.** If `a < b` lie in one window and `ab` is a prime power, then
`(a, b) = (p^i, p^{i+1})` with `p ∈ {2, 3}`. -/
theorem consecutive_powers_of_isPrimePow_mul {X : ℝ} {a b : ℕ} (ha : InDyadicWindow X a)
    (hb : InDyadicWindow X b) (hab : a < b) (h : IsPrimePow (a * b)) :
    ∃ p i : ℕ, (p = 2 ∨ p = 3) ∧ a = p ^ i ∧ b = p ^ (i + 1) := by
  obtain ⟨p, i, j, hp, rfl, rfl, -⟩ := exists_prime_pow_of_isPrimePow_mul h
  have hij : i < j := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hab
  have hj : j = i + 1 := by
    have := exponent_sub_le_one_of_inDyadicWindow hp ha hb
    omega
  subst hj
  refine ⟨p, i, ?_, rfl, rfl⟩
  have hdvd : p ^ i ∣ p ^ (i + 1) := Nat.pow_dvd_pow p (by omega)
  have hpi : 0 < p ^ i := pow_pos hp.pos i
  rcases eq_two_mul_or_three_mul_of_dvd ha hb hab hdvd with h2 | h3
  · left
    rw [pow_succ, mul_comm] at h2
    exact Nat.eq_of_mul_eq_mul_right hpi (by rw [mul_comm] at h2; linarith)
  · right
    rw [pow_succ, mul_comm] at h3
    exact Nat.eq_of_mul_eq_mul_right hpi (by rw [mul_comm] at h3; linarith)

/-- **Window crossing atoms are small.** Inside the window at scale `X > 0` every crossing prime
atom is below `2 log 3 / X`. -/
theorem productAtom_lt_of_inDyadicWindow {X : ℝ} (hX : 0 < X) {a b : ℕ} (ha : InDyadicWindow X a)
    (hb : InDyadicWindow X b) (hab : a < b) : productAtom a b < 2 * Real.log 3 / X := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  by_cases h : IsPrimePow (a * b)
  · obtain ⟨p, i, hp23, rfl, rfl⟩ := consecutive_powers_of_isPrimePow_mul ha hb hab h
    have hp : p.Prime := by rcases hp23 with rfl | rfl <;> norm_num
    rw [productAtom_pow_pow hp (by omega)]
    have hlogp : Real.log p ≤ Real.log 3 := by
      rcases hp23 with rfl | rfl
      · exact Real.log_le_log (by norm_num) (by norm_num)
      · exact le_rfl
    have hsqrt : X / 2 < Real.sqrt ((p ^ (i + (i + 1)) : ℕ) : ℝ) := by
      have hA : (0 : ℝ) < (p : ℝ) ^ i := pow_pos (by exact_mod_cast hp.pos) i
      have h1 : X / 2 < (p : ℝ) ^ i := by
        have := ha.1
        push_cast at this
        exact this
      have h2 : (p : ℝ) ^ i ≤ (p : ℝ) ^ (i + 1) := by
        exact_mod_cast Nat.pow_le_pow_right hp.pos (by omega)
      have h3 : (X / 2) ^ 2 < ((p ^ (i + (i + 1)) : ℕ) : ℝ) := by
        rw [pow_add]
        push_cast
        calc (X / 2) ^ 2 < ((p : ℝ) ^ i) ^ 2 := by nlinarith
          _ = (p : ℝ) ^ i * (p : ℝ) ^ i := sq _
          _ ≤ (p : ℝ) ^ i * (p : ℝ) ^ (i + 1) := mul_le_mul_of_nonneg_left h2 hA.le
      exact (Real.lt_sqrt (by linarith)).mpr h3
    calc Real.log p / Real.sqrt ((p ^ (i + (i + 1)) : ℕ) : ℝ)
        ≤ Real.log 3 / Real.sqrt ((p ^ (i + (i + 1)) : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right hlogp (Real.sqrt_nonneg _)
      _ < Real.log 3 / (X / 2) := div_lt_div_of_pos_left hlog3 (by linarith) hsqrt
      _ = 2 * Real.log 3 / X := by field_simp
  · rw [productAtom_eq_zero_of_not_isPrimePow h]
    positivity

/-! ### The windows of the square-root threshold programme -/

/-- The window `|log n − v| ≤ 2w` with `2w < log 2` of a two-bump test lies inside the dyadic
window at scale `e^v`, for `n ≥ 1`. -/
theorem inDyadicWindow_of_mem_lagPrimeWindow {v w : ℝ} (hw : 2 * w < Real.log 2) {n : ℕ}
    (hn1 : 1 ≤ n) (hn : n ∈ SquareRootThreshold.lagPrimeWindow v w) :
    InDyadicWindow (Real.exp v) n := by
  obtain ⟨-, h⟩ := Finset.mem_filter.mp hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  obtain ⟨h1, h2⟩ := abs_le.mp h
  constructor
  · have : Real.exp (v - Real.log 2) < Real.exp (Real.log n) :=
      Real.exp_lt_exp.mpr (by linarith)
    rwa [Real.exp_sub, Real.exp_log two_pos, Real.exp_log hn0] at this
  · have : Real.exp (Real.log n) < Real.exp (v + Real.log 2) :=
      Real.exp_lt_exp.mpr (by linarith)
    rwa [Real.exp_add, Real.exp_log two_pos, Real.exp_log hn0, mul_comm] at this

/-- Inside the window of a two-bump test, a divisor relation is a doubling or a tripling. -/
theorem eq_two_mul_or_three_mul_of_mem_lagPrimeWindow {v w : ℝ} (hw : 2 * w < Real.log 2)
    {a b : ℕ} (ha1 : 1 ≤ a) (ha : a ∈ SquareRootThreshold.lagPrimeWindow v w)
    (hb : b ∈ SquareRootThreshold.lagPrimeWindow v w) (hab : a < b) (hdvd : a ∣ b) :
    b = 2 * a ∨ b = 3 * a :=
  eq_two_mul_or_three_mul_of_dvd (inDyadicWindow_of_mem_lagPrimeWindow hw ha1 ha)
    (inDyadicWindow_of_mem_lagPrimeWindow hw (by omega) hb) hab hdvd

/-- Inside the window of a two-bump test at lag `v`, every crossing prime atom is below
`2 log 3 · e^{−v}`. -/
theorem productAtom_lt_of_mem_lagPrimeWindow {v w : ℝ} (hw : 2 * w < Real.log 2) {a b : ℕ}
    (ha1 : 1 ≤ a) (ha : a ∈ SquareRootThreshold.lagPrimeWindow v w)
    (hb : b ∈ SquareRootThreshold.lagPrimeWindow v w) (hab : a < b) :
    productAtom a b < 2 * Real.log 3 / Real.exp v :=
  productAtom_lt_of_inDyadicWindow (Real.exp_pos v)
    (inDyadicWindow_of_mem_lagPrimeWindow hw ha1 ha)
    (inDyadicWindow_of_mem_lagPrimeWindow hw (by omega) hb) hab

end GaloisForLFunctions.ArithmeticIncidencePositivity
