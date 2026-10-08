import GaloisForLFunctions.RHTower.WeilWorkPBAPJointWidthPhase

/-!
# Arithmetic scale of the actual nearest prime half-log node

Prime nonsquareness separates the floor square root from the prime by at
least one. The resulting logarithmic lag is strictly negative, with absolute
value between 1/(2p) and 2 exp(-L), L=log(p)/2. Its inverse logarithmic scale
therefore lies between L-log(2) and 2L+log(2).
-/

open Complex MeasureTheory Real Set Filter Topology Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP

/-- A prime is separated by at least one from the square of its floor root. -/
theorem jointPrime_nearest_square_lt (p : Nat.Primes) :
    jointNearestInteger (Real.log (p:ℕ)/2)^2 < (p:ℕ) := by
  let L := Real.log (p:ℕ)/2
  let n := jointNearestInteger L
  have hp : 0 < ((p:ℕ):ℝ) := by exact_mod_cast p.2.pos
  have hn : (n:ℝ) ≤ Real.exp L := Nat.floor_le (Real.exp_pos L).le
  have he : (Real.exp L)^2 = ((p:ℕ):ℝ) := by
    rw [pow_two, ← Real.exp_add, show L+L=Real.log (p:ℕ) by dsimp [L]; ring,
      Real.exp_log hp]
  have hsq : (n:ℝ)^2 ≤ ((p:ℕ):ℝ) := by
    rw [← he]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hn 2
  have hnat : n^2 ≤ (p:ℕ) := by exact_mod_cast hsq
  have hne : n^2 ≠ (p:ℕ) := by
    intro h
    have hnp : (n^2).Prime := h.symm ▸ p.2
    exact Nat.Prime.not_prime_pow (by norm_num : 2 ≤ (2:ℕ)) hnp
  exact lt_of_le_of_ne hnat hne

/-- Integer separation bounds the actual prime half-log lag away from zero. -/
theorem jointPrime_integer_lag_lower (p : Nat.Primes) :
    1/(2*((p:ℕ):ℝ)) ≤ -jointIntegerLag (Real.log (p:ℕ)/2) := by
  let L := Real.log (p:ℕ)/2
  let n := jointNearestInteger L
  have hp : 0 < ((p:ℕ):ℝ) := by exact_mod_cast p.2.pos
  have hp1 : (1:ℝ) ≤ ((p:ℕ):ℝ) := by exact_mod_cast p.2.one_le
  have hL : 0 ≤ L := div_nonneg (Real.log_nonneg hp1) (by norm_num)
  have he : (1:ℝ) ≤ Real.exp L := by
    calc 1 = Real.exp 0 := Real.exp_zero.symm
         _ ≤ _ := Real.exp_le_exp.mpr hL
  have hn1 : 1 ≤ n := Nat.le_floor (by simpa only [Nat.cast_one] using he)
  have hn : 0 < (n:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hsqnat : n^2+1 ≤ (p:ℕ) := jointPrime_nearest_square_lt p
  have hsq : (n:ℝ)^2+1 ≤ ((p:ℕ):ℝ) := by exact_mod_cast hsqnat
  have hlog := Real.log_le_sub_one_of_pos (div_pos (sq_pos_of_pos hn) hp)
  rw [Real.log_div (sq_pos_of_pos hn).ne' hp.ne', Real.log_pow] at hlog
  have hmul := mul_le_mul_of_nonneg_right hlog hp.le
  rw [sub_mul, sub_mul, div_mul_cancel₀ _ hp.ne', one_mul] at hmul
  change 1/(2*((p:ℕ):ℝ)) ≤ -(Real.log (n:ℝ)-L)
  apply (div_le_iff₀ (mul_pos (by norm_num) hp)).mpr
  dsimp [L] at *
  nlinarith only [hmul, hsq]

theorem jointPrime_integer_lag_neg (p : Nat.Primes) :
    jointIntegerLag (Real.log (p:ℕ)/2) < 0 := by
  have hp : 0 < ((p:ℕ):ℝ) := by exact_mod_cast p.2.pos
  have h := jointPrime_integer_lag_lower p
  have hp' : 0 < 1/(2*((p:ℕ):ℝ)) := by positivity
  linarith

/-- Both arithmetic lag scales are paid for the actual nearest integer. -/
theorem jointPrime_integer_lag_bounds (p : Nat.Primes)
    (hL : 1 ≤ Real.log (p:ℕ)/2) :
    1/(2*((p:ℕ):ℝ)) ≤ |jointIntegerLag (Real.log (p:ℕ)/2)| ∧
    |jointIntegerLag (Real.log (p:ℕ)/2)| ≤ 2*Real.exp (-(Real.log (p:ℕ)/2)) := by
  rw [abs_of_neg (jointPrime_integer_lag_neg p)]
  refine ⟨jointPrime_integer_lag_lower p, ?_⟩
  simpa only [abs_of_neg (jointPrime_integer_lag_neg p)] using jointIntegerLag_abs_le hL

/-- Logarithmic phase height lies between the first and second separation scales. -/
theorem jointPrime_log_lag_bounds (p : Nat.Primes)
    (hL : 1 ≤ Real.log (p:ℕ)/2) :
    Real.log (p:ℕ)/2-Real.log 2 ≤
        Real.log (1/|jointIntegerLag (Real.log (p:ℕ)/2)|) ∧
    Real.log (1/|jointIntegerLag (Real.log (p:ℕ)/2)|) ≤
        Real.log (p:ℕ)+Real.log 2 := by
  have hp : 0 < ((p:ℕ):ℝ) := by exact_mod_cast p.2.pos
  have ha : 0 < |jointIntegerLag (Real.log (p:ℕ)/2)| :=
    abs_pos.mpr (jointPrime_integer_lag_neg p).ne
  have hb := jointPrime_integer_lag_bounds p hL
  have hu := Real.log_le_log ha hb.2
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (Real.exp_pos _).ne', Real.log_exp] at hu
  have hl := Real.log_le_log (by positivity : 0 < 1/(2*((p:ℕ):ℝ))) hb.1
  rw [Real.log_div one_ne_zero (mul_pos (by norm_num : (0:ℝ)<2) hp).ne',
    Real.log_one, Real.log_mul (by norm_num : (2:ℝ)≠0) hp.ne'] at hl
  rw [one_div, Real.log_inv]
  constructor <;> linarith

end RHTower.WeilWorkPBAP
