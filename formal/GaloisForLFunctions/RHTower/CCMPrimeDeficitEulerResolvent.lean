import GaloisForLFunctions.RHTower.CCMPrimeDeficitEulerRenewal
import Mathlib.Data.Nat.Log

/-!
# A finite positive inverse for the Euler renewal equation

Every nontrivial rough factor is at least two. Thus the squared renewal
kernel starts at four, and its `k`th power starts at `4^k`. At each finite
time a geometric inverse terminates exactly. No infinite series or
contraction estimate is assumed. Positivity of its coefficients alone
does not bound their size at the critical exponent.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

theorem logarithmicWeightedDilation_arithmetic_mul
    (a b : ArithmeticFunction ℝ) (f : ℝ → ℝ) (T : ℝ) :
    logarithmicWeightedDilation a (logarithmicWeightedDilation b f) T =
      logarithmicWeightedDilation (a * b : ArithmeticFunction ℝ) f T := by
  rw [logarithmicWeightedDilation_comp]
  rfl

theorem logarithmicWeightedDilation_arithmetic_sub
    (a b : ArithmeticFunction ℝ) (f : ℝ → ℝ) (T : ℝ) :
    logarithmicWeightedDilation (a - b : ArithmeticFunction ℝ) f T =
      logarithmicWeightedDilation a f T - logarithmicWeightedDilation b f T := by
  simp only [sub_eq_add_neg, logarithmicWeightedDilation, ArithmeticFunction.add_apply,
    ArithmeticFunction.neg_apply, add_mul, neg_mul, Finset.sum_add_distrib,
    Finset.sum_neg_distrib]

theorem logarithmicWeightedDilation_arithmetic_one (f : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) :
    logarithmicWeightedDilation (1 : ArithmeticFunction ℝ) f T = f T := by
  have hN : 1 ≤ ⌊Real.exp T⌋₊ :=
    (Nat.le_floor_iff (Real.exp_pos T).le).mpr (by simpa using Real.one_le_exp_iff.mpr hT)
  simp [logarithmicWeightedDilation, ArithmeticFunction.one_apply, hN]

def ccmEulerRenewalKernel (P : ℕ) : ArithmeticFunction ℝ := ccmEulerRough P ^ 2

def ccmEulerResolvent (P k : ℕ) : ArithmeticFunction ℝ :=
  ∑ j ∈ Finset.range k, ccmEulerRenewalKernel P ^ j

private theorem arithmetic_mul_nonneg (a b : ArithmeticFunction ℝ)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) (n : ℕ) : 0 ≤ (a * b) n := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg fun _ _ => mul_nonneg (ha _) (hb _)

theorem ccmEulerRenewalKernel_nonneg (P n : ℕ) : 0 ≤ ccmEulerRenewalKernel P n := by
  rw [ccmEulerRenewalKernel, pow_two]
  exact arithmetic_mul_nonneg _ _ (ccmEulerRough_nonneg P) (ccmEulerRough_nonneg P) n

theorem ccmEulerResolvent_nonneg (P k n : ℕ) : 0 ≤ ccmEulerResolvent P k n := by
  have hp : ∀ j n, 0 ≤ (ccmEulerRenewalKernel P ^ j) n := by
    intro j
    induction j with
    | zero =>
      intro n
      simp only [pow_zero, ArithmeticFunction.one_apply]
      split <;> norm_num
    | succ j ih =>
      intro n
      rw [pow_succ]
      exact arithmetic_mul_nonneg _ _ ih (ccmEulerRenewalKernel_nonneg P) n
  induction k with
  | zero => simp [ccmEulerResolvent]
  | succ k ih =>
    simpa only [ccmEulerResolvent, Finset.sum_range_succ, ArithmeticFunction.add_apply]
      using add_nonneg ih (hp k n)

theorem ccmEulerRenewalKernel_pow_vanishesBelow (P k : ℕ) :
    Sieve.VanishesBelow (ccmEulerRenewalKernel P ^ k) (4 ^ k) := by
  have hq : Sieve.VanishesBelow (ccmEulerRough P) 2 := by
    intro n hn
    change (if 1 < n ∧ n.Coprime P then (1 : ℝ) else 0) = 0
    exact if_neg (by omega)
  have hb : Sieve.VanishesBelow (ccmEulerRenewalKernel P) 4 := by
    simpa only [ccmEulerRenewalKernel, pow_two] using Sieve.vanishesBelow_mul hq hq
  exact Sieve.vanishesBelow_pow hb

/-- Exact finite geometric transport, retaining the unestimated last remainder. -/
theorem ccmEulerResolvent_action_identity (P k : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    logarithmicWeightedDilation (ccmEulerResolvent P k) (ccmPrimeDeficitEulerAction P) T =
      ccmLogChebyshevDeficitPrimitive T -
        logarithmicWeightedDilation (ccmEulerRenewalKernel P ^ k : ArithmeticFunction ℝ)
          ccmLogChebyshevDeficitPrimitive T := by
  have ha : ∀ t, 0 ≤ t → ccmPrimeDeficitEulerAction P t =
      ccmLogChebyshevDeficitPrimitive t -
        logarithmicWeightedDilation (ccmEulerRenewalKernel P) ccmLogChebyshevDeficitPrimitive t := by
    intro t ht
    have h := ccmLogChebyshevDeficitPrimitive_sub_eulerAction_eq_renewal P ht
    rw [logarithmicWeightedDilation_arithmetic_mul] at h
    simp only [ccmEulerRenewalKernel, pow_two]
    linarith only [h]
  rw [logarithmicWeightedDilation_congr_nonneg _ _ _ ha T,
    logarithmicWeightedDilation_sub_profile, logarithmicWeightedDilation_arithmetic_mul,
    ← logarithmicWeightedDilation_arithmetic_sub]
  have hg : ccmEulerResolvent P k - ccmEulerResolvent P k * ccmEulerRenewalKernel P =
      1 - ccmEulerRenewalKernel P ^ k := by
    rw [← mul_one_sub]
    simpa only [ccmEulerResolvent, mul_comm] using mul_neg_geom_sum (ccmEulerRenewalKernel P) k
  rw [hg, logarithmicWeightedDilation_arithmetic_sub, logarithmicWeightedDilation_arithmetic_one _ hT]

/-- At a finite horizon, sufficiently many delayed interactions vanish exactly. -/
theorem ccmLogChebyshevDeficitPrimitive_eq_eulerResolvent
    (P k : ℕ) {T : ℝ} (hT : 0 ≤ T) (hk : ⌊Real.exp T⌋₊ < 4 ^ k) :
    ccmLogChebyshevDeficitPrimitive T =
      logarithmicWeightedDilation (ccmEulerResolvent P k) (ccmPrimeDeficitEulerAction P) T := by
  rw [ccmEulerResolvent_action_identity P k hT]
  have hz : logarithmicWeightedDilation
      (ccmEulerRenewalKernel P ^ k : ArithmeticFunction ℝ) ccmLogChebyshevDeficitPrimitive T = 0 := by
    unfold logarithmicWeightedDilation
    apply Finset.sum_eq_zero
    intro n hn
    rw [ccmEulerRenewalKernel_pow_vanishesBelow P k n ((Finset.mem_Icc.mp hn).2.trans_lt hk),
      zero_mul]
  rw [hz, sub_zero]

/-- An explicit logarithmic number of renewal steps suffices, without an estimated tail. -/
theorem ccmLogChebyshevDeficitPrimitive_eq_eulerResolvent_logDepth
    (P : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ccmLogChebyshevDeficitPrimitive T =
      logarithmicWeightedDilation (ccmEulerResolvent P (Nat.log 4 ⌊Real.exp T⌋₊ + 1))
        (ccmPrimeDeficitEulerAction P) T :=
  ccmLogChebyshevDeficitPrimitive_eq_eulerResolvent P _ hT
    (Nat.lt_pow_succ_log_self (by norm_num) _)

end RHTower
