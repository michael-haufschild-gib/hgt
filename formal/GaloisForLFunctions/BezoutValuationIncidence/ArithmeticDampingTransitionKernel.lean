import GaloisForLFunctions.BezoutValuationIncidence.DampingWorkAsArithmeticMarkovBoundaryFlux

/-!
# Finite arithmetic damping transition kernel

The exact Cesàro transform of the damped divisor transition has nonnegative
rows of mass one at nonnegative damping. These are finite identities for the
literal Möbius source; no critical Hilbert-space bound is assumed.
-/

open Finset ArithmeticFunction RHTower

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

private def adtTwist (η : ℝ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ where
  toFun n := f n * (n : ℝ) ^ (-η)
  map_zero' := by simp

private theorem adtTwist_mul (η : ℝ) (f g : ArithmeticFunction ℝ) :
    adtTwist η (f * g) = adtTwist η f * adtTwist η g := by
  ext n
  change (f * g) n * (n : ℝ) ^ (-η) = _
  simp only [ArithmeticFunction.mul_apply, sum_mul]
  apply sum_congr rfl
  intro x hx
  have he := (pmNaturalRpowHom η).map_mul x.1 x.2
  change ((x.1 * x.2 : ℕ) : ℝ) ^ (-η) =
    (x.1 : ℝ) ^ (-η) * (x.2 : ℝ) ^ (-η) at he
  rw [(Nat.mem_divisorsAntidiagonal.mp hx).1] at he
  change f x.1 * g x.2 * (n : ℝ) ^ (-η) =
    (f x.1 * (x.1 : ℝ) ^ (-η)) * (g x.2 * (x.2 : ℝ) ^ (-η))
  rw [he]
  ring

private theorem adtTwist_one (η : ℝ) : adtTwist η 1 = 1 := by
  ext n
  change (1 : ArithmeticFunction ℝ) n * (n : ℝ) ^ (-η) =
    (1 : ArithmeticFunction ℝ) n
  by_cases hn : n = 1 <;> simp [hn, ArithmeticFunction.one_apply]

private theorem adtTwist_moebius_zeta (η : ℝ) (n : ℕ) :
    (adtTwist η ((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) *
      ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)) n =
      pmPowerDampedDivisorCoeff η n := by
  rw [coe_mul_zeta_apply]
  rfl

/-- The positive divisor transition has total mass one. The identity itself
holds for every real damping, without a positivity restriction. -/
theorem arithmeticDamping_divisor_mass (η : ℝ) {n : ℕ} (hn : 0 < n) :
    (∑ d ∈ n.divisors, (d : ℝ) ^ (-η) *
      pmPowerDampedDivisorCoeff η (n / d)) = 1 := by
  have h : adtTwist η ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) *
      (adtTwist η ((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) *
        ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)) =
      ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) := by
    rw [← mul_assoc, ← adtTwist_mul, coe_zeta_mul_coe_moebius,
      adtTwist_one, one_mul]
  have he := congrArg (fun f : ArithmeticFunction ℝ => f n) h
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal] at he
  simp_rw [adtTwist_moebius_zeta] at he
  have hz : (((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) n) = 1 := by
    simp [natCoe_apply, zeta_apply_ne hn.ne']
  rw [hz] at he
  convert he using 1
  apply sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  simp [adtTwist, natCoe_apply, zeta_apply_ne hd0]

theorem arithmeticDampingPrefix_nonneg {η : ℝ} (hη : 0 ≤ η) (n : ℕ) :
    0 ≤ arithmeticDampingPrefix η n :=
  sum_nonneg fun k _ => pmPowerDampedDivisorCoeff_nonneg hη k

theorem arithmeticDampingPrefix_mono {η : ℝ} (hη : 0 ≤ η) :
    Monotone (arithmeticDampingPrefix η) := by
  intro m n hmn
  apply sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hmn)
  intro k _ _
  exact pmPowerDampedDivisorCoeff_nonneg hη k

/-- Normalization of the exact weighted divisor prefixes. -/
theorem arithmeticDampingPrefix_weighted_sum (η : ℝ) (n : ℕ) :
    (∑ k ∈ Icc 1 n, (k : ℝ) ^ (-η) * arithmeticDampingPrefix η (n / k)) = n := by
  have h := Sieve.sum_divisors_swap n
    (fun d k => (d : ℝ) ^ (-η) * pmPowerDampedDivisorCoeff η k)
  simp only [← mul_sum] at h
  change (∑ k ∈ Icc 1 n, ∑ d ∈ k.divisors,
    (d : ℝ) ^ (-η) * pmPowerDampedDivisorCoeff η (k / d)) =
      ∑ d ∈ Icc 1 n, (d : ℝ) ^ (-η) * arithmeticDampingPrefix η (n / d) at h
  rw [← h]
  have hs : (∑ k ∈ Icc 1 n, ∑ d ∈ k.divisors,
      (d : ℝ) ^ (-η) * pmPowerDampedDivisorCoeff η (k / d)) =
      ∑ _k ∈ Icc 1 n, (1 : ℝ) := by
    exact sum_congr rfl fun k hk => arithmeticDamping_divisor_mass η (mem_Icc.mp hk).1
  rw [hs]
  simp

/-- The finite Cesàro transition. State zero has zero weight, and a positive
row is supported on the positive states at most its starting state. -/
def arithmeticDampingTransition (η : ℝ) (n k : ℕ) : ℝ :=
  (k : ℝ) / n *
    ((k : ℝ) ^ (-η) * arithmeticDampingPrefix η (n / k) -
      ((k + 1 : ℕ) : ℝ) ^ (-η) * arithmeticDampingPrefix η (n / (k + 1)))

@[simp] theorem arithmeticDampingTransition_zero_right (η : ℝ) (n : ℕ) :
    arithmeticDampingTransition η n 0 = 0 := by
  simp [arithmeticDampingTransition]

@[simp] theorem arithmeticDampingTransition_zero_left (η : ℝ) (k : ℕ) :
    arithmeticDampingTransition η 0 k = 0 := by
  simp [arithmeticDampingTransition]

theorem arithmeticDampingTransition_eq_zero_of_lt (η : ℝ) {n k : ℕ} (hnk : n < k) :
    arithmeticDampingTransition η n k = 0 := by
  simp [arithmeticDampingTransition, Nat.div_eq_of_lt hnk,
    Nat.div_eq_of_lt (show n < k + 1 by omega), arithmeticDampingPrefix]

theorem arithmeticDampingTransition_nonneg {η : ℝ} (hη : 0 ≤ η) (n k : ℕ) :
    0 ≤ arithmeticDampingTransition η n k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  apply mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  apply sub_nonneg.mpr
  apply mul_le_mul
  · apply Real.rpow_le_rpow_of_nonpos
    · exact_mod_cast Nat.pos_of_ne_zero hk
    · exact_mod_cast Nat.le_succ k
    · linarith
  · apply arithmeticDampingPrefix_mono hη
    exact Nat.div_le_div_left (Nat.le_succ k) (Nat.pos_of_ne_zero hk)
  · exact arithmeticDampingPrefix_nonneg hη _
  · exact Real.rpow_nonneg (Nat.cast_nonneg _) _

private theorem adt_weighted_telescope (a : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Icc 1 n, (k : ℝ) * (a k - a (k + 1))) =
      (∑ k ∈ Icc 1 n, a k) - (n : ℝ) * a (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

/-- Every positive row has total probability one. -/
theorem arithmeticDampingTransition_sum (η : ℝ) {n : ℕ} (hn : 0 < n) :
    (∑ k ∈ Icc 1 n, arithmeticDampingTransition η n k) = 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold arithmeticDampingTransition
  simp_rw [div_mul_eq_mul_div]
  rw [← sum_div, adt_weighted_telescope, arithmeticDampingPrefix_weighted_sum]
  simp [Nat.div_eq_of_lt (Nat.lt_succ_self n), arithmeticDampingPrefix, hn0]

end GaloisForLFunctions.BezoutValuationIncidence
