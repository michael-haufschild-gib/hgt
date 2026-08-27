import GaloisForLFunctions.RHTower.Sieve.SiftTailDivisorWeightedMean
import GaloisForLFunctions.RHTower.Sieve.DivisorMomentEulerBound
import GaloisForLFunctions.RHTower.Sieve.SquarefreeDivisorCount

/-!
# Euler-product bound for the divisor-weighted smooth tail

At Rankin exponent `1/log z`, every prime below `z` contributes at most `exp(1)`.  Since a
squarefree divisor `e` has `2^ω(e)` divisors, the fixed divisor weight is absorbed into the one-
variable Euler product with local parameter `2^K exp(1)`.  This closes the arithmetic part of the
literal `c₁,n` estimate.
-/

namespace RHTower.Sieve

open Finset Nat

noncomputable section

/-- A divisor of the sifting modulus has Rankin tilt at most `exp(1)` per prime factor. -/
theorem divisor_rpow_invLog_le_exp_card_primeFactors
    {z e : ℕ} (hz : 2 ≤ z) (he : e ∈ (siftModulus z).divisors) :
    (e : ℝ) ^ (1 / Real.log z) ≤
      (Real.exp 1) ^ e.primeFactors.card := by
  have heDiv : e ∣ siftModulus z := (Nat.mem_divisors.mp he).1
  have heSq : Squarefree e := (siftModulus_squarefree z).squarefree_of_dvd heDiv
  rw [natCast_rpow_eq_prod_primeFactors heSq]
  have hsub : e.primeFactors ⊆ z.primesBelow := by
    rw [← primeFactors_siftModulus]
    exact Nat.primeFactors_mono heDiv (siftModulus_pos z).ne'
  calc
    ∏ p ∈ e.primeFactors, (p : ℝ) ^ (1 / Real.log z) ≤
        ∏ _p ∈ e.primeFactors, Real.exp 1 := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        have hpMem := hsub hp
        exact rpow_mul_inv_log_le_exp
          (Nat.mem_primesBelow.mp hpMem).2 hz (Nat.mem_primesBelow.mp hpMem).1 (by norm_num)
    _ = (Real.exp 1) ^ e.primeFactors.card := by simp

/-- Divisor weight and Rankin tilt combine into one fixed local Euler factor. -/
theorem card_pow_mul_rpow_invLog_le
    (K : ℕ) {z e : ℕ} (hz : 2 ≤ z) (he : e ∈ (siftModulus z).divisors) :
    ((e.divisors.card : ℝ) ^ K) * (e : ℝ) ^ (1 / Real.log z) ≤
      (((2 : ℝ) ^ K) * Real.exp 1) ^ e.primeFactors.card := by
  have heDiv : e ∣ siftModulus z := (Nat.mem_divisors.mp he).1
  have hePos : 0 < e := Nat.pos_of_mem_divisors he
  have heSq : Squarefree e := (siftModulus_squarefree z).squarefree_of_dvd heDiv
  have hcard := card_divisors_of_squarefree heSq hePos.ne'
  have hrpow := divisor_rpow_invLog_le_exp_card_primeFactors hz he
  have hcast : (e.divisors.card : ℝ) = (2 : ℝ) ^ e.primeFactors.card := by
    exact_mod_cast hcard
  rw [hcast]
  calc
    ((2 : ℝ) ^ e.primeFactors.card) ^ K * (e : ℝ) ^ (1 / Real.log z) ≤
        ((2 : ℝ) ^ e.primeFactors.card) ^ K *
          (Real.exp 1) ^ e.primeFactors.card := by
      exact mul_le_mul_of_nonneg_left hrpow (by positivity)
    _ = (((2 : ℝ) ^ K) * Real.exp 1) ^ e.primeFactors.card := by
      rw [mul_pow]
      congr 1
      simp only [← pow_mul]
      rw [Nat.mul_comm]

/-- Explicit Rankin--Euler bound for the weighted discarded-divisor harmonic mass. -/
theorem sum_largeSiftDivisors_card_pow_div_le
    (K : ℕ) {z D : ℕ} (hz : 2 ≤ z) (hD : 0 < D) :
    ∑ e ∈ largeSiftDivisors z D,
        ((e.divisors.card : ℝ) ^ K) / (e : ℝ) ≤
      (D : ℝ) ^ (-(1 / Real.log z)) *
        Real.exp ((((2 : ℝ) ^ K) * Real.exp 1) *
          (logLog z + mertensSecondUpperConst)) := by
  let lam : ℝ := ((2 : ℝ) ^ K) * Real.exp 1
  have hlogz : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hz))
  have hα : 0 < 1 / Real.log (z : ℝ) := by positivity
  have hDpow : 0 ≤ (D : ℝ) ^ (-(1 / Real.log z)) :=
    Real.rpow_nonneg (Nat.cast_nonneg D) _
  have hterm : ∀ e ∈ largeSiftDivisors z D,
      ((e.divisors.card : ℝ) ^ K) / (e : ℝ) ≤
        (D : ℝ) ^ (-(1 / Real.log z)) *
          (lam ^ e.primeFactors.card / (e : ℝ)) := by
    intro e heTail
    have heAll : e ∈ (siftModulus z).divisors := (Finset.mem_filter.mp heTail).1
    have hDe : D < e := (Finset.mem_filter.mp heTail).2
    have hePos : 0 < e := Nat.pos_of_mem_divisors heAll
    have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
    have heR : 0 < (e : ℝ) := by exact_mod_cast hePos
    have hpow : (D : ℝ) ^ (1 / Real.log z) ≤
        (e : ℝ) ^ (1 / Real.log z) := by
      exact Real.rpow_le_rpow hDR.le (by exact_mod_cast hDe.le) hα.le
    have hRankin : (1 : ℝ) ≤
        (D : ℝ) ^ (-(1 / Real.log z)) * (e : ℝ) ^ (1 / Real.log z) := by
      rw [Real.rpow_neg hDR.le, ← div_eq_inv_mul, le_div_iff₀
        (Real.rpow_pos_of_pos hDR _)]
      simpa using hpow
    have htilt : ((e.divisors.card : ℝ) ^ K) *
        (e : ℝ) ^ (1 / Real.log z) ≤ lam ^ e.primeFactors.card := by
      simpa only [lam] using card_pow_mul_rpow_invLog_le K hz heAll
    calc
      ((e.divisors.card : ℝ) ^ K) / (e : ℝ) ≤
          ((e.divisors.card : ℝ) ^ K) *
            ((D : ℝ) ^ (-(1 / Real.log z)) * (e : ℝ) ^ (1 / Real.log z)) /
              (e : ℝ) := by
        apply div_le_div_of_nonneg_right _ heR.le
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hRankin
          (show 0 ≤ ((e.divisors.card : ℝ) ^ K) from
            pow_nonneg (Nat.cast_nonneg _) _)
      _ = (D : ℝ) ^ (-(1 / Real.log z)) *
          ((((e.divisors.card : ℝ) ^ K) *
            (e : ℝ) ^ (1 / Real.log z)) / (e : ℝ)) := by ring
      _ ≤ (D : ℝ) ^ (-(1 / Real.log z)) *
          (lam ^ e.primeFactors.card / (e : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hDpow
        exact div_le_div_of_nonneg_right htilt heR.le
  have hprod :
      ∏ p ∈ z.primesBelow, (1 + lam / (p : ℝ)) ≤
        Real.exp (lam * mertensS z) := by
    calc
      ∏ p ∈ z.primesBelow, (1 + lam / (p : ℝ)) ≤
          Real.exp (lam * ∑ p ∈ z.primesBelow, 1 / (p : ℝ)) :=
        prod_one_add_le_exp_sum z.primesBelow (lam := lam) (by positivity)
      _ ≤ Real.exp (lam * mertensS z) := by
        rw [Real.exp_le_exp]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        unfold mertensS
        exact Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => by
            rw [Nat.mem_primesLE]
            exact ⟨(Nat.mem_primesBelow.mp hp).1.le,
              (Nat.mem_primesBelow.mp hp).2⟩)
          (fun p _ _ => by positivity)
  have hMertens : Real.exp (lam * mertensS z) ≤
      Real.exp (lam * (logLog z + mertensSecondUpperConst)) := by
    rw [Real.exp_le_exp]
    exact mul_le_mul_of_nonneg_left (mertensS_le hz) (by positivity)
  calc
    ∑ e ∈ largeSiftDivisors z D,
        ((e.divisors.card : ℝ) ^ K) / (e : ℝ) ≤
      ∑ e ∈ largeSiftDivisors z D,
        (D : ℝ) ^ (-(1 / Real.log z)) *
          (lam ^ e.primeFactors.card / (e : ℝ)) := Finset.sum_le_sum hterm
    _ = (D : ℝ) ^ (-(1 / Real.log z)) *
        ∑ e ∈ largeSiftDivisors z D,
          lam ^ e.primeFactors.card / (e : ℝ) := by rw [Finset.mul_sum]
    _ ≤ (D : ℝ) ^ (-(1 / Real.log z)) *
        ∑ e ∈ (siftModulus z).divisors,
          lam ^ e.primeFactors.card / (e : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hDpow
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro e he _
      positivity
    _ = (D : ℝ) ^ (-(1 / Real.log z)) *
        ∏ p ∈ z.primesBelow, (1 + lam / (p : ℝ)) := by
      rw [sum_divisors_pow_card_primeFactors_div_eq_prod (siftModulus_squarefree z),
        primeFactors_siftModulus]
    _ ≤ (D : ℝ) ^ (-(1 / Real.log z)) * Real.exp (lam * mertensS z) := by
      exact mul_le_mul_of_nonneg_left hprod hDpow
    _ ≤ (D : ℝ) ^ (-(1 / Real.log z)) *
        Real.exp (lam * (logLog z + mertensSecondUpperConst)) := by
      exact mul_le_mul_of_nonneg_left hMertens hDpow
    _ = (D : ℝ) ^ (-(1 / Real.log z)) *
        Real.exp ((((2 : ℝ) ^ K) * Real.exp 1) *
          (logLog z + mertensSecondUpperConst)) := by rfl

end

end RHTower.Sieve
