import GaloisForLFunctions.RHTower.Sieve.SelbergInversion

/-!
# The error term of a `Λ²` sieve

Two structural facts control `errSum (Λ² w)`.

First, the `Λ²` coefficients inherit a bound from the weights: `|Λ²_d| ≤ (∑_{e ∣ d} |w e|)²`, by
the triangle inequality on the defining double sum.

Second, they inherit the support: if `w` vanishes above `Y`, then `Λ²_d = 0` above `Y²`, because a
nonzero term needs `d = lcm d₁ d₂` with `w d₁ w d₂ ≠ 0`, whence `d ≤ d₁ d₂ ≤ Y²`.  This is what
makes the level of a Selberg sieve `D = Y²`, and it is the reason the error sum runs only over
`d ≤ D` rather than over all divisors of the sifting modulus.
-/

namespace RHTower.Sieve

open Finset Nat BoundingSieve

/-- **Triangle bound for the `Λ²` coefficients.** -/
theorem abs_lambdaSquared_le (w : ℕ → ℝ) (d : ℕ) :
    |lambdaSquared w d| ≤ (∑ e ∈ d.divisors, |w e|) ^ 2 := by
  classical
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hinner : ∀ d1 ∈ d.divisors,
      |∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then w d1 * w d2 else 0|
        ≤ |w d1| * ∑ e ∈ d.divisors, |w e| := by
    intro d1 _
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro d2 _
    by_cases h : d = Nat.lcm d1 d2
    · rw [if_pos h, abs_mul]
    · rw [if_neg h, abs_zero]
      positivity
  refine le_trans (Finset.sum_le_sum hinner) ?_
  rw [← Finset.sum_mul, sq]

/-- **Support inheritance.**  A `Λ²` sieve built from weights supported below `Y` has level
`Y²`. -/
theorem lambdaSquared_eq_zero_of_lt {w : ℕ → ℝ} {Y : ℕ} (hw : ∀ n, Y < n → w n = 0)
    {d : ℕ} (hd : Y * Y < d) : lambdaSquared w d = 0 := by
  classical
  have hd0 : d ≠ 0 := by omega
  refine Finset.sum_eq_zero ?_
  intro d1 hd1
  refine Finset.sum_eq_zero ?_
  intro d2 hd2
  by_cases h : d = Nat.lcm d1 d2
  · rw [if_pos h]
    by_cases h1 : Y < d1
    · rw [hw d1 h1, zero_mul]
    · by_cases h2 : Y < d2
      · rw [hw d2 h2, mul_zero]
      · exfalso
        have hd1pos : 0 < d1 := Nat.pos_of_mem_divisors hd1
        have hd2pos : 0 < d2 := Nat.pos_of_mem_divisors hd2
        have hlcm : Nat.lcm d1 d2 ≤ d1 * d2 :=
          Nat.le_of_dvd (Nat.mul_pos hd1pos hd2pos)
            (Nat.lcm_dvd (Dvd.intro d2 rfl) (Dvd.intro_left d1 rfl))
        have hprod : d1 * d2 ≤ Y * Y :=
          Nat.mul_le_mul (by omega) (by omega)
        omega
  · rw [if_neg h]

/-- **Error bound.**  A uniform bound on the weights and on the remainders bounds the whole error
sum by the number of divisors involved. -/
theorem errSum_lambdaSquared_le (s : BoundingSieve) (w : ℕ → ℝ) {B : ℝ}
    (hB : ∀ d ∈ s.prodPrimes.divisors, |s.rem d| ≤ B) :
    s.errSum (lambdaSquared w)
      ≤ B * ∑ d ∈ s.prodPrimes.divisors, (∑ e ∈ d.divisors, |w e|) ^ 2 := by
  classical
  rw [errSum, Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro d hd
  have h1 : |lambdaSquared w d| ≤ (∑ e ∈ d.divisors, |w e|) ^ 2 := abs_lambdaSquared_le w d
  have h2 : |s.rem d| ≤ B := hB d hd
  have hnn : (0 : ℝ) ≤ (∑ e ∈ d.divisors, |w e|) ^ 2 := sq_nonneg _
  have habs : (0 : ℝ) ≤ |s.rem d| := abs_nonneg _
  calc |lambdaSquared w d| * |s.rem d|
      ≤ (∑ e ∈ d.divisors, |w e|) ^ 2 * |s.rem d| :=
        mul_le_mul_of_nonneg_right h1 habs
    _ ≤ (∑ e ∈ d.divisors, |w e|) ^ 2 * B := mul_le_mul_of_nonneg_left h2 hnn
    _ = B * (∑ e ∈ d.divisors, |w e|) ^ 2 := by ring

/-- With unit weights the divisor bound is the square of the divisor count. -/
theorem abs_lambdaSquared_le_card_sq {w : ℕ → ℝ} (hw : ∀ n, |w n| ≤ 1) (d : ℕ) :
    |lambdaSquared w d| ≤ ((d.divisors.card : ℝ)) ^ 2 := by
  refine le_trans (abs_lambdaSquared_le w d) ?_
  have hle : ∑ e ∈ d.divisors, |w e| ≤ (d.divisors.card : ℝ) := by
    calc ∑ e ∈ d.divisors, |w e| ≤ ∑ _e ∈ d.divisors, (1 : ℝ) :=
          Finset.sum_le_sum fun e _ => hw e
      _ = (d.divisors.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hnn : (0 : ℝ) ≤ ∑ e ∈ d.divisors, |w e| :=
    Finset.sum_nonneg fun e _ => abs_nonneg _
  exact pow_le_pow_left₀ hnn hle 2

end RHTower.Sieve
