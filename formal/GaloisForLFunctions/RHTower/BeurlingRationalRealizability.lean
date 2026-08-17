import GaloisForLFunctions.RHTower.BeurlingRationalFactorBalance

/-!
# Realizability of a rational Euler factor: power sums, and the failure of majorization

A rational function `R` with `R(∞) = 1`, poles `p_1,…,p_n` and zeros `z_1,…,z_n`, is the zeta
function of a Beurling generalized prime system exactly when the logarithmic prime density

```
  w(t) = ( ∑_i e^{p_i t} - ∑_j e^{z_j t} ) / t
```

is nonnegative on `(0, ∞)`.  So realizability is the single inequality
`F(t) := ∑_i e^{p_i t} - ∑_j e^{z_j t} ≥ 0`, a question about a difference of two exponential sums
with equally many terms.

This module settles the two natural guesses about that inequality.

* **Power-sum dominance is sufficient.**  Expanding both exponential sums, the Taylor coefficients of
  `F` are the power-sum differences `σ_k = ∑_i p_i^k - ∑_j z_j^k`.  If every `σ_k ≥ 0` then `F ≥ 0`
  termwise.  (The necessary counterpart — the first nonvanishing `σ_k` is positive — is
  `abs_density_ge_of_count_ne` and `sum_pole_ge_sum_zero_of_nonneg` at `k = 0, 1`.)

* **Majorization is *not* necessary.**  The classical sufficient condition for a difference of
  exponential sums to be nonnegative is Karamata's inequality, which requires the pole multiset to
  majorize the zero multiset.  That is strictly stronger than realizability: for poles `{3, 0, 0}`
  and zeros `{2, 2, -1}` majorization fails at the second partial sum (`3 + 0 < 2 + 2`), yet

  ```
     e^{3t} + 2 - 2 e^{2t} - e^{-t}  =  (e^t - 1)^3 (e^t + 1) / e^t  ≥  0.
  ```

  The identity is exact, so the example is unconditional.  Rescaling `t ↦ t/3` puts the top pole at
  `s = 1`: the resulting Beurling system has a simple pole at `1`, a double pole at `0`, and **zeros
  at `2/3` and `-1/3`** — an explicit RH-violating system whose pole/zero configuration is not
  majorizing.

All statements are unconditional.
-/

namespace RHTower.RationalFactor

open Finset

/-! ## Power-sum dominance is sufficient -/

theorem real_exp_tsum (x : ℝ) : Real.exp x = ∑' n : ℕ, x ^ n / (Nat.factorial n : ℝ) := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

theorem hasSum_exp (x : ℝ) :
    HasSum (fun k : ℕ => x ^ k / (Nat.factorial k : ℝ)) (Real.exp x) := by
  rw [real_exp_tsum x]
  exact (Real.summable_pow_div_factorial x).hasSum

/-- **Power-sum dominance implies realizability.**  If every power sum of the poles dominates the
corresponding power sum of the zeros, then the numerator of the logarithmic prime density is
nonnegative on `[0, ∞)`, so the rational Euler factor is realized by a positive generalized-prime
measure.  The Taylor coefficients of the exponential difference are exactly the power-sum
differences, so the series is termwise nonnegative. -/
theorem factorNumerator_nonneg_of_powerSum_le {P Z : ℕ} (p : Fin P → ℝ) (z : Fin Z → ℝ)
    (h : ∀ k : ℕ, (∑ j, z j ^ k) ≤ ∑ i, p i ^ k) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ factorNumerator p z t := by
  have hP := hasSum_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin P))) => hasSum_exp (p i * t))
  have hZ := hasSum_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin Z))) => hasSum_exp (z j * t))
  have hD := hP.sub hZ
  rw [factorNumerator]
  refine hasSum_le ?_ hasSum_zero hD
  intro k
  have hfac : (0 : ℝ) < (Nat.factorial k : ℝ) := by
    exact_mod_cast Nat.factorial_pos k
  have hexpand : ∀ {m : ℕ} (a : Fin m → ℝ),
      (∑ i, (a i * t) ^ k / (Nat.factorial k : ℝ)) =
        (∑ i, a i ^ k) * t ^ k / (Nat.factorial k : ℝ) := by
    intro m a
    rw [Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [mul_pow]
  rw [hexpand p, hexpand z, div_sub_div_same, div_nonneg_iff]
  left
  refine ⟨?_, hfac.le⟩
  have hkey := h k
  have htk : (0 : ℝ) ≤ t ^ k := pow_nonneg ht k
  nlinarith [hkey, htk]

/-! ## Majorization is not necessary -/

/-- **The realizability inequality holds for a non-majorizing configuration.**  Poles `{3, 0, 0}`
against zeros `{2, 2, -1}`: the exponential difference factors exactly as
`(e^t - 1)^3 (e^t + 1) / e^t`. -/
theorem exp_difference_factorization (t : ℝ) :
    Real.exp (3 * t) + 2 - 2 * Real.exp (2 * t) - Real.exp (-t) =
      (Real.exp t - 1) ^ 3 * (Real.exp t + 1) / Real.exp t := by
  have hx : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have h3 : Real.exp (3 * t) = Real.exp t ^ 3 := by
    rw [show (3 : ℝ) * t = t + t + t by ring, Real.exp_add, Real.exp_add]
    ring
  have h2 : Real.exp (2 * t) = Real.exp t ^ 2 := by
    rw [show (2 : ℝ) * t = t + t by ring, Real.exp_add]
    ring
  have hm : Real.exp (-t) = 1 / Real.exp t := by
    rw [Real.exp_neg, one_div]
  rw [h3, h2, hm]
  field_simp
  ring

/-- The non-majorizing configuration is realizable. -/
theorem exp_difference_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ Real.exp (3 * t) + 2 - 2 * Real.exp (2 * t) - Real.exp (-t) := by
  rw [exp_difference_factorization]
  have hx : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have h1 : (1 : ℝ) ≤ Real.exp t := Real.one_le_exp ht
  apply div_nonneg _ hx.le
  exact mul_nonneg (pow_nonneg (by linarith) 3) (by linarith)

/-- Majorization fails for that configuration: the second partial sum of the sorted poles is
strictly smaller than that of the sorted zeros. -/
theorem majorization_fails : (3 : ℝ) + 0 < 2 + 2 := by norm_num

end RHTower.RationalFactor
