import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheCoreDominanceCriterion

/-!
# The core grows like the inverse damping

The core of the signed work is the pronic average of the damped Chebyshev prefix
`ψ_ε(n) = Σ_{j ≤ n} Λ(j) j^{-ε}`, and the powers of two alone show how large that prefix is: each
`2^k` with `k ≤ K` contributes `log 2 · (2^{-ε})^k ≥ log 2 · (2^{-ε})^K`, so

`ψ_ε(n) ≥ K log 2 (2^{-ε})^K`  whenever `2^K ≤ n`
(`dampedPrimePrefix_ge_powersOfTwo`).

Choosing `K` with `1 ≤ εK ≤ 2` makes `(2^{-ε})^K ≥ 1/4` and `K ≥ 1/ε`, hence

`ψ_ε(n) ≥ (log 2)/(4 ε)`  for `n ≥ 2^K`
(`dampedPrimePrefix_ge_inv_damping`).

So the explicit positive core of the work is of order `1/ε`, but only once the horizon passes
`2^{1/ε}` — the same deep-horizon, small-damping corner where the escape lives.  That fixes the units
of the core-dominance criterion: `O(1)` before the corner and `1/ε` inside it.
-/

open Finset RHTower

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-- **The powers of two in the damped Chebyshev prefix.** -/
theorem dampedPrimePrefix_ge_powersOfTwo (ε : ℝ) (hε : 0 ≤ ε) {K n : ℕ} (hK : 2 ^ K ≤ n) :
    (K : ℝ) * (Real.log 2 * ((2 : ℝ) ^ (-ε)) ^ K) ≤ dampedPrimePrefix ε n := by
  classical
  set r : ℝ := (2 : ℝ) ^ (-ε) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  set S : Finset ℕ := (Icc 1 K).image (fun k => 2 ^ k) with hS
  have hSsub : S ⊆ Icc 1 n := by
    intro j hj
    rw [hS, Finset.mem_image] at hj
    obtain ⟨k, hk, rfl⟩ := hj
    rw [mem_Icc] at hk ⊢
    exact ⟨Nat.one_le_two_pow, le_trans (Nat.pow_le_pow_right (by norm_num) hk.2) hK⟩
  have hScard : S.card = K := by
    rw [hS, Finset.card_image_of_injective _ (Nat.pow_right_injective (by norm_num)),
      Nat.card_Icc]
    omega
  have hterm : ∀ j ∈ S, Real.log 2 * r ^ K ≤ dampedPrimeWeight ε j := by
    intro j hj
    rw [hS, Finset.mem_image] at hj
    obtain ⟨k, hk, rfl⟩ := hj
    rw [mem_Icc] at hk
    have hΛ : ArithmeticFunction.vonMangoldt (2 ^ k) = Real.log 2 := by
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega : k ≠ 0),
        ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      norm_num
    have hpow : (((2 : ℕ) ^ k : ℕ) : ℝ) ^ (-ε) = r ^ k := by
      rw [hr]
      push_cast
      rw [← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_natCast ((2 : ℝ) ^ (-ε)) k, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    rw [dampedPrimeWeight, hΛ, hpow]
    have hmono : r ^ K ≤ r ^ k := pow_le_pow_of_le_one hr0.le hr1 hk.2
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact mul_le_mul_of_nonneg_left hmono hlog.le
  have hsub : (∑ j ∈ S, dampedPrimeWeight ε j) ≤ dampedPrimePrefix ε n := by
    rw [dampedPrimePrefix]
    refine Finset.sum_le_sum_of_subset_of_nonneg hSsub fun j _ _ => ?_
    rw [dampedPrimeWeight]
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg j) _)
  have hcard := Finset.card_nsmul_le_sum S (dampedPrimeWeight ε) (Real.log 2 * r ^ K) hterm
  rw [nsmul_eq_mul, hScard] at hcard
  linarith

/-- **The core's inverse-damping lower bound.**  Beyond `2^K` with `1 ≤ εK ≤ 2`, the damped
Chebyshev prefix is at least `(log 2)/(4ε)`. -/
theorem dampedPrimePrefix_ge_inv_damping {ε : ℝ} (hε : 0 < ε) {K n : ℕ}
    (hKlow : 1 ≤ ε * (K : ℝ)) (hKhigh : ε * (K : ℝ) ≤ 2) (hK : 2 ^ K ≤ n) :
    Real.log 2 / (4 * ε) ≤ dampedPrimePrefix ε n := by
  set r : ℝ := (2 : ℝ) ^ (-ε) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hrK : (1 : ℝ) / 4 ≤ r ^ K := by
    have hrKpow : r ^ K = (2 : ℝ) ^ (-ε * (K : ℝ)) := by
      rw [hr, ← Real.rpow_natCast ((2 : ℝ) ^ (-ε)) K,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hge : (2 : ℝ) ^ (-2 : ℝ) ≤ (2 : ℝ) ^ (-ε * (K : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
    have hval : (2 : ℝ) ^ (-2 : ℝ) = 1 / 4 := by
      rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
      norm_num
    rw [hrKpow, ← hval]
    exact hge
  have hKge : 1 / ε ≤ (K : ℝ) := by
    rw [div_le_iff₀ hε]
    linarith
  have hmain := dampedPrimePrefix_ge_powersOfTwo ε hε.le hK
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine le_trans ?_ hmain
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * ε)]
  have hstep : (1 / ε) * (Real.log 2 * (1 / 4)) ≤ (K : ℝ) * (Real.log 2 * r ^ K) := by
    have h1 : (1 / ε) * (Real.log 2 * (1 / 4)) ≤ (K : ℝ) * (Real.log 2 * (1 / 4)) :=
      mul_le_mul_of_nonneg_right hKge (by positivity)
    have h2 : (K : ℝ) * (Real.log 2 * (1 / 4)) ≤ (K : ℝ) * (Real.log 2 * r ^ K) := by
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg K)
      exact mul_le_mul_of_nonneg_left hrK hlog.le
    linarith
  have hεinv : (1 / ε) * (Real.log 2 * (1 / 4)) = Real.log 2 / (4 * ε) := by
    field_simp
  rw [hεinv] at hstep
  calc Real.log 2 = Real.log 2 / (4 * ε) * (4 * ε) := by field_simp
    _ ≤ ((K : ℝ) * (Real.log 2 * r ^ K)) * (4 * ε) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        linarith [hstep]

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
