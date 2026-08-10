import GaloisForLFunctions.RHTower.Sieve.PrimeWindowSharpDelta
import GaloisForLFunctions.RHTower.Sieve.GhsOuterBlock

/-!
# The sharp affine mean square on the Perron line

The scale-`δ` prime count, transported to the Perron variable at the scale `δ = 1/T` the height
forces:

```text
∫_{|y| ≤ T} ‖L(a, σ+iy)‖² dy
  ≤ 2π·[ (5·700/4)·∑_q (q/log(q/T))·‖a_q q^{−σ}‖²  +  (5T/4)·∑_q ‖a_q q^{−σ}‖² ] ,
```

for a prime support all of whose members satisfy `q ≥ e⁴T`.  The first term is height-independent
and carries the *sharp* near-diagonal mass — one logarithm below the Montgomery–Vaughan weight; the
second is the plain mass and is the only place the height enters.

For the outer weight `a_p = f(p)·log p/log(N/p)` this is the `I₁` of the argument.  Once
`T ≤ √p` throughout the block — which the argument's `T = (log x)²`, `p > log⁴x` gives with room —
the near-diagonal mass is the block sum `∑_p log p/(p log²(N/p))` of `sum_block_outer_le`, up to a
factor two.
-/

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set Finset

/-- **The sharp affine mean square on the Perron line.** -/
theorem integral_Icc_normSq_LSeries_le_prime_sharp_delta {a : ℕ → ℂ} {s : Finset ℕ}
    (hs : ∀ m ∈ s, m.Prime) (hs0 : 0 ∉ s) (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ s) (σ : ℝ)
    {T : ℝ} (hT : 1 ≤ T) (hbig : ∀ q ∈ s, 4 ≤ Real.log ((q : ℝ) * (1 / T))) :
    (∫ y in Set.Icc (-T) T, ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2)
      ≤ 2 * Real.pi
          * ((5 * 700 / 4)
                * ∑ q ∈ s, ((q : ℝ) / Real.log ((q : ℝ) * (1 / T)))
                    * ‖a q * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2
              + (5 * T / 4) * ∑ q ∈ s, ‖a q * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hδ0 : (0 : ℝ) < 1 / T := by positivity
  have hδ1 : (1 : ℝ) / T ≤ 1 := by
    rw [div_le_one hT0]; linarith
  have hWδ : 2 * Real.pi * (1 / T) * (T / (2 * Real.pi)) ≤ 1 := by
    rw [show 2 * Real.pi * (1 / T) * (T / (2 * Real.pi)) = 1 by field_simp]
  rw [integral_Icc_normSq_LSeries_eq hs0 hsupp σ hT0.le]
  refine mul_le_mul_of_nonneg_left ?_ hπ.le
  refine le_trans (integral_Icc_normSq_logPoly_le_prime_sharp_delta
    (fun n => a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)) s hs hδ0 hδ1 hbig hWδ) ?_
  have hrate : (5 : ℝ) / (4 * (1 / T)) = 5 * T / 4 := by field_simp
  rw [hrate]

end RHTower.Sieve

end

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set Finset

/-- Past the square of the height the scale-`1/T` logarithm is at least half the plain one. -/
theorem half_log_le_log_div {T : ℝ} (hT : 1 ≤ T) {q : ℕ} (hq2 : (2 : ℝ) ≤ (q : ℝ))
    (hsq : T * T ≤ (q : ℝ)) : Real.log q / 2 ≤ Real.log ((q : ℝ) * (1 / T)) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hd0 : (0 : ℝ) < (q : ℝ) * (1 / T) := by positivity
  have hsqge : (q : ℝ) ≤ ((q : ℝ) * (1 / T)) ^ 2 := by
    have hT2 : (0 : ℝ) < T ^ 2 := by positivity
    have hkey : (q : ℝ) * T ^ 2 ≤ (q : ℝ) ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hsq hq0.le
      nlinarith [h]
    have heq : ((q : ℝ) * (1 / T)) ^ 2 = (q : ℝ) ^ 2 / T ^ 2 := by
      field_simp
    rw [heq, le_div_iff₀ hT2]
    linarith [hkey]
  have hlog := Real.log_le_log hq0 hsqge
  rw [Real.log_pow] at hlog
  push_cast at hlog
  linarith

/-- **The outer weight's sharp near-diagonal mass at the scale the height forces.** -/
theorem sum_sharp_mass_ghsOuter_le {f : ℕ → ℂ} (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) {σ : ℝ} (hσ : 1 ≤ σ)
    {T : ℝ} (hT : 1 ≤ T) {N : ℕ} {s : Finset ℕ} (hs : ∀ q ∈ s, q.Prime)
    (hsq : ∀ q ∈ s, T * T ≤ (q : ℝ)) :
    ∑ q ∈ s, ((q : ℝ) / Real.log ((q : ℝ) * (1 / T)))
        * ‖ghsOuter f N q * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2
      ≤ 2 * ∑ q ∈ s, Real.log q / ((q : ℝ) * (Real.log ((N / q : ℕ) : ℝ)) ^ 2) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q hq => ?_
  have hqp : q.Prime := hs q hq
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqp.two_le
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hlog : (0 : ℝ) < Real.log q := Real.log_pos (by linarith)
  have hhalf := half_log_le_log_div hT hq2 (hsq q hq)
  have hd0 : (0 : ℝ) < Real.log ((q : ℝ) * (1 / T)) := by linarith
  have hcoef : (q : ℝ) / Real.log ((q : ℝ) * (1 / T)) ≤ 2 * ((q : ℝ) / Real.log q) := by
    rw [div_le_iff₀ hd0]
    have hmul : 2 * ((q : ℝ) / Real.log q) * (Real.log q / 2) ≤
        2 * ((q : ℝ) / Real.log q) * Real.log ((q : ℝ) * (1 / T)) :=
      mul_le_mul_of_nonneg_left hhalf (by positivity)
    have heq : 2 * ((q : ℝ) / Real.log q) * (Real.log q / 2) = (q : ℝ) := by
      field_simp
    linarith [hmul, heq.le, heq.ge]
  have hnn : (0 : ℝ) ≤ ‖ghsOuter f N q * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 := by positivity
  calc ((q : ℝ) / Real.log ((q : ℝ) * (1 / T)))
        * ‖ghsOuter f N q * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2
      ≤ (2 * ((q : ℝ) / Real.log q))
        * ‖ghsOuter f N q * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef hnn
    _ = 2 * (((q : ℝ) / Real.log q)
        * ‖ghsOuter f N q * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2) := by ring
    _ ≤ 2 * (Real.log q / ((q : ℝ) * (Real.log ((N / q : ℕ) : ℝ)) ^ 2)) :=
        mul_le_mul_of_nonneg_left (ghsOuter_weighted_term_le hbdd hσ hqp) (by norm_num)

/-- **The `I₁` mass of one outer block, in final form.** -/
theorem sum_sharp_mass_ghsOuter_block_le {f : ℕ → ℂ} (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) {σ : ℝ}
    (hσ : 1 ≤ σ) {T : ℝ} (hT : 1 ≤ T) {A B N : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) (hBN : 2 ≤ N / B)
    (hsq : ∀ q ∈ Nat.primesLE B \ Nat.primesLE A, T * T ≤ (q : ℝ)) :
    ∑ q ∈ Nat.primesLE B \ Nat.primesLE A, ((q : ℝ) / Real.log ((q : ℝ) * (1 / T)))
        * ‖ghsOuter f N q * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2
      ≤ 2 * ((Real.log B - Real.log A + mertensBlockGapConst)
          / (Real.log ((N / B : ℕ) : ℝ)) ^ 2) := by
  have hprime : ∀ q ∈ Nat.primesLE B \ Nat.primesLE A, q.Prime := by
    intro q hq
    rw [Finset.mem_sdiff] at hq
    exact Nat.prime_of_mem_primesLE hq.1
  refine le_trans (sum_sharp_mass_ghsOuter_le hbdd hσ hT hprime hsq) ?_
  exact mul_le_mul_of_nonneg_left (sum_block_outer_le hA hAB hBN) (by norm_num)

end RHTower.Sieve

end
