import GaloisForLFunctions.RHTower.Sieve.GhsStepFour
import GaloisForLFunctions.RHTower.Sieve.SelbergTail
/-!
# The sieve mean square against two zeta-type prime sums

The Selberg majorant of the almost-diagonal count is `2(n·2 sinh δ + 1)/log Y + E + z`, linear in `n`.
Paired with logarithmically bounded coefficients it splits into exactly two sums:

`sieveMeanSquare a s σ z Y
    ≤ (4 sinh δ/log Y)·A²·∑_{n ∈ s} n^{1−2σ}(log n)² + (2/log Y + E + z)·A²·∑_{n ∈ s} n^{−2σ}(log n)²`,

for `‖a_n‖ ≤ A log n`.  Both sums converge for `σ > 1`, the first being the one that grows as `σ ↓ 1`: at
`σ = 1 + 1/log N` it is of size `(log N)²`, and it is this pairing of a linear sieve count against a
quadratically damped coefficient that carries the saving of the argument.

Instantiated at the two prime weights of the Granville–Harper–Soundararajan convolution the constants are
`A = 1` for the inner weight and `A = 1/log 2` for the outer one, and the coefficient size is the only thing
that enters — the sieve level and the frequency scale remain free.
-/

noncomputable section
namespace RHTower.Sieve
open Finset

/-- **The sieve mean square against two zeta-type prime sums.**  For logarithmically bounded coefficients
the Selberg majorant splits into its linear part, which pairs with `∑ n^{1−2σ}(log n)²`, and its constant
part, which pairs with `∑ n^{−2σ}(log n)²`.  Both sums converge for `σ > 1`, and this is the only place
where the size of the coefficients enters. -/
theorem sieveMeanSquare_le_of_norm_le_log {a : ℕ → ℂ} {A : ℝ}
    (haB : ∀ n : ℕ, ‖a n‖ ≤ A * Real.log n) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) (σ : ℝ)
    (z Y : ℕ) (hz : 2 ≤ z) (hlogY : 0 < Real.log Y) :
    sieveMeanSquare a s σ z Y
      ≤ (2 * (Real.exp (1 / (2 * Real.pi)) - Real.exp (-(1 / (2 * Real.pi)))) / Real.log Y)
            * (A ^ 2 * ∑ n ∈ s, (n : ℝ) ^ (1 - 2 * σ) * (Real.log n) ^ 2)
        + (2 / Real.log Y + selbergFibreError z Y + (z : ℝ))
            * (A ^ 2 * ∑ n ∈ s, (n : ℝ) ^ (-(2 * σ)) * (Real.log n) ^ 2) := by
  classical
  set S : ℝ := Real.exp (1 / (2 * Real.pi)) - Real.exp (-(1 / (2 * Real.pi))) with hS
  have hS0 : 0 ≤ S := by
    rw [hS]
    have hpi : (0 : ℝ) < 1 / (2 * Real.pi) := by positivity
    have h := Real.exp_le_exp.2 (show -(1 / (2 * Real.pi)) ≤ 1 / (2 * Real.pi) by linarith)
    linarith
  have herr : 0 ≤ selbergFibreError z Y := selbergFibreError_nonneg hz Y
  have hzR : (0 : ℝ) ≤ (z : ℝ) := Nat.cast_nonneg z
  have hterm : ∀ n ∈ s,
      (2 * ((n : ℝ) * S + 1) / Real.log Y + selbergFibreError z Y + (z : ℝ))
          * ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2
        ≤ (2 * S / Real.log Y) * (A ^ 2 * ((n : ℝ) ^ (1 - 2 * σ) * (Real.log n) ^ 2))
          + (2 / Real.log Y + selbergFibreError z Y + (z : ℝ))
              * (A ^ 2 * ((n : ℝ) ^ (-(2 * σ)) * (Real.log n) ^ 2)) := by
    intro n hn
    have hn1 : 1 ≤ n := hs n hn
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hlogn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hnR
    -- the damped coefficient
    have hrpow : (0 : ℝ) ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg hnpos.le _
    have hsq : ((n : ℝ) ^ (-σ)) ^ 2 = (n : ℝ) ^ (-(2 * σ)) := by
      rw [← Real.rpow_natCast ((n : ℝ) ^ (-σ)) 2, ← Real.rpow_mul hnpos.le]
      norm_num
      ring_nf
    have hnorm : ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2
        = ‖a n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hrpow, mul_pow, hsq]
    have hcoeff : ‖a n‖ ^ 2 ≤ A ^ 2 * (Real.log n) ^ 2 := by
      have h := haB n
      have h0 : (0 : ℝ) ≤ ‖a n‖ := norm_nonneg _
      calc ‖a n‖ ^ 2 ≤ (A * Real.log n) ^ 2 := pow_le_pow_left₀ h0 h 2
        _ = A ^ 2 * (Real.log n) ^ 2 := by ring
    have hK0 : (0 : ℝ) ≤ 2 * ((n : ℝ) * S + 1) / Real.log Y
        + selbergFibreError z Y + (z : ℝ) := by
      have hnum : (0 : ℝ) ≤ 2 * ((n : ℝ) * S + 1) := by positivity
      have : (0 : ℝ) ≤ 2 * ((n : ℝ) * S + 1) / Real.log Y := div_nonneg hnum hlogY.le
      linarith
    have hlinear : (n : ℝ) ^ (1 - 2 * σ) = (n : ℝ) * (n : ℝ) ^ (-(2 * σ)) := by
      rw [show (1 : ℝ) - 2 * σ = 1 + -(2 * σ) by ring, Real.rpow_add hnpos, Real.rpow_one]
    rw [hnorm]
    have hstep : (2 * ((n : ℝ) * S + 1) / Real.log Y + selbergFibreError z Y + (z : ℝ))
        * (‖a n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ)))
        ≤ (2 * ((n : ℝ) * S + 1) / Real.log Y + selbergFibreError z Y + (z : ℝ))
            * ((A ^ 2 * (Real.log n) ^ 2) * (n : ℝ) ^ (-(2 * σ))) := by
      refine mul_le_mul_of_nonneg_left ?_ hK0
      exact mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hnpos.le _)
    refine hstep.trans (le_of_eq ?_)
    rw [hlinear]
    field_simp
    ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]

/-- The inner prime weight: `A = 1`. -/
theorem sieveMeanSquare_ghsInner_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (M : ℕ) (σ : ℝ)
    (z Y : ℕ) (hz : 2 ≤ z) (hlogY : 0 < Real.log Y) :
    sieveMeanSquare (ghsInner f M) (Finset.Icc 1 M) σ z Y
      ≤ (2 * (Real.exp (1 / (2 * Real.pi)) - Real.exp (-(1 / (2 * Real.pi)))) / Real.log Y)
            * (1 ^ 2 * ∑ n ∈ Finset.Icc 1 M, (n : ℝ) ^ (1 - 2 * σ) * (Real.log n) ^ 2)
        + (2 / Real.log Y + selbergFibreError z Y + (z : ℝ))
            * (1 ^ 2 * ∑ n ∈ Finset.Icc 1 M, (n : ℝ) ^ (-(2 * σ)) * (Real.log n) ^ 2) :=
  sieveMeanSquare_le_of_norm_le_log (by simpa using norm_ghsInner_le hf M)
    (Finset.Icc 1 M) (fun n hn => (Finset.mem_Icc.1 hn).1) σ z Y hz hlogY

/-- The outer prime weight: `A = 1/log 2`. -/
theorem sieveMeanSquare_ghsOuter_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (N : ℕ) (σ : ℝ)
    (z Y : ℕ) (hz : 2 ≤ z) (hlogY : 0 < Real.log Y) :
    sieveMeanSquare (ghsOuter f N) (Finset.Icc 1 N) σ z Y
      ≤ (2 * (Real.exp (1 / (2 * Real.pi)) - Real.exp (-(1 / (2 * Real.pi)))) / Real.log Y)
            * ((1 / Real.log 2) ^ 2
                * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (1 - 2 * σ) * (Real.log n) ^ 2)
        + (2 / Real.log Y + selbergFibreError z Y + (z : ℝ))
            * ((1 / Real.log 2) ^ 2
                * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(2 * σ)) * (Real.log n) ^ 2) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  exact sieveMeanSquare_le_of_norm_le_log (norm_ghsOuter_le hf N)
    (Finset.Icc 1 N) (fun n hn => (Finset.mem_Icc.1 hn).1) σ z Y hz hlogY

end RHTower.Sieve
end
