import GaloisForLFunctions.RHTower.Sieve.RamarePhaseBilinear

/-!
# Cauchy–Schwarz with harmonic weights

Splitting a Dirichlet polynomial over a ladder of prime ranges and then applying Cauchy–Schwarz
naively costs the *number* of ranges.  Weighting each range by its harmonic mass costs instead the
*total* harmonic mass, which is what the short-interval argument can afford: for positive weights
`v`,

    ‖∑_i F_i‖² ≤ (∑_i 1/v_i)(∑_i v_i ‖F_i‖²) ,

and along a geometric ladder `∑_i 1/v_i` with `v_i = log P_i` is the harmonic mass of the primes of
the ladder, not its length.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **Cauchy–Schwarz with arbitrary positive weights.** -/
theorem normSq_sum_le_weighted {ι : Type*} (I : Finset ι) (v : ι → ℝ) (hv : ∀ i ∈ I, 0 < v i)
    (F : ι → ℂ) :
    ‖∑ i ∈ I, F i‖ ^ (2 : ℕ) ≤ (∑ i ∈ I, 1 / v i) * ∑ i ∈ I, v i * ‖F i‖ ^ (2 : ℕ) := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq I (fun i => Real.sqrt (1 / v i))
    (fun i => Real.sqrt (v i) * ‖F i‖)
  have hsum : (∑ i ∈ I, Real.sqrt (1 / v i) * (Real.sqrt (v i) * ‖F i‖)) = ∑ i ∈ I, ‖F i‖ := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hvi := hv i hi
    have h1 : (0 : ℝ) ≤ 1 / v i := le_of_lt (div_pos one_pos hvi)
    have hs : Real.sqrt (1 / v i) * Real.sqrt (v i) = 1 := by
      rw [← Real.sqrt_mul h1, one_div, inv_mul_cancel₀ (ne_of_gt hvi), Real.sqrt_one]
    calc Real.sqrt (1 / v i) * (Real.sqrt (v i) * ‖F i‖)
        = (Real.sqrt (1 / v i) * Real.sqrt (v i)) * ‖F i‖ := by ring
      _ = ‖F i‖ := by rw [hs, one_mul]
  have hasq : (∑ i ∈ I, Real.sqrt (1 / v i) ^ (2 : ℕ)) = ∑ i ∈ I, 1 / v i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    exact Real.sq_sqrt (le_of_lt (div_pos one_pos (hv i hi)))
  have hbsq : (∑ i ∈ I, (Real.sqrt (v i) * ‖F i‖) ^ (2 : ℕ)) = ∑ i ∈ I, v i * ‖F i‖ ^ (2 : ℕ) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [mul_pow, Real.sq_sqrt (hv i hi).le]
  rw [hsum, hasq, hbsq] at hcs
  refine le_trans ?_ hcs
  have htri : ‖∑ i ∈ I, F i‖ ≤ ∑ i ∈ I, ‖F i‖ := norm_sum_le _ _
  exact pow_le_pow_left₀ (norm_nonneg _) htri 2

/-- **The harmonic split of a product decomposition.**  If a polynomial is a sum of products, its
mean square is controlled by the harmonic mass of the weights times the weighted mean squares. -/
theorem normSq_sum_mul_le_weighted {ι : Type*} (I : Finset ι) (v : ι → ℝ) (hv : ∀ i ∈ I, 0 < v i)
    (R S : ι → ℂ) :
    ‖∑ i ∈ I, R i * S i‖ ^ (2 : ℕ)
      ≤ (∑ i ∈ I, 1 / v i) * ∑ i ∈ I, v i * (‖R i‖ ^ (2 : ℕ) * ‖S i‖ ^ (2 : ℕ)) := by
  refine (normSq_sum_le_weighted I v hv (fun i => R i * S i)).trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_mul, mul_pow]

end

end RHTower.Sieve
