import GaloisForLFunctions.RHTower.Sieve.FejerSymmBound

/-!
# Localisation of a Dirichlet polynomial by the Fejér weight

Writing `W(T, L)` for the symmetric Fejér pairing at frequency `L`, the coefficient sum splits into
the term whose frequency vanishes and a tail:

`‖∑_{n < N} a_n W(T, log n) - a_1 T‖ ≤ ∑_{n ≥ 2} |a_n| · 4/(T (log n)²)`.

The frequency vanishes only at `n = 1`, where the weight is exactly `T`; every other frequency is
`log n ≥ log 2 > 0` and its weight is `O(T^{-1}(log n)^{-2})`.

So the Fejér average of a Dirichlet polynomial equals its first coefficient times `T`, up to an error
governed entirely by the remaining coefficients and the square-summable kernel tail.  This is the
localisation a short-interval argument performs.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

/-- The symmetric Fejér weight at a frequency. -/
noncomputable def fejerWeightAt (T : ℝ) (L : ℝ) : ℂ :=
  (∫ t in (0 : ℝ)..T, ((1 - t / T : ℝ) : ℂ) * Complex.exp (((t * L : ℝ) : ℂ) * Complex.I))
    + (∫ t in (0 : ℝ)..T,
        ((1 - t / T : ℝ) : ℂ) * Complex.exp (((t * (-L) : ℝ) : ℂ) * Complex.I))

/-- At the trivial frequency the weight is the whole interval. -/
theorem fejerWeightAt_zero {T : ℝ} (hT : 0 < T) : fejerWeightAt T 0 = (T : ℂ) := by
  rw [fejerWeightAt, neg_zero, integral_fejer_zero hT]
  push_cast
  ring

/-- Away from the trivial frequency the weight is small. -/
theorem norm_fejerWeightAt_le {T : ℝ} (hT : 0 < T) {L : ℝ} (hL : L ≠ 0) :
    ‖fejerWeightAt T L‖ ≤ 4 / (T * L ^ (2 : ℕ)) :=
  norm_integral_fejer_symm_le_inv L hL hT

/-- The frequency of the first term vanishes. -/
theorem log_succ_zero {N : ℕ} (hN : 0 < N) :
    Real.log (((((⟨0, hN⟩ : Fin N) : ℕ)) : ℝ) + 1) = 0 := by
  norm_num

/-- Every other frequency is nonzero. -/
theorem log_succ_ne_zero {N : ℕ} {n : Fin N} (hn : n ≠ ⟨0, n.pos⟩) :
    Real.log ((((n : ℕ)) : ℝ) + 1) ≠ 0 := by
  have hpos : 0 < (n : ℕ) := by
    rcases Nat.eq_zero_or_pos (n : ℕ) with h | h
    · exact absurd (Fin.ext h) hn
    · exact h
  have hone : (1 : ℝ) < ((n : ℕ) : ℝ) + 1 := by
    have : (1 : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hpos
    linarith
  exact ne_of_gt (Real.log_pos hone)

/-- **Localisation: the Fejér average is the first coefficient, up to a controlled tail.** -/
theorem norm_fejer_dirPoly_sub_main_le (N : ℕ) (hN : 0 < N) (a : Fin N → ℂ) {T : ℝ}
    (hT : 0 < T) :
    ‖(∑ n : Fin N, a n * fejerWeightAt T (Real.log (((n : ℕ) : ℝ) + 1)))
        - a ⟨0, hN⟩ * (T : ℂ)‖
      ≤ ∑ n ∈ (Finset.univ : Finset (Fin N)).erase ⟨0, hN⟩,
          ‖a n‖ * (4 / (T * (Real.log (((n : ℕ) : ℝ) + 1)) ^ (2 : ℕ))) := by
  classical
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin N))
    (fun n : Fin N => a n * fejerWeightAt T (Real.log (((n : ℕ) : ℝ) + 1)))
    (Finset.mem_univ (⟨0, hN⟩ : Fin N))
  have hmain : a ⟨0, hN⟩ * fejerWeightAt T (Real.log (((((⟨0, hN⟩ : Fin N) : ℕ)) : ℝ) + 1))
      = a ⟨0, hN⟩ * (T : ℂ) := by
    rw [log_succ_zero hN, fejerWeightAt_zero hT]
  rw [← hsplit, hmain, add_sub_cancel_left]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun n hn => ?_
  have hne : n ≠ ⟨0, n.pos⟩ := by
    intro hcon
    exact (Finset.mem_erase.mp hn).1 (by simpa using hcon)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_fejerWeightAt_le hT (log_succ_ne_zero hne))
    (norm_nonneg _)

end RHTower.Sieve
