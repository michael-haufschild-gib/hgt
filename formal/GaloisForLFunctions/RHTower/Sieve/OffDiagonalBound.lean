import GaloisForLFunctions.RHTower.Sieve.OffDiagonalSwap

/-!
# The off-diagonal sum of a Dirichlet polynomial

`∑_m ∑_{n ≠ m} |a_m| |a_n| · 2/|log(m/n)| ≤ 4N(1 + log N) ∑_m |a_m|²`.

Three steps, each already proved: `LogSeparation.lean` replaces the logarithmic separations by
integer ones at the cost of a factor `N`; the arithmetic–geometric mean inequality decouples
`|a_m||a_n|` into `(|a_m|² + |a_n|²)/2`; and the two resulting halves are equal by
`OffDiagonalSwap.lean`, each being a row sum bounded by `2(1 + log N)`.
-/

namespace RHTower.Sieve

open Finset

/-- **The off-diagonal sum.** -/
theorem offDiagonal_le (N : ℕ) (a : Fin N → ℂ) :
    ∑ m : Fin N, ∑ n ∈ (Finset.univ : Finset (Fin N)).erase m,
        ‖a m‖ * ‖a n‖
          * (2 / |Real.log (((m : ℕ) : ℝ) + 1) - Real.log (((n : ℕ) : ℝ) + 1)|)
      ≤ 4 * (N : ℝ) * (1 + Real.log N) * ∑ m : Fin N, ‖a m‖ ^ (2 : ℕ) := by
  classical
  have hNR : (0 : ℝ) ≤ (N : ℝ) := by positivity
  -- termwise: decouple and pass to integer separations
  have hA : ∀ m : Fin N, ∀ n ∈ (Finset.univ : Finset (Fin N)).erase m,
      ‖a m‖ * ‖a n‖
          * (2 / |Real.log (((m : ℕ) : ℝ) + 1) - Real.log (((n : ℕ) : ℝ) + 1)|)
        ≤ (N : ℝ) * (‖a m‖ ^ (2 : ℕ) * (1 / |((m : ℕ) : ℝ) - ((n : ℕ) : ℝ)|))
          + (N : ℝ) * (‖a n‖ ^ (2 : ℕ) * (1 / |((m : ℕ) : ℝ) - ((n : ℕ) : ℝ)|)) := by
    intro m n hn
    have hmn : ((m : ℕ)) ≠ ((n : ℕ)) := by
      have hne : n ≠ m := (Finset.mem_erase.mp hn).1
      exact fun hcon => hne (Fin.val_injective hcon).symm
    have hlog := two_div_abs_log_le m.isLt n.isLt hmn
    have hprod : ‖a m‖ * ‖a n‖ ≤ (‖a m‖ ^ (2 : ℕ) + ‖a n‖ ^ (2 : ℕ)) / 2 := by
      nlinarith [sq_nonneg (‖a m‖ - ‖a n‖)]
    have hnn : (0 : ℝ) ≤ ‖a m‖ * ‖a n‖ := by positivity
    have hgap : (0 : ℝ) < |((m : ℕ) : ℝ) - ((n : ℕ) : ℝ)| := by
      rw [abs_pos, sub_ne_zero]
      intro hcon
      exact hmn (by exact_mod_cast hcon)
    calc ‖a m‖ * ‖a n‖
            * (2 / |Real.log (((m : ℕ) : ℝ) + 1) - Real.log (((n : ℕ) : ℝ) + 1)|)
        ≤ ‖a m‖ * ‖a n‖ * (2 * (N : ℝ) / |((m : ℕ) : ℝ) - ((n : ℕ) : ℝ)|) :=
          mul_le_mul_of_nonneg_left hlog hnn
      _ ≤ ((‖a m‖ ^ (2 : ℕ) + ‖a n‖ ^ (2 : ℕ)) / 2)
            * (2 * (N : ℝ) / |((m : ℕ) : ℝ) - ((n : ℕ) : ℝ)|) := by
          refine mul_le_mul_of_nonneg_right hprod ?_
          positivity
      _ = (N : ℝ) * (‖a m‖ ^ (2 : ℕ) * (1 / |((m : ℕ) : ℝ) - ((n : ℕ) : ℝ)|))
            + (N : ℝ) * (‖a n‖ ^ (2 : ℕ) * (1 / |((m : ℕ) : ℝ) - ((n : ℕ) : ℝ)|)) := by
          field_simp
  refine le_trans (Finset.sum_le_sum (fun m _ => Finset.sum_le_sum (hA m))) ?_
  -- split into the two halves
  rw [Finset.sum_congr rfl (fun m (_ : m ∈ (Finset.univ : Finset (Fin N))) =>
    Finset.sum_add_distrib), Finset.sum_add_distrib]
  -- the first half: the row sum against `‖a m‖²`
  have hB1 : ∑ m : Fin N, ∑ n ∈ (Finset.univ : Finset (Fin N)).erase m,
      (N : ℝ) * (‖a m‖ ^ (2 : ℕ) * (1 / |((m : ℕ) : ℝ) - ((n : ℕ) : ℝ)|))
      ≤ (N : ℝ) * (2 * (1 + Real.log N)) * ∑ m : Fin N, ‖a m‖ ^ (2 : ℕ) := by
    have hrow : ∀ m : Fin N,
        ∑ n ∈ (Finset.univ : Finset (Fin N)).erase m,
            (N : ℝ) * (‖a m‖ ^ (2 : ℕ) * (1 / |((m : ℕ) : ℝ) - ((n : ℕ) : ℝ)|))
          ≤ (N : ℝ) * (2 * (1 + Real.log N)) * ‖a m‖ ^ (2 : ℕ) := by
      intro m
      have hcomm : ∀ n ∈ (Finset.univ : Finset (Fin N)).erase m,
          (N : ℝ) * (‖a m‖ ^ (2 : ℕ) * (1 / |((m : ℕ) : ℝ) - ((n : ℕ) : ℝ)|))
            = ((N : ℝ) * ‖a m‖ ^ (2 : ℕ)) * (1 / |((n : ℕ) : ℝ) - ((m : ℕ) : ℝ)|) := by
        intro n _
        rw [abs_sub_comm]
        ring
      rw [Finset.sum_congr rfl hcomm, ← Finset.mul_sum]
      have hbound := sum_inv_abs_fin_dist_le m
      have hpos : (0 : ℝ) ≤ (N : ℝ) * ‖a m‖ ^ (2 : ℕ) := by positivity
      have := mul_le_mul_of_nonneg_left hbound hpos
      linarith [this]
    refine le_trans (Finset.sum_le_sum (fun m _ => hrow m)) ?_
    rw [Finset.mul_sum]
  -- the second half: the same, after swapping the order of summation
  have hB2 : ∑ m : Fin N, ∑ n ∈ (Finset.univ : Finset (Fin N)).erase m,
      (N : ℝ) * (‖a n‖ ^ (2 : ℕ) * (1 / |((m : ℕ) : ℝ) - ((n : ℕ) : ℝ)|))
      ≤ (N : ℝ) * (2 * (1 + Real.log N)) * ∑ m : Fin N, ‖a m‖ ^ (2 : ℕ) := by
    rw [sum_erase_swap (fun m n : Fin N =>
      (N : ℝ) * (‖a n‖ ^ (2 : ℕ) * (1 / |((m : ℕ) : ℝ) - ((n : ℕ) : ℝ)|)))]
    have hrow : ∀ n : Fin N,
        ∑ m ∈ (Finset.univ : Finset (Fin N)).erase n,
            (N : ℝ) * (‖a n‖ ^ (2 : ℕ) * (1 / |((m : ℕ) : ℝ) - ((n : ℕ) : ℝ)|))
          ≤ (N : ℝ) * (2 * (1 + Real.log N)) * ‖a n‖ ^ (2 : ℕ) := by
      intro n
      have hcomm : ∀ m ∈ (Finset.univ : Finset (Fin N)).erase n,
          (N : ℝ) * (‖a n‖ ^ (2 : ℕ) * (1 / |((m : ℕ) : ℝ) - ((n : ℕ) : ℝ)|))
            = ((N : ℝ) * ‖a n‖ ^ (2 : ℕ)) * (1 / |((m : ℕ) : ℝ) - ((n : ℕ) : ℝ)|) := by
        intro m _
        ring
      rw [Finset.sum_congr rfl hcomm, ← Finset.mul_sum]
      have hbound := sum_inv_abs_fin_dist_le n
      have hpos : (0 : ℝ) ≤ (N : ℝ) * ‖a n‖ ^ (2 : ℕ) := by positivity
      have := mul_le_mul_of_nonneg_left hbound hpos
      linarith [this]
    refine le_trans (Finset.sum_le_sum (fun n _ => hrow n)) ?_
    rw [Finset.mul_sum]
  linarith [hB1, hB2]

end RHTower.Sieve
