import GaloisForLFunctions.RHTower.Sieve.IntegerRowSum

/-!
# The integer row sum over `Fin N`

The Dirichlet sums of this folder are indexed by `Fin N`, while the row sum of
`IntegerRowSum.lean` is stated over `range N`.  The two agree, and the transfer is immediate: the
omitted diagonal term is `|m - m|^{-1} = 0` in Lean's convention, so erasing it changes neither sum
and both equal the full sum, which `Fin.sum_univ_eq_sum_range` identifies.
-/

namespace RHTower.Sieve

open Finset

/-- Erasing the diagonal changes nothing, the omitted term being zero. -/
theorem sum_erase_inv_abs_eq {N : ℕ} (m : Fin N) :
    ∑ n ∈ (Finset.univ : Finset (Fin N)).erase m, 1 / |((n : ℕ) : ℝ) - ((m : ℕ) : ℝ)|
      = ∑ n : Fin N, 1 / |((n : ℕ) : ℝ) - ((m : ℕ) : ℝ)| := by
  have hself : (1 : ℝ) / |((m : ℕ) : ℝ) - ((m : ℕ) : ℝ)| = 0 := by simp
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin N))
    (fun n : Fin N => 1 / |((n : ℕ) : ℝ) - ((m : ℕ) : ℝ)|) (Finset.mem_univ m)
  rw [hself] at hsplit
  linarith [hsplit]

theorem sum_erase_inv_abs_range_eq {N m : ℕ} (hm : m < N) :
    ∑ n ∈ (Finset.range N).erase m, 1 / |(n : ℝ) - (m : ℝ)|
      = ∑ n ∈ Finset.range N, 1 / |(n : ℝ) - (m : ℝ)| := by
  have hself : (1 : ℝ) / |(m : ℝ) - (m : ℝ)| = 0 := by simp
  have hsplit := Finset.add_sum_erase (Finset.range N)
    (fun n : ℕ => 1 / |(n : ℝ) - (m : ℝ)|) (Finset.mem_range.mpr hm)
  rw [hself] at hsplit
  linarith [hsplit]

/-- **The harmonic row sum over `Fin N`.** -/
theorem sum_inv_abs_fin_dist_le {N : ℕ} (m : Fin N) :
    ∑ n ∈ (Finset.univ : Finset (Fin N)).erase m, 1 / |((n : ℕ) : ℝ) - ((m : ℕ) : ℝ)|
      ≤ 2 * (1 + Real.log N) := by
  rw [sum_erase_inv_abs_eq m,
    Fin.sum_univ_eq_sum_range (fun n : ℕ => 1 / |(n : ℝ) - ((m : ℕ) : ℝ)|) N,
    ← sum_erase_inv_abs_range_eq m.isLt]
  exact sum_inv_abs_int_dist_le m.isLt

end RHTower.Sieve
