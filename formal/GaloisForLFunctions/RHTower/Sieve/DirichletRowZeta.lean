import GaloisForLFunctions.RHTower.Sieve.DirichletRow
import GaloisForLFunctions.RHTower.Sieve.GramEntryZetaBound

/-!
# The Gram entry of two Dirichlet rows, against `ζ`

`Sieve/DirichletRow.inner_dirRow` identifies the Gram entry with the exponential sum at the
frequency difference, and `Sieve/GramEntryZetaBound.norm_sum_expSum_le_zeta` bounds that sum by
`‖ζ(1/2+iτ)‖` plus elementary terms.  Composing them puts the Halász–Montgomery input
(`Sieve/DirichletRow.dirichlet_bessel`) in the form Jutila's averaging step consumes: the only
non-elementary quantity in a Gram row is a sum of `‖ζ‖` at the frequency differences.
-/

namespace RHTower.Sieve

open Finset Complex

noncomputable section

/-- The Gram entry, written as a prefix sum of pure powers. -/
theorem inner_dirRow_eq_sum_range (N : ℕ) {t u : ℝ} (htu : t ≠ u) :
    (inner (𝕜 := ℂ) (dirRow N t) (dirRow N u))
      = ∑ n ∈ Finset.range (N + 1), (n : ℂ) ^ (-(((t - u : ℝ)) : ℂ) * Complex.I) := by
  classical
  have hne : ((t - u : ℝ) : ℂ) ≠ 0 := by
    intro h
    have : (t - u : ℝ) = 0 := by exact_mod_cast h
    exact htu (by linarith)
  have hexp : -(((t - u : ℝ)) : ℂ) * Complex.I ≠ 0 := by
    intro h
    rcases mul_eq_zero.1 h with h1 | h2
    · exact hne (neg_eq_zero.1 h1)
    · exact absurd h2 Complex.I_ne_zero
  rw [inner_dirRow, Finset.sum_range_succ']
  have h0 : ((0 : ℕ) : ℂ) ^ (-(((t - u : ℝ)) : ℂ) * Complex.I) = 0 := by
    rw [Nat.cast_zero]
    exact Complex.zero_cpow hexp
  rw [h0, add_zero, ← Fin.sum_univ_eq_sum_range
    (fun n => ((n + 1 : ℕ) : ℂ) ^ (-(((t - u : ℝ)) : ℂ) * Complex.I)) N]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hn0 : (0 : ℝ) < ((n : ℕ) + 1 : ℕ) := by positivity
  have hcast : ((((n : ℕ) + 1 : ℕ)) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [Complex.cpow_def_of_ne_zero hcast]
  congr 1
  rw [← Complex.natCast_log]
  push_cast
  ring

/-- **The Gram entry of two Dirichlet rows, bounded through `ζ`.**  Only `‖ζ‖` is non-elementary. -/
theorem norm_inner_dirRow_le_zeta (N : ℕ) {t u : ℝ} (h : 2 ≤ |t - u|) :
    ‖(inner (𝕜 := ℂ) (dirRow N t) (dirRow N u))‖
      ≤ 2 * criticalPrefixBound (N + 1) (t - u) * ((N : ℝ)) ^ ((1 : ℝ) / 2) := by
  have htu : t ≠ u := by
    intro hEq
    rw [hEq] at h
    simp at h
    linarith
  rw [inner_dirRow_eq_sum_range N htu]
  have hbase := norm_sum_expSum_le_zeta (N + 1) (t := t - u) h
  refine le_trans hbase (le_of_eq ?_)
  congr 2

end

end RHTower.Sieve
