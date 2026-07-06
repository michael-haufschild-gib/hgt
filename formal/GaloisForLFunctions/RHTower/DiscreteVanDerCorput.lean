/-
Discrete van der Corput: the finite Dirichlet-test bound and the reduction of an amplitude-weighted
exponential sum to its pure-phase partial sums.

For an antitone nonnegative real amplitude `a` and a complex sequence `b` whose partial sums are
bounded by `M`, summation by parts telescopes the amplitude:

  `‖Σ_{m<K} a m · b m‖ ≤ a 0 · M`.

This is the finite form of Dirichlet's test — the discrete companion of the van der Corput
first-derivative integral bound.  Applied with `a n = n^(σ−1)` (a decreasing amplitude, `σ < 1`) and
`b n = n^(iτ) = exp(iτ·log n)`, it bounds the reflected Dirichlet block `Σ_{n≤N} n^(z−1)` (`z = σ+iτ`)
by the largest pure-phase partial sum `max_k ‖Σ_{n≤k} exp(iτ·log n)‖`, moving the oscillatory content
onto the phase sums where the van der Corput integral bound (`norm_integral_cexp_logPhase_le`) applies
after a sum-to-integral comparison.
-/
import GaloisForLFunctions.RHTower.VanDerCorput

open Finset

noncomputable section

namespace RHTower

/-- **Finite Dirichlet-test bound.**  An antitone nonnegative amplitude against a complex sequence
with uniformly bounded partial sums telescopes to `a 0 · M`.  This generalises the geometric master
bound `CascadeGeometric.abel_geom_bound` off the special case `b m = w^m` (bounded partial sums via
`norm_geom_sum_le`) to an arbitrary sequence with a partial-sum bound. -/
theorem norm_sum_amplitude_phase_le {a : ℕ → ℝ} (hmono : Antitone a) (hnn : ∀ n, 0 ≤ a n)
    {b : ℕ → ℂ} {M : ℝ} (hM : ∀ n, ‖∑ j ∈ Finset.range n, b j‖ ≤ M) (K : ℕ) :
    ‖∑ m ∈ Finset.range K, (a m : ℂ) * b m‖ ≤ a 0 * M := by
  have hM0 : 0 ≤ M := le_trans (by simp) (hM 0)
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    exact mul_nonneg (hnn 0) hM0
  have hparts := Finset.sum_range_by_parts (fun m => (a m : ℂ)) (fun m => b m) K
  simp only [smul_eq_mul] at hparts
  have hstep : ∀ i : ℕ,
      ‖((a (i + 1) : ℂ) - (a i : ℂ)) * ∑ j ∈ Finset.range (i + 1), b j‖
        ≤ (a i - a (i + 1)) * M := by
    intro i
    rw [norm_mul]
    have hcast : ((a (i + 1) : ℂ) - (a i : ℂ)) = ((a (i + 1) - a i : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
    have habs : |a (i + 1) - a i| = a i - a (i + 1) := by
      rw [abs_sub_comm]; exact abs_of_nonneg (sub_nonneg.mpr (hmono (Nat.le_succ i)))
    rw [habs]
    exact mul_le_mul_of_nonneg_left (hM (i + 1)) (sub_nonneg.mpr (hmono (Nat.le_succ i)))
  calc ‖∑ m ∈ Finset.range K, (a m : ℂ) * b m‖
      = ‖(a (K - 1) : ℂ) * ∑ i ∈ Finset.range K, b i
          - ∑ i ∈ Finset.range (K - 1),
              (((a (i + 1) : ℂ)) - (a i : ℂ)) * ∑ j ∈ Finset.range (i + 1), b j‖ := by rw [hparts]
    _ ≤ ‖(a (K - 1) : ℂ) * ∑ i ∈ Finset.range K, b i‖
          + ‖∑ i ∈ Finset.range (K - 1),
              (((a (i + 1) : ℂ)) - (a i : ℂ)) * ∑ j ∈ Finset.range (i + 1), b j‖ := norm_sub_le _ _
    _ ≤ a (K - 1) * M + ∑ i ∈ Finset.range (K - 1), (a i - a (i + 1)) * M := by
        gcongr
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hnn _)]
          exact mul_le_mul_of_nonneg_left (hM K) (hnn _)
        · exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => hstep i)
    _ = a (K - 1) * M + (a 0 - a (K - 1)) * M := by
        rw [← Finset.sum_mul, Finset.sum_range_sub' a (K - 1)]
    _ = a 0 * M := by ring

end RHTower
