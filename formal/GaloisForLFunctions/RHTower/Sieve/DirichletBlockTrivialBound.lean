import GaloisForLFunctions.RHTower.Sieve.DirichletHeadTailSplit
import GaloisForLFunctions.RHTower.Sieve.HarmonicDyadicBlock

/-!
# The trivial competitor and a per-block choice of bound

Every block of the Dirichlet sum on the line `Re s = 1` obeys the harmonic bound
`log (M-1) - log (N-1)`, which on a dyadic block is close to `log 2`.  The derivative-test saving
beats it only on part of the range, so the assembly must be free to choose, block by block, which
of the two to use.

The primitive for that is the block-bound form of the dyadic tail estimate: supply any family of
per-block bounds and the tail is bounded by their sum.  The saving bound and the trivial bound are
then two ways of discharging a single hypothesis, and a block on which both hold obeys their
minimum.
-/

namespace RHTower.Sieve

open Finset

/-- **Trivial per-block bound.**  The harmonic sum over the block controls it. -/
theorem norm_dirichlet_block_trivial_le {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) (t : ℝ) :
    ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ Real.log ((M - 1 : ℕ) : ℝ) - Real.log ((N : ℝ) - 1) := by
  have hM1 : M = (M - 1) + 1 := by omega
  calc ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ ∑ n ∈ Finset.Ico N M, ‖(n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖ := norm_sum_le _ _
    _ = ∑ n ∈ Finset.Icc N (M - 1), 1 / (n : ℝ) := by
        rw [show Finset.Icc N (M - 1) = Finset.Ico N ((M - 1) + 1) from rfl, ← hM1]
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn1 : 1 ≤ n := le_trans (by omega) (Finset.mem_Ico.mp hn).1
        rw [norm_dirichletTerm hn1 t, one_div]
    _ ≤ Real.log ((M - 1 : ℕ) : ℝ) - Real.log ((N : ℝ) - 1) :=
        sum_Icc_one_div_le_log_sub hN (by omega)

/-- **Dyadic tail from an arbitrary family of per-block bounds.**  This is the primitive the
assembly should use: each block is discharged independently, by the saving bound or the trivial
bound, whichever is available there. -/
theorem dirichlet_tail_dyadic_of_blockBound {t : ℝ} {A R : ℕ} (b : ℕ → ℝ)
    (hb : ∀ r < R,
      ‖∑ n ∈ Finset.Ico (A * 2 ^ r) (A * 2 ^ (r + 1)),
          (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖ ≤ b r) :
    ‖∑ n ∈ Finset.Ico A (A * 2 ^ R), (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ ∑ r ∈ Finset.range R, b r := by
  refine le_trans (norm_sum_Ico_dyadic_le A _ R) ?_
  exact Finset.sum_le_sum fun r hr => hb r (Finset.mem_range.mp hr)

/-- **Trivial dyadic tail.**  Using only the harmonic bound on every block. -/
theorem dirichlet_tail_dyadic_trivial_le {t : ℝ} {A R : ℕ} (hA : 2 ≤ A) :
    ‖∑ n ∈ Finset.Ico A (A * 2 ^ R), (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ ∑ r ∈ Finset.range R,
          (Real.log ((A * 2 ^ (r + 1) - 1 : ℕ) : ℝ)
            - Real.log (((A * 2 ^ r : ℕ) : ℝ) - 1)) := by
  refine dirichlet_tail_dyadic_of_blockBound _ fun r _ => ?_
  have hN : 2 ≤ A * 2 ^ r := by
    calc 2 = 2 * 1 := (Nat.mul_one 2).symm
      _ ≤ A * 2 ^ r := Nat.mul_le_mul hA Nat.one_le_two_pow
  have hNM : A * 2 ^ r ≤ A * 2 ^ (r + 1) :=
    Nat.mul_le_mul_left A (Nat.pow_le_pow_right (by norm_num) (by omega))
  exact norm_dirichlet_block_trivial_le hN hNM t

/-- **Per-block minimum.**  On a block where the schedule applies, both bounds hold, so the block
obeys the smaller of them. -/
theorem norm_dirichlet_block_min_le {t : ℝ} (ht : 0 < t) {N k₀ : ℕ} (hN : 2 ≤ N) (hk₀ : 2 ≤ k₀)
    (hfac : Nat.factorial (k₀ - 1) ≤ N)
    (hlow : 8 * Real.pi * (N : ℝ) ^ ((1 : ℝ) / 3) ≤ t)
    (hhigh : t ≤ 2 * Real.pi * 2 ^ k₀ * (N : ℝ) ^ (k₀ - 1) * (N : ℝ) ^ (-(1 / 3) : ℝ)) :
    ‖∑ n ∈ Finset.Ico N (2 * N), (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ min (2560 * (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k₀))))
          (Real.log ((2 * N - 1 : ℕ) : ℝ) - Real.log ((N : ℝ) - 1)) :=
  le_min
    (dirichlet_block_saving_of_small_factorial ht (by omega) (by omega) (by omega) hk₀ hfac hlow
      hhigh)
    (norm_dirichlet_block_trivial_le hN (by omega) t)

end RHTower.Sieve
