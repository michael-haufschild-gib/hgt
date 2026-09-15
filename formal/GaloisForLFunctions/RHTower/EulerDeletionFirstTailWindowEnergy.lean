import GaloisForLFunctions.RHTower.EulerDeletionFirstTailMertens
import GaloisForLFunctions.RHTower.Sieve.MoebiusUnweighted

/-!
# The first EDQ tail as a weighted fixed-cutoff Möbius-window energy

The literal first complementary block is a family of Mertens increments with
one fixed lower endpoint. This identity retains its exact reciprocal Gram
weight and makes the signed correlation obligation explicit.
-/

noncomputable section
set_option autoImplicit false
open ArithmeticFunction
open scoped BigOperators

namespace RHTower.DeletionFirstTail

private theorem mertens_increment_eq_window (N L : ℕ) :
    Sieve.mertensM (N + L) - Sieve.mertensM N =
      ∑ m ∈ Finset.Ioc N (N + L), ((moebius m : ℤ) : ℝ) := by
  rw [show Finset.Ioc N (N + L) = Finset.Ico (N + 1) (N + L + 1) by
    ext m
    simp]
  rw [Sieve.mertensM, Sieve.mertensM]
  exact (Finset.sum_Ico_eq_sub _ (by omega)).symm

/-- The literal first EDQ tail is a Gram-weighted family of Möbius windows with cutoff `N` fixed. -/
theorem incrementEnergy_eq_weighted_window_energy (N : ℕ) :
    incrementEnergy N =
      ∑ n ∈ Finset.Ioc N (2 * N),
        ‖∑ m ∈ Finset.Ioc N n, Sieve.moebiusC m‖ ^ 2 /
          ((n : ℝ) * ((n : ℝ) + 1)) := by
  unfold incrementEnergy
  refine Finset.sum_congr rfl fun n hn => ?_
  have hNn : N ≤ n := (Finset.mem_Ioc.mp hn).1.le
  have hinc := mertens_increment_eq_window N (n - N)
  rw [Nat.add_sub_of_le hNn] at hinc
  rw [hinc]
  have hnorm := Sieve.normSq_sum_moebiusC_eq N (n - N)
  rw [Nat.add_sub_of_le hNn] at hnorm
  rw [hnorm]

end RHTower.DeletionFirstTail
