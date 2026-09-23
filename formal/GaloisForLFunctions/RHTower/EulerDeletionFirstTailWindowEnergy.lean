import GaloisForLFunctions.RHTower.EulerDeletionFirstTailMertens
import GaloisForLFunctions.RHTower.Sieve.MoebiusUnweighted
import GaloisForLFunctions.RHTower.Sieve.DyadicMeanSquareGallagher

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
        ‖∑ m ∈ Finset.Ioc N n, Sieve.moebiusC m‖ ^ (2 : ℕ) /
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

/-- The first EDQ tail is the one-start diagonal of the fixed-window Möbius energy.
The outer Gram weight and every window length remain literal. -/
theorem incrementEnergy_eq_weighted_fixedWindowSq (N : ℕ) :
    incrementEnergy N =
      ∑ n ∈ Finset.Ioc N (2 * N),
        Sieve.fixedWindowSq (fun m => ((moebius m : ℤ) : ℝ)) (n - N) N /
          ((n : ℝ) * ((n : ℝ) + 1)) := by
  unfold incrementEnergy
  refine Finset.sum_congr rfl fun n hn => ?_
  have hNlt : N < n := (Finset.mem_Ioc.mp hn).1
  have hNn : N ≤ n := hNlt.le
  have hlen : 1 ≤ n - N := by omega
  have hinc := mertens_increment_eq_window N (n - N)
  rw [Nat.add_sub_of_le hNn] at hinc
  rw [hinc, Sieve.fixedWindowSq_eq_sq_sum _ hlen N]
  rw [Nat.add_sub_of_le hNn]

/-- A fixed EDQ start is one nonnegative summand of the literal dyadic start average. -/
theorem fixedWindowSq_le_dyadicMeanSquare (f : ℕ → ℝ) (N l : ℕ) (hN : 1 ≤ N) :
    Sieve.fixedWindowSq f l N ≤ Sieve.dyadicMeanSquare f l N (2 * N - 1) := by
  unfold Sieve.dyadicMeanSquare
  exact Finset.single_le_sum (fun z hz => Sieve.fixedWindowSq_nonneg f l z)
    (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)

/-- Exact reduction of the first-tail energy to dyadic window means.  It is an extraction
inequality only: closing it requires a pointwise or signed transfer beyond averaged control. -/
theorem incrementEnergy_le_weighted_dyadicMeanSquare (N : ℕ) (hN : 1 ≤ N) :
    incrementEnergy N ≤
      ∑ n ∈ Finset.Ioc N (2 * N),
        Sieve.dyadicMeanSquare (fun m => ((moebius m : ℤ) : ℝ)) (n - N) N (2 * N - 1) /
          ((n : ℝ) * ((n : ℝ) + 1)) := by
  rw [incrementEnergy_eq_weighted_fixedWindowSq]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn0 : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le N) (Finset.mem_Ioc.mp hn).1)
  exact div_le_div_of_nonneg_right
    (fixedWindowSq_le_dyadicMeanSquare _ N (n - N) hN)
    (mul_pos hn0 (by positivity)).le

end RHTower.DeletionFirstTail
