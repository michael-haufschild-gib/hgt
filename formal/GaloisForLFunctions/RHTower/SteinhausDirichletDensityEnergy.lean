import GaloisForLFunctions.RHTower.SteinhausPrimeConvolutionEnergy
import GaloisForLFunctions.RHTower.SteinhausDirichletLogCost

open Complex MeasureTheory Finset
noncomputable section
namespace RHTower
open SteinhausModel Sieve

/-- Weighted selected-prime occupation of a normalized Dirichlet density is
bounded by logarithmic frequency cost. -/
theorem dirichletDensity_primeOccupation_logCost_le
    (P S : Finset ℕ) (a : ℕ → ℂ) (hP : ∀ p ∈ P, Nat.Prime p)
    (hS : ∀ n ∈ S, n ≠ 0) (hnorm : ∑ n ∈ S, ‖a n‖ ^ 2 = 1)
    {ell : ℝ} (hell : 0 < ell) (hlog : ∀ p ∈ P, ell ≤ Real.log p) :
    (∑ n ∈ S, ((primeFactorsIn P n).card : ℝ) * ‖a n‖ ^ 2) ≤
      Real.log (∑ n ∈ S, (n : ℝ) * ‖a n‖ ^ 2) / ell := by
  have hpoint (n : ℕ) (hn : n ∈ S) :
      ell * ((primeFactorsIn P n).card : ℝ) ≤ Real.log n := by
    calc
      _ = ∑ p ∈ primeFactorsIn P n, ell := by simp [mul_comm]
      _ ≤ ∑ p ∈ primeFactorsIn P n, Real.log p :=
        sum_le_sum (fun p hp => hlog p (mem_primeFactorsIn.mp hp).1)
      _ ≤ _ := primeDivisorLogWeight_le_log_frequency P hP (hS n hn)
  have hsum : ell * (∑ n ∈ S, ((primeFactorsIn P n).card : ℝ) * ‖a n‖ ^ 2) ≤
      ∑ n ∈ S, Real.log n * ‖a n‖ ^ 2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hpoint n hn) (sq_nonneg ‖a n‖)
  have hjensen := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (t := S) (w := fun n => ‖a n‖ ^ 2) (p := fun n => (n : ℝ))
    (fun _ _ => sq_nonneg _) hnorm
    (fun n hn => (by exact_mod_cast Nat.pos_of_ne_zero (hS n hn) : (0 : ℝ) < n))
  have hj : (∑ n ∈ S, Real.log n * ‖a n‖ ^ 2) ≤
      Real.log (∑ n ∈ S, (n : ℝ) * ‖a n‖ ^ 2) := by
    simpa only [smul_eq_mul, mul_comm] using hjensen
  exact (le_div_iff₀ hell).mpr (by nlinarith [hsum.trans hj])

/-- Actual prime-polynomial second moment under an arbitrary normalized
Dirichlet square density, with logarithmic frequency cost. -/
theorem integral_normSq_primePoly_mul_density_le_logCost
    (P S : Finset ℕ) (v a : ℕ → ℂ) (hP : ∀ p ∈ P, Nat.Prime p)
    (hS : ∀ n ∈ S, n ≠ 0) (hnorm : ∑ n ∈ S, ‖a n‖ ^ 2 = 1)
    {ell : ℝ} (hell : 0 < ell) (hlog : ∀ p ∈ P, ell ≤ Real.log p) :
    (∫ ω, ‖∑ p ∈ P, v p * X p ω‖ ^ 2 *
      ‖∑ n ∈ S, a n * X n ω‖ ^ 2 ∂steinhausMeasure) ≤
      (∑ p ∈ P, ‖v p‖ ^ 2) *
        (1 + Real.log (∑ n ∈ S, (n : ℝ) * ‖a n‖ ^ 2) / ell) := by
  have h := integral_normSq_primePoly_mul_density_le_occupation P S v a hP hS
  have heq : (∑ n ∈ S, (1 + ((primeFactorsIn P n).card : ℝ)) * ‖a n‖ ^ 2) =
      1 + ∑ n ∈ S, ((primeFactorsIn P n).card : ℝ) * ‖a n‖ ^ 2 := by
    simp_rw [add_mul, one_mul, sum_add_distrib, hnorm]
  rw [heq] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (add_le_add (le_refl 1) (dirichletDensity_primeOccupation_logCost_le P S a hP hS hnorm hell hlog))
    (sum_nonneg (fun _ _ => sq_nonneg _)))

end RHTower
