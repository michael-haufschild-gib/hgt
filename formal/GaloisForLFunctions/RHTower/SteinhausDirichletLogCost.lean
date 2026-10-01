import GaloisForLFunctions.RHTower.SteinhausDirichletDensityCost
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen

open Complex Finset MeasureTheory
noncomputable section
namespace RHTower
open SteinhausModel

/-- Selected distinct prime logarithms cannot exceed the logarithm of the
integer frequency they divide. -/
theorem primeDivisorLogWeight_le_log_frequency (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) {n : ℕ} (hn : n ≠ 0) :
    (∑ p ∈ P.filter (fun p => p ∣ n), Real.log p) ≤ Real.log n := by
  classical
  have hsub : P.filter (fun p => p ∣ n) ⊆ n.primeFactors := by
    intro p hp
    exact (hP p (mem_filter.mp hp).1).mem_primeFactors (mem_filter.mp hp).2 hn
  have hsum : (∑ p ∈ P.filter (fun p => p ∣ n), Real.log p) ≤
      ∑ p ∈ n.primeFactors, Real.log p :=
    sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ =>
      Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le))
  have htotal : (∑ p ∈ n.primeFactors, Real.log p) ≤ Real.log n := by
    rw [← Real.log_prod (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)]
    apply Real.log_le_log
    · exact prod_pos (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
    · have hh : ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)
      simpa only [Nat.cast_prod] using hh
  exact hsum.trans htotal

/-- The coefficient correlations of every normalized Dirichlet square density
obey the logarithmic prime occupation budget. -/
theorem steinhausSpectralPrimeCorrelation_logCost_lower
    (S P : Finset ℕ) (a : ℕ → ℂ) (hS : ∀ n ∈ S, n ≠ 0)
    (hP : ∀ p ∈ P, Nat.Prime p) (hnorm : ∑ n ∈ S, ‖a n‖ ^ 2 = 1) :
    (∑ p ∈ P, Real.log p * ‖steinhausSpectralPrimeCorrelation S a p‖ ^ 2) ≤
      Real.log (∑ n ∈ S, (n : ℝ) * ‖a n‖ ^ 2) := by
  classical
  have hmean : (∑ p ∈ P, Real.log p * ‖steinhausSpectralPrimeCorrelation S a p‖ ^ 2) ≤
      ∑ n ∈ S, Real.log n * ‖a n‖ ^ 2 := by
    calc
      _ ≤ ∑ p ∈ P, Real.log p * ∑ n ∈ S.filter (fun n => p ∣ n), ‖a n‖ ^ 2 := by
        apply sum_le_sum
        intro p hp
        exact mul_le_mul_of_nonneg_left (norm_steinhausSpectralPrimeCorrelation_sq_le S a hnorm (hP p hp).pos)
          (Real.log_nonneg (by exact_mod_cast (hP p hp).one_lt.le))
      _ = ∑ n ∈ S, (∑ p ∈ P.filter (fun p => p ∣ n), Real.log p) * ‖a n‖ ^ 2 := by
        simp_rw [sum_filter, mul_sum, mul_ite, mul_zero]
        rw [sum_comm]
        simp_rw [sum_mul, ite_mul, zero_mul]
      _ ≤ _ := sum_le_sum (fun n hn => mul_le_mul_of_nonneg_right
        (primeDivisorLogWeight_le_log_frequency P hP (hS n hn)) (sq_nonneg _))
  have hjensen := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (t := S) (w := fun n => ‖a n‖ ^ 2) (p := fun n => (n : ℝ))
    (fun _ _ => sq_nonneg _) hnorm
    (fun n hn => (by exact_mod_cast Nat.pos_of_ne_zero (hS n hn) : (0 : ℝ) < n))
  have hj : (∑ n ∈ S, Real.log n * ‖a n‖ ^ 2) ≤
      Real.log (∑ n ∈ S, (n : ℝ) * ‖a n‖ ^ 2) := by
    simpa only [smul_eq_mul, mul_comm] using hjensen
  exact hmean.trans hj

/-- The actual original-law prime moments satisfy the logarithmic cost bound,
with arbitrary complex finite Dirichlet coefficients. -/
theorem dirichletDensity_primeMoment_logCost_lower
    (S P : Finset ℕ) (a : ℕ → ℂ) (hS : ∀ n ∈ S, n ≠ 0)
    (hP : ∀ p ∈ P, Nat.Prime p) (hnorm : ∑ n ∈ S, ‖a n‖ ^ 2 = 1) :
    (∑ p ∈ P, Real.log p *
      ‖∫ ω, X p ω * ((‖∑ n ∈ S, a n * X n ω‖ ^ 2 : ℝ) : ℂ) ∂steinhausMeasure‖ ^ 2) ≤
      Real.log (∑ n ∈ S, (n : ℝ) * ‖a n‖ ^ 2) := by
  have heq : (∑ p ∈ P, Real.log p *
      ‖∫ ω, X p ω * ((‖∑ n ∈ S, a n * X n ω‖ ^ 2 : ℝ) : ℂ) ∂steinhausMeasure‖ ^ 2) =
      ∑ p ∈ P, Real.log p * ‖steinhausSpectralPrimeCorrelation S a p‖ ^ 2 := by
    apply sum_congr rfl
    intro p hp
    rw [integral_character_mul_dirichletDensity S a hS (hP p hp).ne_zero]
  rw [heq]
  exact steinhausSpectralPrimeCorrelation_logCost_lower S P a hS hP hnorm

end RHTower
