import GaloisForLFunctions.RHTower.SteinhausPrimeCorrelationBudget

open Complex MeasureTheory Finset
open scoped ComplexConjugate
noncomputable section
namespace RHTower
open SteinhausModel

/-- The literal original-law first prime moment of an arbitrary Dirichlet
square density is its multiplicative coefficient correlation. -/
theorem integral_character_mul_dirichletDensity
    (S : Finset ℕ) (a : ℕ → ℂ) (hS : ∀ n ∈ S, n ≠ 0) {p : ℕ} (hp : p ≠ 0) :
    (∫ ω, X p ω * ((‖∑ n ∈ S, a n * X n ω‖ ^ 2 : ℝ) : ℂ) ∂steinhausMeasure) =
      steinhausSpectralPrimeCorrelation S a p := by
  classical
  have hexp (ω : Omega) :
      X p ω * ((‖∑ n ∈ S, a n * X n ω‖ ^ 2 : ℝ) : ℂ) =
        ∑ n ∈ S, ∑ m ∈ S, (a n * conj (a m)) * (X (p * n) ω * conj (X m ω)) := by
    have hnrm : (∑ n ∈ S, a n * X n ω) * conj (∑ n ∈ S, a n * X n ω) =
        ((‖∑ n ∈ S, a n * X n ω‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj']
      push_cast
      ring
    rw [← hnrm]
    simp_rw [map_sum, sum_mul_sum, mul_sum]
    apply sum_congr rfl
    intro n hn
    apply sum_congr rfl
    intro m _
    rw [map_mul, X_mul hp (hS n hn)]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp)]
  rw [integral_finsetSum _ (fun n _ => integrable_finsetSum _
    (fun m _ => (integrable_X_mul_conj (p * n) m).const_mul _))]
  have hinner (n : ℕ) (hn : n ∈ S) :
      (∫ ω, ∑ m ∈ S, (a n * conj (a m)) * (X (p * n) ω * conj (X m ω)) ∂steinhausMeasure) =
        if p * n ∈ S then a n * conj (a (p * n)) else 0 := by
    rw [integral_finsetSum _ (fun m _ => (integrable_X_mul_conj (p * n) m).const_mul _)]
    calc
      _ = ∑ m ∈ S, if m = p * n then a n * conj (a m) else 0 := by
        apply sum_congr rfl
        intro m hm
        rw [integral_const_mul, integral_X_mul_conj (Nat.mul_ne_zero hp (hS n hn)) (hS m hm)]
        by_cases heq : m = p * n
        · simp [heq]
        · simp [heq, Ne.symm heq]
      _ = _ := sum_ite_eq' S (p * n) (fun m => a n * conj (a m))
  rw [sum_congr rfl hinner]
  simp only [steinhausSpectralPrimeCorrelation, sum_filter]

/-- Original normalized Dirichlet square densities satisfy a prime-moment
frequency budget even without independent or degree-one local factors. -/
theorem dirichletDensity_primeMoment_frequencyCost_lower
    (S P : Finset ℕ) (a : ℕ → ℂ) (hS : ∀ n ∈ S, n ≠ 0)
    (hP : ∀ p ∈ P, Nat.Prime p) (hnorm : ∑ n ∈ S, ‖a n‖ ^ 2 = 1) :
    1 + (∑ p ∈ P, ((p : ℝ) - 1) *
      ‖∫ ω, X p ω * ((‖∑ n ∈ S, a n * X n ω‖ ^ 2 : ℝ) : ℂ) ∂steinhausMeasure‖ ^ 2) ≤
      ∑ n ∈ S, (n : ℝ) * ‖a n‖ ^ 2 := by
  have heq : (∑ p ∈ P, ((p : ℝ) - 1) *
      ‖∫ ω, X p ω * ((‖∑ n ∈ S, a n * X n ω‖ ^ 2 : ℝ) : ℂ) ∂steinhausMeasure‖ ^ 2) =
      ∑ p ∈ P, ((p : ℝ) - 1) * ‖steinhausSpectralPrimeCorrelation S a p‖ ^ 2 := by
    apply sum_congr rfl
    intro p hp
    rw [integral_character_mul_dirichletDensity S a hS (hP p hp).ne_zero]
  rw [heq]
  exact steinhausSpectralPrimeCorrelation_frequencyCost_lower S P a hS hP hnorm

end RHTower
