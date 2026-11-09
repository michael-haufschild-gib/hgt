import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.FiniteUnitSpectrum
import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.IntegralityActsOnlyOnTheTorsion

/-!
# Polynomial functions of unit modulus on the prime orbit

Distinct monomials have distinct prime frequencies. Constant modulus on
the orbit therefore forces a polynomial to be one unimodular monomial.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

variable {P : Finset Nat.Primes}

/-- Evaluation of a complex polynomial along the prime orbit. -/
def complexOrbitValue (F : MvPolynomial P ℂ) (t : ℝ) : ℂ :=
  MvPolynomial.eval (orbitPoint P t) F

/-- Orbit restriction is a finite wave with distinct prime frequencies. -/
theorem complexOrbitValue_eq_wave (F : MvPolynomial P ℂ) (t : ℝ) :
    complexOrbitValue F t =
      finiteExpWave F.support F.coeff (fun α => -frequency α) t := by
  classical
  rw [complexOrbitValue, MvPolynomial.eval_eq]
  unfold finiteExpWave
  refine sum_congr rfl fun α _ => ?_
  congr 1
  simp only [orbitPoint, InfiniteRankWeilTheory.phase, ← Complex.exp_nat_mul,
    ← Complex.exp_sum, expChar]
  congr 1
  unfold frequency
  push_cast
  rw [← sum_neg_distrib, sum_mul, sum_mul, ← sum_subset (subset_univ α.support)
    (fun p _ hp => by rw [Finsupp.notMem_support_iff.mp hp]; simp)]
  refine sum_congr rfl fun p _ => ?_
  ring

/-- A monomial restricts to its single prime character. -/
theorem complexOrbitValue_monomial (α : P →₀ ℕ) (c : ℂ) (t : ℝ) :
    complexOrbitValue (MvPolynomial.monomial α c) t =
      c * expChar (-frequency α) t := by
  classical
  by_cases hc : c = 0
  · simp [hc, complexOrbitValue]
  · rw [complexOrbitValue_eq_wave]
    simp only [finiteExpWave, MvPolynomial.support_monomial, if_neg hc,
      sum_singleton, MvPolynomial.coeff_monomial, if_true]

/-- The frequency of a pure prime power. -/
theorem frequency_single (p : P) (n : ℕ) :
    frequency (Finsupp.single p n) = (n : ℝ) * Real.log ((p : Nat.Primes) : ℕ) := by
  classical
  simp only [frequency, Finsupp.single_apply, Nat.cast_ite, Nat.cast_zero,
    ite_mul, zero_mul, sum_ite_eq, mem_univ, if_true]

/-- Unit modulus on the prime orbit forces a single unimodular monomial. -/
theorem complexOrbitValue_unit_monomial (F : MvPolynomial P ℂ)
    (hunit : ∀ t, ‖complexOrbitValue F t‖ = 1) :
    ∃ α c, ‖c‖ = 1 ∧ F = MvPolynomial.monomial α c := by
  classical
  obtain ⟨α, hα, hc⟩ := finiteExpWave_unit_support F.support F.coeff
    (fun β => -frequency β)
    (fun β _ γ _ h => frequency_injective (neg_injective h))
    (fun β hβ => MvPolynomial.mem_support_iff.mp hβ)
    (fun t => by rw [← complexOrbitValue_eq_wave]; exact hunit t)
  refine ⟨α, F.coeff α, hc, ?_⟩
  conv_lhs => rw [MvPolynomial.as_sum F]
  rw [hα, sum_singleton]

#print axioms complexOrbitValue_unit_monomial

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
