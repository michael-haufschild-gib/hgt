import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Coleman.MomentFunctionalJets

/-!
# Atomic translation and observable differences

Goto–Ishii, Lemma 5.1, identifies multiplication by a division series
with the adjoint of a translation difference on observables. For the
corpus's finite moment functional this identity holds for every observable,
without continuity or convergence conditions. The finite Amice transform
then transfers it to arbitrary polynomial tests of invariant jets.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Coleman
open Polynomial

/-- Multiplication by a monomial translates the observable's frequency argument. -/
theorem momentFunctional_frequency_translate (n : ℕ) (s : ℕ → ℝ) (f : ℝ[X]) :
    HTGeometry.momentFunctional s (X ^ n * f) =
      HTGeometry.momentFunctional (fun m => s (n + m)) f := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [mul_add, HTGeometry.momentFunctional_add, HTGeometry.momentFunctional_add, hf, hg]
  | monomial m a =>
    rw [← monomial_one_right_eq_X_pow, monomial_mul_monomial,
      HTGeometry.momentFunctional_monomial, HTGeometry.momentFunctional_monomial, one_mul]

/-- A finite atomic translation difference is dual to the observable's forward difference. -/
theorem momentFunctional_translation_difference (n : ℕ) (s : ℕ → ℝ) (f : ℝ[X]) :
    HTGeometry.momentFunctional s ((X ^ n - 1) * f) =
      HTGeometry.momentFunctional (fun m => s (n + m) - s m) f := by
  rw [sub_mul, one_mul, HTGeometry.momentFunctional_sub, momentFunctional_frequency_translate]
  simp only [HTGeometry.momentFunctional_eq_support_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- Polynomial tests of division-series jets are forward differences at the atomic frequencies. -/
theorem momentFunctional_divisionPolynomial_jets (n : ℕ) (f p : ℝ[X]) :
    HTGeometry.momentFunctional
        (fun k => multiplicativeJet k (divisionPolynomial n * f.comp (1 + X))) p =
      HTGeometry.momentFunctional
        (fun m => p.eval ((n + m : ℕ) : ℝ) - p.eval (m : ℝ)) f := by
  have hcomp : divisionPolynomial n * f.comp (1 + X) =
      ((X ^ n - 1) * f).comp (1 + X) := by
    simp only [divisionPolynomial, mul_comp, sub_comp, pow_comp, X_comp, one_comp]
  rw [hcomp, momentFunctional_multiplicativeJets, momentFunctional_translation_difference]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Coleman

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.Coleman.momentFunctional_translation_difference
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.Coleman.momentFunctional_divisionPolynomial_jets
