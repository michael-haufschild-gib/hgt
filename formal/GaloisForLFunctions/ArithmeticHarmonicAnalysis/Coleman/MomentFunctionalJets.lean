import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Coleman.MultiplicativeJets
import GaloisForLFunctions.HTGeometry.MomentHankelStrict

/-!
# Multiplicative jets as finite moment functionals

The polynomial Amice transform sends `X^n` to `(1+X)^n`.
Its invariant derivatives recover the existing moment functional at
integral frequencies. Thus translation congruences can be consumed by
the corpus's moment and Hankel calculus.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Coleman
open Polynomial

/-- The finite Amice transform identifies invariant jets with frequency moments. -/
theorem multiplicativeJet_comp_eq_momentFunctional (k : ℕ) (f : ℝ[X]) :
    multiplicativeJet k (f.comp (1 + X)) =
      HTGeometry.momentFunctional (fun n => (n : ℝ) ^ k) f := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [add_comp, multiplicativeJet_add, HTGeometry.momentFunctional_add, hf, hg]
  | monomial n a =>
    rw [monomial_comp, multiplicativeJet_C_mul, multiplicativeJet_character,
      HTGeometry.momentFunctional_monomial]

/-- A finite weighted transform has exactly its expected power moments. -/
theorem multiplicativeJet_comp_support_sum (k : ℕ) (f : ℝ[X]) :
    multiplicativeJet k (f.comp (1 + X)) =
      ∑ n ∈ f.support, f.coeff n * (n : ℝ) ^ k := by
  rw [multiplicativeJet_comp_eq_momentFunctional,
    HTGeometry.momentFunctional_eq_support_sum]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Coleman

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.Coleman.multiplicativeJet_comp_eq_momentFunctional
