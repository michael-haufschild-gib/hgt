import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRationalBoundary
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRegularDifferentialDimension
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.RegularDifferentialEquivalence

/-!
# The exact rational boundary of the prime-power Kummer family

The regular differential dimension vanishes exactly when the covering
degree divides the branch exponent. At that boundary the quotient
radical is a rational parameter for the whole field. Conversely, any
rational presentation transports the zero differential space of the
zero-exponent model, forcing the same divisibility condition.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ)

/-- The actual prime-power Kummer field is rational precisely at the divisible branch boundary. -/
theorem squareKummer_rational_iff :
    Nonempty (FractionRing (SquareConstantField p s)[X] ≃ₐ[SquareConstantField p s]
      SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) ↔
      p ^ (s + 1) + 1 ∣ kummerExponent (p ^ (d + 1)) r := by
  let K := SquareConstantField p s
  let b := p ^ (d + 1) - 2
  let L₀ := SquareKummerField p s c b (kummerExponent (p ^ (d + 1)) 0)
  constructor
  · rintro ⟨e⟩
    have e₀ : FractionRing K[X] ≃ₐ[K] L₀ := by
      exact kummerBranchField_mul_degree_rationalEquiv c b (p ^ (s + 1)) 0
    have h₀ : Module.finrank K (globalRegularDifferentials K L₀) = 0 :=
      (squareKummer_regularDifferential_finrank_eq_zero_iff p s c d 0).mpr
        (by simp only [kummerExponent, Finset.range_zero, Finset.sum_empty]; exact dvd_zero _)
    have hdim := globalRegularDifferential_finrank_eq (e₀.symm.trans e)
    rw [h₀] at hdim
    exact (squareKummer_regularDifferential_finrank_eq_zero_iff p s c d r).mp hdim.symm
  · rintro ⟨t, ht⟩
    rw [ht]
    exact ⟨kummerBranchField_mul_degree_rationalEquiv c b (p ^ (s + 1)) t⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
