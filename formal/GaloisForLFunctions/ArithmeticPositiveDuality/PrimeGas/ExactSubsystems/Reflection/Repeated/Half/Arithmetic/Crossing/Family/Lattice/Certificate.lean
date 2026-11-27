import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Clearing

/-! # Algebraic coordinates of blind temperatures on a single frequency lattice -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice

open Finset Real Polynomial

variable {I : Type*} [Fintype I]

def levels (k : I → ℕ) (i : I) : ℝ := k i

/-- A nonreflecting list with a blind reading has an algebraic exponential
coordinate. The division by the number of states allows a fractional mean. -/
theorem algebraic_coordinate (k : I → ℕ) {t : ℝ} (asym : ¬Reflects (levels k))
    (hit : agrees (levels k) t) : IsAlgebraic ℤ (exp (t/Fintype.card I)) := by
  rcases isEmpty_or_nonempty I with he | hn
  · exact (asym ⟨0,Equiv.refl _,fun i => (he.false i).elim⟩).elim
  · letI := hn
    exact ⟨imbalancePolynomial k,imbalancePolynomial_ne_zero asym,(imbalancePolynomial_root k t).mpr hit⟩

#print axioms algebraic_coordinate

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice
