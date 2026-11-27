import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Grid

/-! # Reflected power sums of a centered finite preparation -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity

open Polynomial Finset Real

/-- At every real damping, an integral doubled mean converts the centered
trace comparison into equality of two ordinary power sums. -/
theorem reflected_exponentials {I : Type*} [Fintype I] [Nonempty I] (k : I → ℕ)
    {c : ℕ} (align : 2*(∑ i, k i)=Fintype.card I*c) (bounded : ∀ i, k i≤c) (t : ℝ) :
    agrees (levels k) t ↔ (∑ i, (exp t)^k i)=∑ i, (exp t)^(c-k i) := by
  let m := ∑ i, k i
  have shift (i : I) : m-k i+c=m+(c-k i) := by
    have h : k i ≤ m := single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (mem_univ i)
    have := bounded i
    omega
  have test := imbalancePolynomial_root k t
  rw [←expand_grid k align,expand_eq_comp_X_pow,aeval_comp,map_pow,aeval_X,←exp_nat_mul,
    mul_comm (Fintype.card I : ℝ),div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)] at test
  refine test.symm.trans ?_
  change aeval (exp t) (∑ i, ((X : ℤ[X])^(m+k i)-X^(m-k i+c)))=0 ↔ _
  simp only [shift,pow_add,←mul_sub,←mul_sum,sum_sub_distrib]
  simp only [map_mul,map_sub,map_sum,map_pow,aeval_X,mul_eq_zero,
    or_iff_right (pow_ne_zero m (exp_ne_zero t)),sub_eq_zero]

#print axioms reflected_exponentials

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity
