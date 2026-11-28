import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Commutators.Core

/-! # The measured lowering and raising operators are adjoint on the gas core -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Commutators

open CoassociativeSplitting
open scoped ComplexConjugate

private theorem adjoint_kets (K : Kernel) (p : Nat.Primes) (m n : Occupation) :
    inner ℂ (embed (lower K p (ket m))) (embed (ket n)) =
      inner ℂ (embed (ket m)) (embed (raise K p (ket n))) := by
  rw [lower_ket,raise_ket,embed.map_smul,embed.map_smul,inner_smul_left,inner_smul_right,
    ket_inner,ket_inner]
  by_cases h : m = n + particle p
  · subst m
    rw [add_tsub_cancel_right, add_count, if_pos rfl, if_pos rfl]
  · rw [if_neg h, mul_zero]
    by_cases zero : m p = 0
    · rw [zero,ladder,map_zero,zero_mul]
    · have ne : m-particle p ≠ n := fun e => h ((restore zero).symm.trans
        (congrArg (fun x : Occupation => x+particle p) e))
      rw [if_neg ne,mul_zero]

/-- Equality is in the inner product of the integer-labelled gas for
arbitrary finite superpositions on both sides. -/
theorem adjoint_core (K : Kernel) (p : Nat.Primes) (f g : Core) :
    inner ℂ (embed (lower K p f)) (embed g) = inner ℂ (embed f) (embed (raise K p g)) := by
  have single (m : Occupation) (c : ℂ) : Finsupp.single m c = c • ket m := by
    rw [ket, Finsupp.smul_single', mul_one]
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp only [map_add, inner_add_left, hu, hv]
  | single m c =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add u v hu hv => simp only [map_add, inner_add_right, hu, hv]
    | single n d =>
      rw [single m c,single n d]
      simp only [map_smul, inner_smul_left, inner_smul_right, adjoint_kets]

#print axioms adjoint_core

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Commutators
