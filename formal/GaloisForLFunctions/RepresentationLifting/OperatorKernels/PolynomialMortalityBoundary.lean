import GaloisForLFunctions.RepresentationLifting.OperatorKernels.LocalMortality
import GaloisForLFunctions.RepresentationLifting.OperatorKernels.CyclicDifferentialHom

/-!
# Local annihilation without a global annihilator

Polynomial differentiation kills each polynomial and each finite family,
but no power is the zero operator. Thus finite generation is essential
when passing from local mortality to one common annihilating product.
The exact power kernels are the existing polynomial degree filtration.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.OperatorKernels
open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- No derivative order annihilates the whole polynomial representation. -/
theorem polynomialDerivative_pow_ne_zero (n : ℕ) :
    (derivative : Module.End K K[X]) ^ n ≠ 0 := by
  intro hn
  have hX : (X : K[X]) ^ n ∈ LinearMap.ker ((derivative : Module.End K K[X]) ^ n) := by
    rw [hn]
    exact LinearMap.mem_ker.mpr rfl
  rw [ker_polynomialDerivative_pow, mem_degreeLT, degree_X_pow] at hX
  exact lt_irrefl _ hX

/-- Every polynomial dies at a finite derivative order. -/
theorem polynomialDerivative_pointwise_killable (f : K[X]) :
    ∃ T ∈ Submonoid.powers (derivative : Module.End K K[X]), T f = 0 := by
  refine ⟨derivative ^ (f.natDegree + 1), ⟨f.natDegree + 1, rfl⟩, ?_⟩
  rw [Module.End.pow_apply]
  exact iterate_derivative_eq_zero (Nat.lt_succ_self _)

/-- Finite sets can still be synchronized even in this infinite-dimensional representation. -/
theorem polynomialDerivative_finset_killable (s : Finset K[X]) :
    ∃ T ∈ Submonoid.powers (derivative : Module.End K K[X]), ∀ f ∈ s, T f = 0 :=
  exists_annihilator_finset _ polynomialDerivative_pointwise_killable s

/-- The derivative power semigroup has local mortality but contains no zero operator. -/
theorem polynomialDerivative_local_without_global :
    (∀ f : K[X], ∃ T ∈ Submonoid.powers (derivative : Module.End K K[X]), T f = 0) ∧
      (0 : Module.End K K[X]) ∉ Submonoid.powers derivative := by
  refine ⟨polynomialDerivative_pointwise_killable, ?_⟩
  rintro ⟨n, hn⟩
  exact polynomialDerivative_pow_ne_zero n hn

#print axioms polynomialDerivative_pow_ne_zero
#print axioms polynomialDerivative_finset_killable
#print axioms polynomialDerivative_local_without_global

end GaloisForLFunctions.RepresentationLifting.OperatorKernels
