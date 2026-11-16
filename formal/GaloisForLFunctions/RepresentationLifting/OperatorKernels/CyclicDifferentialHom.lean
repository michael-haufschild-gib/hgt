import GaloisForLFunctions.RepresentationLifting.OperatorKernels.CyclicOperatorHom
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Cyclic modules in polynomial differential representations

The equation Dⁿf=0 cuts out exactly the polynomials of degree below n
in characteristic zero. Evaluation at the cyclic generator therefore
identifies Hom(K[X]/Xⁿ, K[t] with X acting as D) with this degree space.
For any nonzero symbol p, the same kernel is the degree space below its
order of vanishing at zero. The target is infinite-dimensional, but every
nonzero cyclic presentation has finite Hom dimension.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.OperatorKernels
open Polynomial
open scoped Classical

variable {K : Type*} [Field K] [CharZero K]

/-- The differential kernel is the actual degree filtration, including n=0. -/
theorem ker_polynomialDerivative_pow (n : ℕ) :
    LinearMap.ker ((derivative : Module.End K K[X]) ^ n) = degreeLT K n := by
  ext f
  rw [LinearMap.mem_ker, Module.End.pow_apply, mem_degreeLT]
  constructor
  · intro h
    rw [degree_lt_iff_coeff_zero]
    intro j hj
    have hc := congrArg (fun q : K[X] => q.coeff (j - n)) h
    rw [coeff_iterate_derivative, Nat.sub_add_cancel hj, coeff_zero, nsmul_eq_mul] at hc
    have hn : (j.descFactorial n : K) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hj))
    exact (mul_eq_zero.mp hc).resolve_left hn
  · exact iterate_derivative_eq_zero_of_degree_lt

/-- Cyclic differential maps are parametrized by their first n polynomial coefficients. -/
def cyclicDifferentialHomEquiv (n : ℕ) :
    CyclicOperatorHom (derivative : Module.End K K[X]) (X ^ n) ≃ₗ[K] (Fin n → K) :=
  (cyclicOperatorHomEquiv derivative (X ^ n)).trans
    ((LinearEquiv.ofEq _ _ (by
      rw [map_pow, aeval_X, ker_polynomialDerivative_pow])).trans (degreeLTEquiv K n))

/-- Exact finite dimension inside the infinite-dimensional differential representation. -/
theorem finrank_cyclicDifferentialHom (n : ℕ) :
    Module.finrank K (CyclicOperatorHom (derivative : Module.End K K[X]) (X ^ n)) = n := by
  rw [(cyclicDifferentialHomEquiv (K := K) n).finrank_eq]
  simp

omit [CharZero K] in
/-- A symbol coprime to X acts injectively on polynomials: Bézout applies to each
vector's finite derivative horizon. -/
private theorem ker_aeval_derivative_eq_bot {q : K[X]} (hq : ¬ X ∣ q) :
    LinearMap.ker (aeval (derivative : Module.End K K[X]) q) = ⊥ := by
  apply LinearMap.ker_eq_bot'.mpr
  intro f hf
  let N := f.natDegree + 1
  have hN : ((derivative : Module.End K K[X]) ^ N) f = 0 := by
    rw [Module.End.pow_apply]
    exact iterate_derivative_eq_zero (Nat.lt_succ_self _)
  have hcop : IsCoprime q ((X : K[X]) ^ N) :=
    ((dvd_or_isCoprime X q irreducible_X).resolve_left hq).symm.pow_right
  obtain ⟨a, b, hab⟩ := hcop
  have he := congrArg (fun r : K[X] => aeval (derivative : Module.End K K[X]) r f) hab
  simp only [map_add, map_mul, map_one, map_pow, aeval_X, LinearMap.add_apply,
    Module.End.mul_apply] at he
  simpa [hf, hN] using he.symm

/-- For every nonzero constant-coefficient differential symbol, its polynomial
solution space depends only on its order of vanishing at zero. -/
theorem ker_aeval_derivative_of_ne_zero {q : K[X]} (hq : q ≠ 0) :
    LinearMap.ker (aeval (derivative : Module.End K K[X]) q) =
      degreeLT K q.natTrailingDegree := by
  obtain ⟨r, hqr, hr⟩ := q.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hq 0
  simp only [C_0, sub_zero, rootMultiplicity_eq_natTrailingDegree'] at hqr hr
  have hi := LinearMap.ker_eq_bot.mp (ker_aeval_derivative_eq_bot hr)
  rw [← ker_polynomialDerivative_pow]
  nth_rw 1 [hqr]
  rw [mul_comm, map_mul, map_pow, aeval_X]
  ext f
  simp only [LinearMap.mem_ker, Module.End.mul_apply]
  constructor
  · intro h
    apply hi
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

/-- Unconditional classification, including the identically zero operator. -/
theorem ker_aeval_derivative (q : K[X]) :
    LinearMap.ker (aeval (derivative : Module.End K K[X]) q) =
      if q = 0 then ⊤ else degreeLT K q.natTrailingDegree := by
  by_cases hq : q = 0
  · simp [hq]
  · rw [if_neg hq]
    exact ker_aeval_derivative_of_ne_zero hq

/-- Every nonzero cyclic differential presentation has its exact finite Hom dimension. -/
theorem zero_or_finrank_cyclicDifferentialHom (q : K[X]) :
    q = 0 ∨ Module.finrank K
      (CyclicOperatorHom (derivative : Module.End K K[X]) q) = q.natTrailingDegree := by
  by_cases hq : q = 0
  · exact Or.inl hq
  · right
    rw [finrank_cyclicOperatorHom, ker_aeval_derivative_of_ne_zero hq,
      (degreeLTEquiv K q.natTrailingDegree).finrank_eq]
    simp

end GaloisForLFunctions.RepresentationLifting.OperatorKernels

#print axioms GaloisForLFunctions.RepresentationLifting.OperatorKernels.ker_polynomialDerivative_pow
#print axioms GaloisForLFunctions.RepresentationLifting.OperatorKernels.cyclicDifferentialHomEquiv
#print axioms GaloisForLFunctions.RepresentationLifting.OperatorKernels.finrank_cyclicDifferentialHom
#print axioms GaloisForLFunctions.RepresentationLifting.OperatorKernels.ker_aeval_derivative
#print axioms GaloisForLFunctions.RepresentationLifting.OperatorKernels.zero_or_finrank_cyclicDifferentialHom

