import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Scaling rigidity and nilpotence in finite algebras

An algebra endomorphism sends powers of a scaled element to eigenvectors with
the corresponding scalar powers as eigenvalues. Finite-dimensionality forces
nilpotence when those scalar powers are distinct. Consequently a positive real
scaling of a nonnilpotent element is trivial, even without an inner product.

For conjugation of complex linear operators this gives the finite-dimensional
nilpotence boundary of the no-scalar-monodromy mechanism in Lemma 5.3 of Alexa,
*Gauge Rigidity and Holonomy Classification of Time-Scaled Intertwining
Cocycles on Hilbert Bundles*.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Distinct powers of a scaling factor force a scaled element to be nilpotent. -/
theorem isNilpotent_of_algHom_scale {K A : Type*} [Field K] [Ring A]
    [Algebra K A] [FiniteDimensional K A] (e : A →ₐ[K] A) (a : A) (q : K)
    (hq : Function.Injective (fun n : ℕ => q ^ n)) (hscale : e a = q • a) :
    IsNilpotent a := by
  by_contra hn
  have hp : ∀ n : ℕ, a ^ n ≠ 0 := fun n h => hn ⟨n, h⟩
  have he (n : ℕ) : Module.End.HasEigenvalue e.toLinearMap (q ^ n) := by
    apply Module.End.hasEigenvalue_of_hasEigenvector
      (x := a ^ n)
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hp n⟩
    change e (a ^ n) = q ^ n • a ^ n
    rw [map_pow, hscale, smul_pow]
  have hf : Set.Finite (Set.range (fun n : ℕ => q ^ n)) :=
    (Module.End.finite_hasEigenvalue e.toLinearMap).subset
      (by rintro _ ⟨n, rfl⟩; exact he n)
  exact (Set.infinite_range_of_injective hq) hf

/-- Positive real scaling is trivial unless the scaled element is nilpotent. -/
theorem real_algHom_scale_eq_one_or_nilpotent {A : Type*} [Ring A]
    [Algebra ℝ A] [FiniteDimensional ℝ A] (e : A →ₐ[ℝ] A) (a : A) (q : ℝ)
    (hq : 0 < q) (hscale : e a = q • a) : q = 1 ∨ IsNilpotent a := by
  by_cases heq : q = 1
  · exact Or.inl heq
  · exact Or.inr (isNilpotent_of_algHom_scale e a q (pow_right_injective₀ hq heq) hscale)

/-- An invertible element of a nonzero finite real algebra cannot acquire a positive scale. -/
theorem real_algHom_unit_scale_rigid {A : Type*} [Ring A] [Nontrivial A]
    [Algebra ℝ A] [FiniteDimensional ℝ A] (e : A →ₐ[ℝ] A) (a : A) (ha : IsUnit a)
    (q : ℝ) (hq : 0 < q) (hscale : e a = q • a) : q = 1 :=
  (real_algHom_scale_eq_one_or_nilpotent e a q hq hscale).resolve_right ha.not_isNilpotent

/-- Similarity to a scalar multiple with distinct scalar powers forces nilpotence. -/
theorem isNilpotent_of_conj_scale {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (e : V ≃ₗ[K] V) (a : Module.End K V)
    (q : K) (hq : Function.Injective (fun n : ℕ => q ^ n))
    (hscale : e.conj a = q • a) : IsNilpotent a :=
  isNilpotent_of_algHom_scale (e.conjAlgEquiv K).toAlgHom a q hq hscale

/-- A positive real time scale under arbitrary complex similarity is one or has nilpotent generator. -/
theorem complex_conj_scale_eq_one_or_nilpotent {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (e : V ≃ₗ[ℂ] V) (a : Module.End ℂ V)
    (q : ℝ) (hq : 0 < q) (hscale : e.conj a = (q : ℂ) • a) :
    q = 1 ∨ IsNilpotent a := by
  by_cases heq : q = 1
  · exact Or.inl heq
  · right
    apply isNilpotent_of_conj_scale e a (q : ℂ) _ hscale
    intro m n h
    apply pow_right_injective₀ hq heq
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_pow] using h

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.isNilpotent_of_algHom_scale
#print axioms GaloisForLFunctions.HTGeometry.real_algHom_unit_scale_rigid
#print axioms GaloisForLFunctions.HTGeometry.complex_conj_scale_eq_one_or_nilpotent
