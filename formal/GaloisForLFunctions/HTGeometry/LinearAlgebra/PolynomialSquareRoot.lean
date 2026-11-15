import GaloisForLFunctions.HTGeometry.Polynomial.PolynomialSquareRoot
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic

/-!
# Polynomial square roots of invertible endomorphisms

Over an algebraically closed field of characteristic different from two, the
minimal polynomial of an automorphism has nonzero constant term. A square root
of `X` modulo that polynomial therefore gives a square root of the automorphism.

The root is a polynomial in the original operator. It commutes with its entire
centralizer and is self-adjoint for every bilinear form for which the original
operator is self-adjoint. Thus a single square root normalizes all those forms.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Polynomial

section PolynomialPreservation
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Polynomial evaluation preserves self-adjointness for a bilinear form. -/
theorem bilinear_selfAdjoint_aeval (B : LinearMap.BilinForm R M)
    (e : Module.End R M) (he : B.IsSelfAdjoint e) (p : R[X]) :
    B.IsSelfAdjoint (aeval e p) := by
  have hpow (n : ℕ) : B.IsSelfAdjoint (e ^ n : Module.End R M) := by
    induction n with
    | zero => exact LinearMap.isAdjointPair_one
    | succ n ih =>
      simpa only [LinearMap.IsSelfAdjoint, ← pow_succ, ← pow_succ'] using
        (LinearMap.IsAdjointPair.mul (f := e ^ n) (g := e ^ n) (f' := e) (g' := e) ih he)
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add]
      exact LinearMap.IsAdjointPair.add hp hq
  | monomial n c =>
      rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      exact LinearMap.IsAdjointPair.smul c (hpow n)

/-- Every operator commuting with `e` commutes with each polynomial in `e`. -/
theorem endomorphism_commute_aeval (e t : Module.End R M) (h : Commute t e)
    (p : R[X]) : Commute t (aeval e p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add]
      exact hp.add_right hq
  | monomial n c =>
      rw [aeval_monomial]
      exact (show Commute (algebraMap R (Module.End R M) c) t from
        Algebra.commutes c t).symm.mul_right (h.pow_right n)

end PolynomialPreservation

variable {K V : Type*} [Field K] [NeZero (2 : K)] [IsAlgClosed K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Every finite-dimensional automorphism has a square root polynomial in itself. -/
theorem exists_endomorphism_polynomial_square_root (e : V ≃ₗ[K] V) :
    ∃ p : K[X], (aeval (e : Module.End K V) p) ^ 2 = (e : Module.End K V) := by
  have hzero : (minpoly K (e : Module.End K V)).eval 0 ≠ 0 := by
    rw [← coeff_zero_eq_eval_zero]
    exact LinearMap.minpoly_coeff_zero_of_injective e.injective
  obtain ⟨p, d, hd⟩ := exists_polynomial_square_root_mod
    (minpoly K (e : Module.End K V)) hzero
  refine ⟨p, ?_⟩
  have h := congrArg (aeval (e : Module.End K V)) hd
  simp only [map_sub, aeval_X, map_pow, map_mul, minpoly.aeval, zero_mul] at h
  exact (sub_eq_zero.mp h).symm

/-- A polynomial square root of an automorphism is itself an automorphism. -/
theorem exists_polynomial_square_root_equiv (e : V ≃ₗ[K] V) :
    ∃ (s : V ≃ₗ[K] V) (p : K[X]),
      (s : Module.End K V) = aeval (e : Module.End K V) p ∧
      (s : Module.End K V) ^ 2 = (e : Module.End K V) := by
  obtain ⟨p, hp⟩ := exists_endomorphism_polynomial_square_root e
  let r := aeval (e : Module.End K V) p
  have hrr (x : V) : r (r x) = e x := by
    have h := congrArg (fun f : Module.End K V => f x) hp
    dsimp [r]
    simpa only [pow_two, Module.End.mul_apply, LinearEquiv.coe_coe] using h
  have hr : Function.Bijective r := by
    constructor
    · intro x y h
      apply e.injective
      rw [← hrr, ← hrr, h]
    · intro y
      exact ⟨r (e.symm y), by rw [hrr, e.apply_symm_apply]⟩
  exact ⟨LinearEquiv.ofBijective r hr, p, rfl, hp⟩

/-- One square root preserves every commuting operator and every compatible bilinear form.
For each such form, it identifies the twist `B(x,e y)` with `B` by congruence. -/
theorem exists_simultaneous_polynomial_square_root (e : V ≃ₗ[K] V) :
    ∃ s : V ≃ₗ[K] V,
      (s : Module.End K V) ^ 2 = (e : Module.End K V) ∧
      (∀ t : Module.End K V, Commute t (e : Module.End K V) →
        Commute t (s : Module.End K V)) ∧
      (∀ B : LinearMap.BilinForm K V, B.IsSelfAdjoint e →
        B.IsSelfAdjoint s ∧ ∀ x y, B (s x) (s y) = B x (e y)) := by
  obtain ⟨s, p, hsp, hs⟩ := exists_polynomial_square_root_equiv e
  refine ⟨s, hs, ?_, ?_⟩
  · intro t ht
    rw [hsp]
    exact endomorphism_commute_aeval (e : Module.End K V) t ht p
  · intro B hB
    have hBs : B.IsSelfAdjoint s := by
      change B.IsSelfAdjoint (s : Module.End K V)
      rw [hsp]
      exact bilinear_selfAdjoint_aeval B (e : Module.End K V) hB p
    refine ⟨hBs, fun x y => ?_⟩
    rw [hBs]
    have hss : s (s y) = e y := by
      have h := congrArg (fun f : Module.End K V => f y) hs
      simpa only [pow_two, Module.End.mul_apply, LinearEquiv.coe_coe] using h
    rw [hss]

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.exists_polynomial_square_root_equiv
#print axioms GaloisForLFunctions.HTGeometry.exists_simultaneous_polynomial_square_root
