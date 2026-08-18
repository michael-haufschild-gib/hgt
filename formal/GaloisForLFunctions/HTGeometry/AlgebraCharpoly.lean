import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Cayley–Hamilton for a finite free algebra

Every element of a finite free algebra satisfies the monic characteristic polynomial of
multiplication by it.  This supplies the monic relation the chart data of
`AlgebraSpectrumCovering` asks for, with the right degree.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- The characteristic polynomial of multiplication by an element of a finite free algebra. -/
noncomputable def algCharpoly (A : Type*) {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B] (θ : B) : A[X] :=
  (Algebra.lmul A B θ).charpoly

theorem algCharpoly_monic (A : Type*) {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B] [Nontrivial A] (θ : B) :
    (algCharpoly A θ).Monic :=
  LinearMap.charpoly_monic _

/-- **Cayley–Hamilton for a finite free algebra.** -/
theorem aeval_algCharpoly (A : Type*) {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B] (θ : B) :
    Polynomial.aeval θ (algCharpoly A θ) = 0 := by
  have h : Polynomial.aeval (Algebra.lmul A B θ) (algCharpoly A θ) = 0 :=
    LinearMap.aeval_self_charpoly (Algebra.lmul A B θ)
  have h2 : Polynomial.aeval (Algebra.lmul A B θ) (algCharpoly A θ) =
      Algebra.lmul A B (Polynomial.aeval θ (algCharpoly A θ)) := by
    rw [Polynomial.aeval_algHom_apply]
  rw [h2] at h
  have h3 := congrArg (fun f : B →ₗ[A] B => f 1) h
  simpa using h3

/-- The characteristic polynomial has degree the rank. -/
theorem algCharpoly_natDegree (A : Type*) {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B] [Nontrivial A] {n : ℕ}
    (e : Module.Basis (Fin n) A B) (θ : B) :
    (algCharpoly A θ).natDegree = n := by
  rw [algCharpoly, LinearMap.charpoly_natDegree, Module.finrank_eq_card_basis e]
  simp


end GaloisForLFunctions.HTGeometry
