import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Localization.InvSubmonoid
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Finite-type product specialization

This file gives the algebraic specialization step needed to descend a difference certificate from
the function field of a product to one factor.  A nonzero denominator in `A ⊗[C] R` has a nonzero
coefficient in a basis of the field `A`.  The Nullstellensatz supplies a `C`-point of the finite-
type domain `R` at which that coefficient survives.  Specializing the right factor therefore
preserves the denominator and converts a cross-multiplied rational coboundary identity into an
actual coboundary identity in `A`.
-/

open scoped nonZeroDivisors TensorProduct

namespace GaloisForLFunctions

noncomputable section

/-- A nonzero element of a finite-type domain over an algebraically closed field survives at some
rational point. -/
theorem exists_algHom_ne_zero_of_finiteType_domain
    (C R : Type*) [Field C] [IsAlgClosed C] [CommRing R] [IsDomain R]
    [Algebra C R] [Algebra.FiniteType C R] (d : R) (hd : d ≠ 0) :
    ∃ φ : R →ₐ[C] C, φ d ≠ 0 := by
  let S := Localization.Away d
  letI : Algebra C S := OreLocalization.instAlgebra
  letI : IsScalarTower C R S := OreLocalization.instIsScalarTower
  letI : IsDomain S := IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors hd)
  haveI : Algebra.FiniteType C S :=
    Algebra.FiniteType.trans (R := C) (S := R) (A := S) inferInstance inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal S
  letI : Field (S ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType C (S ⧸ m) := inferInstance
  have hfinite : Module.Finite C (S ⧸ m) :=
    finite_of_finite_type_of_isJacobsonRing C (S ⧸ m)
  letI : Module.Finite C (S ⧸ m) := hfinite
  haveI : Algebra.IsAlgebraic C (S ⧸ m) := Algebra.IsIntegral.isAlgebraic
  let ψ : (S ⧸ m) →ₐ[C] C := IsAlgClosed.lift
  let ι : R →ₐ[C] S := IsScalarTower.toAlgHom C R S
  let q : S →ₐ[C] (S ⧸ m) := Ideal.Quotient.mkₐ C m
  refine ⟨ψ.comp (q.comp ι), ?_⟩
  have hunitS : IsUnit (algebraMap R S d) :=
    IsLocalization.map_units S ⟨d, Submonoid.mem_powers d⟩
  have hunitQ : IsUnit (q (algebraMap R S d)) := hunitS.map q
  have hneQ : q (algebraMap R S d) ≠ 0 := hunitQ.ne_zero
  simpa [ι, q] using ψ.injective.ne hneQ

/-- Specialization of the right tensor factor along a `C`-point. -/
def tensorSpecialization
    (C A R : Type*) [CommSemiring C] [CommSemiring A] [CommSemiring R]
    [Algebra C A] [Algebra C R] (φ : R →ₐ[C] C) : (A ⊗[C] R) →ₐ[C] A :=
  Algebra.TensorProduct.lift (AlgHom.id C A) ((Algebra.ofId C A).comp φ)
    (fun _ _ => Commute.all _ _)

@[simp] theorem tensorSpecialization_tmul
    (C A R : Type*) [CommSemiring C] [CommSemiring A] [CommSemiring R]
    [Algebra C A] [Algebra C R] (φ : R →ₐ[C] C) (a : A) (r : R) :
    tensorSpecialization C A R φ (a ⊗ₜ[C] r) = a * algebraMap C A (φ r) := by
  rfl

/-- Every nonzero tensor denominator survives under some specialization of a finite-type domain
factor. -/
theorem exists_tensorSpecialization_ne_zero
    (C A R : Type*) [Field C] [IsAlgClosed C] [Field A] [CommRing R] [IsDomain R]
    [Algebra C A] [Algebra C R] [Algebra.FiniteType C R]
    (D : A ⊗[C] R) (hD : D ≠ 0) :
    ∃ φ : R →ₐ[C] C, tensorSpecialization C A R φ D ≠ 0 := by
  classical
  let B := Module.Free.chooseBasis C A
  let c : (Module.Free.ChooseBasisIndex C A) →₀ R :=
    TensorProduct.equivFinsuppOfBasisLeft B D
  have hc : c ≠ 0 := by
    intro hc0
    apply hD
    apply (TensorProduct.equivFinsuppOfBasisLeft B).injective
    simp [c, hc0]
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hc
  obtain ⟨φ, hφ⟩ := exists_algHom_ne_zero_of_finiteType_domain C R (c i) hi
  refine ⟨φ, ?_⟩
  intro hzero
  have hrepr : D = c.sum fun i r => B i ⊗ₜ[C] r := by
    simpa [c] using
      (TensorProduct.equivFinsuppOfBasisLeft_symm_apply B c)
  have hspec : tensorSpecialization C A R φ D =
      c.sum fun j r => (φ r) • B j := by
    rw [hrepr]
    simp [tensorSpecialization, Finsupp.sum, Algebra.smul_def, mul_comm]
  have hcoord := congr_arg (fun a : A => B.repr a i) hzero
  rw [hspec] at hcoord
  simp only [map_zero, Finsupp.zero_apply] at hcoord
  simp [Finsupp.sum, B] at hcoord
  have hiMem : i ∈ c.support := Finsupp.mem_support_iff.mpr hi
  apply hφ
  simpa [Finsupp.single_apply, hiMem] using hcoord

/-- The automorphism of a tensor product induced from the left factor. -/
def tensorLeftAction
    (C A R : Type*) [CommSemiring C] [CommSemiring A] [CommSemiring R]
    [Algebra C A] [Algebra C R] (σ : A ≃ₐ[C] A) : (A ⊗[C] R) →ₐ[C] (A ⊗[C] R) :=
  Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id C R)

@[simp] theorem tensorLeftAction_tmul
    (C A R : Type*) [CommSemiring C] [CommSemiring A] [CommSemiring R]
    [Algebra C A] [Algebra C R] (σ : A ≃ₐ[C] A) (a : A) (r : R) :
    tensorLeftAction C A R σ (a ⊗ₜ[C] r) = σ a ⊗ₜ[C] r := by
  simp [tensorLeftAction]

theorem tensorSpecialization_tensorLeftAction
    (C A R : Type*) [CommSemiring C] [CommSemiring A] [CommSemiring R]
    [Algebra C A] [Algebra C R] (σ : A ≃ₐ[C] A) (φ : R →ₐ[C] C)
    (x : A ⊗[C] R) :
    tensorSpecialization C A R φ (tensorLeftAction C A R σ x) =
      σ (tensorSpecialization C A R φ x) := by
  induction x with
  | zero => simp
  | tmul a r => simp [tensorSpecialization, tensorLeftAction]
  | add x y hx hy => simp [hx, hy]

/-- **Rational product-specialization descent.** If a rational certificate in a scalar-product
domain satisfies a first-order additive coboundary identity under an automorphism of the left
factor, then the identity already has a certificate in the left field. -/
theorem exists_left_coboundary_of_tensor_fraction_identity
    (C A R : Type*) [Field C] [IsAlgClosed C] [Field A] [CommRing R] [IsDomain R]
    [Algebra C A] [Algebra C R] [Algebra.FiniteType C R]
    (σ : A ≃ₐ[C] A) (a : A) (N D : A ⊗[C] R) (hD : D ≠ 0)
    (hidentity : tensorLeftAction C A R σ N * D -
        N * tensorLeftAction C A R σ D =
      (a ⊗ₜ[C] (1 : R)) * tensorLeftAction C A R σ D * D) :
    ∃ u : A, σ u - u = a := by
  obtain ⟨φ, hφD⟩ := exists_tensorSpecialization_ne_zero C A R D hD
  let sp := tensorSpecialization C A R φ
  let n := sp N
  let d := sp D
  have hd : d ≠ 0 := hφD
  have hσd : σ d ≠ 0 := by simpa using σ.injective.ne hd
  have hid : σ n * d - n * σ d = a * σ d * d := by
    simpa [sp, n, d, tensorSpecialization_tensorLeftAction,
      tensorSpecialization_tmul] using congr_arg sp hidentity
  refine ⟨n / d, ?_⟩
  rw [map_div₀]
  field_simp [hd, hσd]
  linear_combination hid

end

end GaloisForLFunctions
