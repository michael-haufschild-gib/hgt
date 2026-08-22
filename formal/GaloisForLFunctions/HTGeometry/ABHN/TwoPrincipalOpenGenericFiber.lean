/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.AzumayaEnvelopeBaseChange

/-!
# Generic fibers of two-principal Azumaya models

The Azumaya model used for finite residue support is obtained by three successive scalar
extensions. This file proves that all three extensions cancel after passing to any common generic
field. It supplies the algebraic provenance needed before a completed-local-field or
Connes/Tate specialization can compare the model with a source-side local algebra.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

noncomputable section

/-- The generic fiber of a two-principal scalar-extension model is the generic fiber of its
original order. The hypotheses deliberately expose the compatible maps to the common field: a
future local-completion comparison must prove exactly these tower compatibilities. -/
noncomputable def twoPrincipalOpen_scalarExtension_genericFiber_equiv
    {R S U T K O : Type*}
    [CommRing R] [CommRing S] [CommRing U] [CommRing T] [CommRing K]
    [Algebra R S] [Algebra S U] [Algebra U T]
    [Algebra R K] [Algebra S K] [Algebra U K] [Algebra T K]
    [IsScalarTower R S K] [IsScalarTower S U K] [IsScalarTower U T K]
    [Ring O] [Algebra R O] :
    letI : Semiring (S ⊗[R] O) :=
      Algebra.TensorProduct.instSemiring (R := R) (A := S) (B := O)
    letI : Semiring (U ⊗[S] (S ⊗[R] O)) :=
      Algebra.TensorProduct.instSemiring (R := S) (A := U) (B := S ⊗[R] O)
    letI : Semiring (T ⊗[U] (U ⊗[S] (S ⊗[R] O))) :=
      Algebra.TensorProduct.instSemiring (R := U) (A := T) (B := U ⊗[S] (S ⊗[R] O))
    letI : Semiring (K ⊗[T] (T ⊗[U] (U ⊗[S] (S ⊗[R] O)))) :=
      Algebra.TensorProduct.instSemiring (R := T) (A := K)
        (B := T ⊗[U] (U ⊗[S] (S ⊗[R] O)))
    letI : Algebra K (K ⊗[T] (T ⊗[U] (U ⊗[S] (S ⊗[R] O)))) :=
      Algebra.TensorProduct.leftAlgebra (R := T) (S := K) (A := K)
        (B := T ⊗[U] (U ⊗[S] (S ⊗[R] O)))
    K ⊗[T] (T ⊗[U] (U ⊗[S] (S ⊗[R] O))) ≃ₐ[K] K ⊗[R] O := by
  letI : Semiring (S ⊗[R] O) :=
    Algebra.TensorProduct.instSemiring (R := R) (A := S) (B := O)
  letI : Semiring (U ⊗[S] (S ⊗[R] O)) :=
    Algebra.TensorProduct.instSemiring (R := S) (A := U) (B := S ⊗[R] O)
  letI : Semiring (T ⊗[U] (U ⊗[S] (S ⊗[R] O))) :=
    Algebra.TensorProduct.instSemiring (R := U) (A := T) (B := U ⊗[S] (S ⊗[R] O))
  letI : Semiring (K ⊗[T] (T ⊗[U] (U ⊗[S] (S ⊗[R] O)))) :=
    Algebra.TensorProduct.instSemiring (R := T) (A := K)
      (B := T ⊗[U] (U ⊗[S] (S ⊗[R] O)))
  letI : Algebra K (K ⊗[T] (T ⊗[U] (U ⊗[S] (S ⊗[R] O)))) :=
    Algebra.TensorProduct.leftAlgebra (R := T) (S := K) (A := K)
      (B := T ⊗[U] (U ⊗[S] (S ⊗[R] O)))
  exact (AzumayaScalarExtension.cancelBaseChangeNoncommutative
    (R := U) (S := T) (A := U ⊗[S] (S ⊗[R] O)) (T := K)).trans
      ((AzumayaScalarExtension.cancelBaseChangeNoncommutative
        (R := S) (S := U) (A := S ⊗[R] O) (T := K)).trans
          (AzumayaScalarExtension.cancelBaseChangeNoncommutative
            (R := R) (S := S) (A := O) (T := K)))

/-- A two-principal Azumaya model has the prescribed generic algebra whenever the original
order does. This is the form consumed by a future local-place comparison. -/
noncomputable def twoPrincipalOpen_scalarExtension_genericFiber_equiv_of_base_equiv
    {R S U T K O A : Type*}
    [CommRing R] [CommRing S] [CommRing U] [CommRing T] [CommRing K]
    [Algebra R S] [Algebra S U] [Algebra U T]
    [Algebra R K] [Algebra S K] [Algebra U K] [Algebra T K]
    [IsScalarTower R S K] [IsScalarTower S U K] [IsScalarTower U T K]
    [Ring O] [Algebra R O] [Ring A] [Algebra K A]
    (e : K ⊗[R] O ≃ₐ[K] A) :
    letI : Semiring (S ⊗[R] O) :=
      Algebra.TensorProduct.instSemiring (R := R) (A := S) (B := O)
    letI : Semiring (U ⊗[S] (S ⊗[R] O)) :=
      Algebra.TensorProduct.instSemiring (R := S) (A := U) (B := S ⊗[R] O)
    letI : Semiring (T ⊗[U] (U ⊗[S] (S ⊗[R] O))) :=
      Algebra.TensorProduct.instSemiring (R := U) (A := T) (B := U ⊗[S] (S ⊗[R] O))
    letI : Semiring (K ⊗[T] (T ⊗[U] (U ⊗[S] (S ⊗[R] O)))) :=
      Algebra.TensorProduct.instSemiring (R := T) (A := K)
        (B := T ⊗[U] (U ⊗[S] (S ⊗[R] O)))
    letI : Algebra K (K ⊗[T] (T ⊗[U] (U ⊗[S] (S ⊗[R] O)))) :=
      Algebra.TensorProduct.leftAlgebra (R := T) (S := K) (A := K)
        (B := T ⊗[U] (U ⊗[S] (S ⊗[R] O)))
    K ⊗[T] (T ⊗[U] (U ⊗[S] (S ⊗[R] O))) ≃ₐ[K] A := by
  letI : Semiring (S ⊗[R] O) :=
    Algebra.TensorProduct.instSemiring (R := R) (A := S) (B := O)
  letI : Semiring (U ⊗[S] (S ⊗[R] O)) :=
    Algebra.TensorProduct.instSemiring (R := S) (A := U) (B := S ⊗[R] O)
  letI : Semiring (T ⊗[U] (U ⊗[S] (S ⊗[R] O))) :=
    Algebra.TensorProduct.instSemiring (R := U) (A := T) (B := U ⊗[S] (S ⊗[R] O))
  letI : Semiring (K ⊗[T] (T ⊗[U] (U ⊗[S] (S ⊗[R] O)))) :=
    Algebra.TensorProduct.instSemiring (R := T) (A := K)
      (B := T ⊗[U] (U ⊗[S] (S ⊗[R] O)))
  letI : Algebra K (K ⊗[T] (T ⊗[U] (U ⊗[S] (S ⊗[R] O)))) :=
    Algebra.TensorProduct.leftAlgebra (R := T) (S := K) (A := K)
      (B := T ⊗[U] (U ⊗[S] (S ⊗[R] O)))
  exact (twoPrincipalOpen_scalarExtension_genericFiber_equiv
    (R := R) (S := S) (U := U) (T := T) (K := K) (O := O)).trans e

end

end GaloisForLFunctions.HTGeometry.ABHN
