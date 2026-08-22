import GaloisForLFunctions.HTGeometry.ABHN.TwoPrincipalOpenGenericFiber
import GaloisForLFunctions.HTGeometry.ABHN.TwoPrincipalOpenFractionFieldMap

/-!
# Final-localization generic-fiber compatibility

An explicit commuting map to a common field supplies the scalar-tower instance needed to cancel
the last base change in a two-principal Azumaya model.  Applied to the canonical fraction-field
maps, this keeps the final finite-residue model attached to its original central simple algebra.
No completed-local-field or Brauer comparison is asserted here.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

noncomputable section

/-- A commuting final scalar-extension map gives the prescribed generic fiber of a two-principal
model. -/
noncomputable def twoPrincipalOpen_scalarExtension_genericFiber_equiv_of_map_commutes
    {R S U T K O A : Type*}
    [CommRing R] [CommRing S] [CommRing U] [CommRing T] [CommRing K]
    [Algebra R S] [Algebra S U] [Algebra U T]
    [Algebra R K] [Algebra S K] [Algebra U K] [Algebra T K]
    [IsScalarTower R S K] [IsScalarTower S U K]
    [Ring O] [Algebra R O] [Ring A] [Algebra K A]
    (hUTK : (algebraMap T K).comp (algebraMap U T) = algebraMap U K)
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
  letI : IsScalarTower U T K := IsScalarTower.of_algebraMap_eq' hUTK.symm
  exact twoPrincipalOpen_scalarExtension_genericFiber_equiv_of_base_equiv
    (R := R) (S := S) (U := U) (T := T) (K := K) (O := O) e

end

end GaloisForLFunctions.HTGeometry.ABHN
