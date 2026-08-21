import GaloisForLFunctions.HTGeometry.CoLieKaehler
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# The co-Lie complex of an affine group scheme

For an affine group scheme `Spec A` over `R` and a presentation `A = P/J`, the naive cotangent
complex of `A/R` is `J/J² → A ⊗_P Ω[P⁄R]`, with cokernel `Ω[A⁄R]` (mathlib's
`Algebra.Extension.cotangentComplex` and `Algebra.Extension.exact_cotangentComplex_toKaehler`).

The **co-Lie complex** `ℓ_A` of the group scheme is this complex pulled back along the identity
section, i.e. base changed along `A → A / I`.  This file constructs it and proves

`H⁰(ℓ_A) ≅ ω_A = I / I²`,

by right-exactness of the tensor product together with `coLieEquivKaehlerQuotient`.

This is the degree-zero part of Illusie's `RLie`; Proposition 2.1 of Suzuki, *Duality invariance of
Faltings heights, Hodge line bundles and global periods* (arXiv:2504.04993) is a statement about
the determinant of the full complex.
-/

namespace GaloisForLFunctions.HTGeometry.AffineGroupScheme

open Coalgebra Bialgebra Ideal TensorProduct

variable {R A : Type*} [CommRing R] [CommRing A] [Bialgebra R A]

/-- The structure sheaf of the identity section, `A / I`. -/
abbrev identityFibre (R A : Type*) [CommRing R] [CommRing A] [Bialgebra R A] : Type _ :=
  A ⧸ augIdeal R A

/-- **The co-Lie complex** of the group scheme `Spec A`: the naive cotangent complex of `A / R`
base changed along the identity section. -/
noncomputable def coLieComplex (P : Algebra.Extension R A) :
    (P.Cotangent ⊗[A] identityFibre R A) →ₗ[A] (P.CotangentSpace ⊗[A] identityFibre R A) :=
  LinearMap.rTensor _ P.cotangentComplex

/-- The augmentation of the co-Lie complex onto `Ω[A⁄R] ⊗ A/I`. -/
noncomputable def coLieComplexToKaehler (P : Algebra.Extension R A) :
    (P.CotangentSpace ⊗[A] identityFibre R A) →ₗ[A] (Ω[A⁄R] ⊗[A] identityFibre R A) :=
  LinearMap.rTensor _ P.toKaehler

theorem exact_coLieComplex (P : Algebra.Extension R A) :
    Function.Exact (coLieComplex P) (coLieComplexToKaehler P) :=
  rTensor_exact _ Algebra.Extension.exact_cotangentComplex_toKaehler
    Algebra.Extension.toKaehler_surjective

theorem surjective_coLieComplexToKaehler (P : Algebra.Extension R A) :
    Function.Surjective (coLieComplexToKaehler P) :=
  LinearMap.rTensor_surjective _ Algebra.Extension.toKaehler_surjective

/-- **`H⁰` of the co-Lie complex is the co-Lie module.** -/
noncomputable def h0CoLieComplexEquiv :
    (Ω[A⁄R] ⊗[A] identityFibre R A) ≃ₗ[A] coLie R A :=
  (TensorProduct.comm A (Ω[A⁄R]) (identityFibre R A)) ≪≫ₗ
    (quotTensorEquivQuotSMul (Ω[A⁄R]) (augIdeal R A)) ≪≫ₗ
    (coLieEquivKaehlerQuotient (R := R) (A := A)).symm

/-- **The co-Lie complex is exact at its middle term, with cokernel `ω_A`.** -/
theorem coLieComplex_exact_h0 (P : Algebra.Extension R A) :
    Function.Exact (coLieComplex P)
      (fun x => h0CoLieComplexEquiv (R := R) (A := A) (coLieComplexToKaehler P x)) :=
  Function.Exact.comp_injective _ (exact_coLieComplex P)
    (h0CoLieComplexEquiv (R := R) (A := A)).injective (map_zero _)

theorem coLieComplex_surjective_h0 (P : Algebra.Extension R A) :
    Function.Surjective
      (fun x => h0CoLieComplexEquiv (R := R) (A := A) (coLieComplexToKaehler P x)) :=
  (h0CoLieComplexEquiv (R := R) (A := A)).surjective.comp (surjective_coLieComplexToKaehler P)

end GaloisForLFunctions.HTGeometry.AffineGroupScheme
