import GaloisForLFunctions.HTGeometry.FreeParameterBaseChange
import GaloisForLFunctions.HTGeometry.CenteredSplittingField
import GaloisForLFunctions.HTGeometry.CenteredGenericGalois
import GaloisForLFunctions.HTGeometry.GenericPolynomialSeparable
import GaloisForLFunctions.HTGeometry.RootFieldTransport

/-!
# The centered generic polynomial keeps its symmetric group over a free parameter

The centered generic polynomial is separable and its splitting field is the centered field, so
adjoining a free parameter to its coefficient field does not change its Galois group.

So over the coefficient field extended by one independent transcendental — the field the fiber
equation of the rank-one horizon cover is written over — the Galois group is still the full
symmetric group.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}

/-- **The centered generic polynomial is separable over its coefficient field.** -/
theorem separable_centeredMonicE : (centeredMonicE K d).Separable := by
  rw [← Polynomial.separable_map
    (algebraMap (centeredCoeffField K d) (centeredField K d)), map_centeredMonicE]
  exact separable_centeredMonicL

/-- **The Galois group of the centered generic polynomial survives a free parameter.**  Over the
rational functions in one variable above its coefficient field, the centered generic polynomial of
degree `d` still has the full symmetric group on `d` letters. -/
noncomputable def centeredFreeParameterMonodromy (K : Type*) [Field K] [CharZero K] (d : ℕ) :
    (FractionRing (Polynomial (centeredField K d)) ≃ₐ[
        fracSub (centeredCoeffField K d) (centeredField K d)]
      FractionRing (Polynomial (centeredField K d))) ≃* Equiv.Perm (Fin d) :=
  freeParameterPermEquiv (F := centeredCoeffField K d) (E := centeredField K d)
    (p := centeredMonicE K d) centeredMonicE_ne_zero separable_centeredMonicE
    splits_centeredMonicE rootField_centeredMonicE_eq_top (centeredGaloisEquiv K d).symm

/-- **The rank-one boundary case of degree two.**  At tail length one the parameter change is the
identity, so no radical base change is needed: the fiber equation is a centered quadratic over its
coefficient field extended by one free parameter, and its Galois group is the symmetric group on two
letters. -/
noncomputable def quadraticParameterMonodromy (K : Type*) [Field K] [CharZero K] :
    (FractionRing (Polynomial (centeredField K 2)) ≃ₐ[
        fracSub (centeredCoeffField K 2) (centeredField K 2)]
      FractionRing (Polynomial (centeredField K 2))) ≃* Equiv.Perm (Fin 2) :=
  centeredFreeParameterMonodromy K 2

end GaloisForLFunctions.HTGeometry
