import GaloisForLFunctions.HTGeometry.PaperNativeReesQuotient

/-!
# Linear initial-class maps into the native associated graded ring

Package the actual homogeneous Rees monomials as linear maps. The source
specialization kernel identifies their kernels with the next ideal power.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- The degree `n` initial class as a linear map on the actual ideal power. -/
def paperNativeReesInitialLinearMap (n : ℕ) :
    (I ^ n : Ideal R) →ₗ[R] PaperIdealAssociatedGraded I :=
  (paperNativeReesSpecialization I).toLinearMap.comp
    ({
      toFun := fun a => ReesGrading.mono I n a a.property
      map_add' := by
        intro a b
        apply Subtype.ext
        exact map_add (Polynomial.monomial n) (a : R) (b : R)
      map_smul' := by
        intro r a
        apply Subtype.ext
        exact (Polynomial.smul_monomial r n (a : R)).symm } :
      (I ^ n : Ideal R) →ₗ[R] reesAlgebra I)

/-- This linear map uses the native monomial and the actual source specialization. -/
theorem paperNativeReesInitialLinearMap_apply (n : ℕ) (a : (I ^ n : Ideal R)) :
    paperNativeReesInitialLinearMap I n a =
      paperNativeReesSpecialization I (ReesGrading.mono I n a a.property) := rfl

/-- A homogeneous initial class vanishes exactly at the next ideal power. -/
theorem paperNativeReesInitialLinearMap_eq_zero_iff (n : ℕ) (a : (I ^ n : Ideal R)) :
    paperNativeReesInitialLinearMap I n a = 0 ↔ (a : R) ∈ I ^ (n + 1) :=
  paperNativeReesSpecialization_mono_eq_zero_iff I n a

end

end GaloisForLFunctions.HTGeometry
