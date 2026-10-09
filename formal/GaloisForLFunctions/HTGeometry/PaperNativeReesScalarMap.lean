import GaloisForLFunctions.HTGeometry.PaperNativeReesMvPolynomial

/-!
# Scalar-compatible native Rees specialization

The source initial-class substitution is a base-algebra homomorphism. This
lets native coefficient algebras and entire polynomial families enter the
actual normal ring with their original scalar structure.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K R ι : Type*} [CommRing K] [CommRing R] [Algebra K R]
variable (I : Ideal R) (c : ι → I)

/-- The actual source initial-class substitution preserves the base coefficient map. -/
theorem paperNativeReesMvPolynomialSpecialization_C (r : K) :
    paperNativeReesMvPolynomialSpecialization I c (MvPolynomial.C r) =
      algebraMap K (PaperIdealAssociatedGraded I) r := by
  change paperNativeReesSpecialization I
    (MvPolynomial.eval₂Hom ((algebraMap R (reesAlgebra I)).comp (algebraMap K R))
      (fun i => ReesGrading.mono I 1 (c i)
        (by simpa only [pow_one] using (c i).property)) (MvPolynomial.C r)) = _
  rw [MvPolynomial.eval₂Hom_C]
  change paperNativeReesSpecialization I (algebraMap R (reesAlgebra I) (algebraMap K R r)) = _
  rw [AlgHom.commutes]
  exact (IsScalarTower.algebraMap_apply K R (PaperIdealAssociatedGraded I) r).symm

/-- The native polynomial initial-class map with its proved base-algebra structure. -/
def paperNativeReesMvPolynomialAlgHom :
    MvPolynomial ι K →ₐ[K] PaperIdealAssociatedGraded I where
  __ := paperNativeReesMvPolynomialSpecialization I c
  commutes' := paperNativeReesMvPolynomialSpecialization_C I c

/-- The scalar-compatible map is exactly the original source specialization. -/
theorem paperNativeReesMvPolynomialAlgHom_apply (p : MvPolynomial ι K) :
    paperNativeReesMvPolynomialAlgHom I c p =
      paperNativeReesMvPolynomialSpecialization I c p := rfl

end

end GaloisForLFunctions.HTGeometry
