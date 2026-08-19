import GaloisForLFunctions.HTGeometry.DifferencePicardVessiotQuotient

/-!
# The difference action on a localization away from a semi-invariant element

The coordinate ring of a fundamental matrix has to be localized at the determinant before it can
carry a Picard--Vessiot ideal, so the distinguished automorphism has to be extended to that
localization.  The extension exists whenever the image of the inverted element is again invertible
there, which for the determinant of a fundamental matrix is the statement that the system matrix is
invertible.

The construction is by the universal property, and the inverse is the same construction for the
inverse automorphism, so the extension is an automorphism with an explicit two-sided inverse.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]

/-- The difference action extended to a localization away from an element whose image is again
invertible there. -/
def sigmaAwayHom (σ : R ≃+* R) (d : R) [IsLocalization.Away d S]
    (hd : IsUnit (algebraMap R S (σ d))) : S →+* S :=
  IsLocalization.lift (M := Submonoid.powers d)
    (g := (algebraMap R S).comp (σ : R →+* R))
    (by
      rintro ⟨y, k, rfl⟩
      have : ((algebraMap R S).comp (σ : R →+* R)) (d ^ k) = (algebraMap R S (σ d)) ^ k := by
        simp [RingHom.comp_apply]
      rw [this]
      exact hd.pow k)

@[simp] theorem sigmaAwayHom_algebraMap (σ : R ≃+* R) (d : R) [IsLocalization.Away d S]
    (hd : IsUnit (algebraMap R S (σ d))) (x : R) :
    sigmaAwayHom (S := S) σ d hd (algebraMap R S x) = algebraMap R S (σ x) :=
  IsLocalization.lift_eq _ x

/-- **The extension is an automorphism.**  Its inverse is the extension of the inverse
automorphism. -/
def sigmaAwayEquiv (σ : R ≃+* R) (d : R) [IsLocalization.Away d S]
    (hd : IsUnit (algebraMap R S (σ d))) (hd' : IsUnit (algebraMap R S (σ.symm d))) :
    S ≃+* S :=
  RingEquiv.ofRingHom (sigmaAwayHom (S := S) σ d hd) (sigmaAwayHom (S := S) σ.symm d hd')
    (by
      refine IsLocalization.ringHom_ext (Submonoid.powers d) ?_
      ext x
      simp [RingHom.comp_apply])
    (by
      refine IsLocalization.ringHom_ext (Submonoid.powers d) ?_
      ext x
      simp [RingHom.comp_apply])

@[simp] theorem sigmaAwayEquiv_apply (σ : R ≃+* R) (d : R) [IsLocalization.Away d S]
    (hd : IsUnit (algebraMap R S (σ d))) (hd' : IsUnit (algebraMap R S (σ.symm d))) (x : S) :
    sigmaAwayEquiv (S := S) σ d hd hd' x = sigmaAwayHom (S := S) σ d hd x := rfl

@[simp] theorem sigmaAwayEquiv_algebraMap (σ : R ≃+* R) (d : R) [IsLocalization.Away d S]
    (hd : IsUnit (algebraMap R S (σ d))) (hd' : IsUnit (algebraMap R S (σ.symm d))) (x : R) :
    sigmaAwayEquiv (S := S) σ d hd hd' (algebraMap R S x) = algebraMap R S (σ x) :=
  IsLocalization.lift_eq _ x

end

end GaloisForLFunctions.HTGeometry
