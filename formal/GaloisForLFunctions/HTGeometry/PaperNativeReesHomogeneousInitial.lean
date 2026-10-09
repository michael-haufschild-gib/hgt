import GaloisForLFunctions.HTGeometry.PaperHomogeneousNormalRelations

/-!
# Actual initial classes of homogeneous polynomial expressions

The source weighted Laurent map computes homogeneous Rees expressions exactly.
This interface derives ideal-power membership and identifies their actual initial
classes, for subsequent native invariant and discriminant applications.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K R ι : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (I : Ideal R) (c : ι → I)

/-- A homogeneous degree-`n` expression in ideal elements belongs to the actual `n`th power. -/
theorem paperNativeReesMvPolynomial_homogeneous_mem
    (p : MvPolynomial ι K) (n : ℕ) (hp : p.IsHomogeneous n) :
    MvPolynomial.aeval (fun i => (c i : R)) p ∈ I ^ n := by
  have h := (paperNativeReesMvPolynomialMap I c p).property n
  change (paperNativeReesMvPolynomialMap I c p : Polynomial R).coeff n ∈ I ^ n at h
  rw [paperNativeReesMvPolynomialMap_homogeneous I c p n hp] at h
  simpa using h

/-- Source specialization of a homogeneous expression is its actual native initial class. -/
theorem paperNativeReesMvPolynomialSpecialization_homogeneous
    (p : MvPolynomial ι K) (n : ℕ) (hp : p.IsHomogeneous n) :
    paperNativeReesMvPolynomialSpecialization I c p =
      paperNativeReesSpecialization I (ReesGrading.mono I n
        (MvPolynomial.aeval (fun i => (c i : R)) p)
        (paperNativeReesMvPolynomial_homogeneous_mem I c p n hp)) := by
  apply congrArg (paperNativeReesSpecialization I)
  apply Subtype.ext
  exact paperNativeReesMvPolynomialMap_homogeneous I c p n hp

variable {σ : Type*} {J : Ideal (MvPolynomial σ K)}

/-- Membership interface for native homogeneous presentations. -/
theorem PaperHomogeneousNormalPresentationData.homogeneous_evaluation_mem
    (D : PaperHomogeneousNormalPresentationData K σ ι J)
    (p : MvPolynomial ι K) (n : ℕ) (hp : p.IsHomogeneous n) :
    MvPolynomial.aeval D.generator p ∈ J ^ n :=
  paperNativeReesMvPolynomial_homogeneous_mem J D.idealElements p n hp

/-- Every homogeneous presentation expression maps to its actual initial class. -/
theorem PaperHomogeneousNormalPresentationData.polynomialMap_homogeneous
    (D : PaperHomogeneousNormalPresentationData K σ ι J)
    (p : MvPolynomial ι K) (n : ℕ) (hp : p.IsHomogeneous n) :
    D.polynomialMap p = paperNativeReesSpecialization J
      (ReesGrading.mono J n (MvPolynomial.aeval D.generator p)
        (D.homogeneous_evaluation_mem p n hp)) :=
  paperNativeReesMvPolynomialSpecialization_homogeneous J D.idealElements p n hp

end

end GaloisForLFunctions.HTGeometry
