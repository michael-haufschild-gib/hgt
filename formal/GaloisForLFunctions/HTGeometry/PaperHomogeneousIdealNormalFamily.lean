import GaloisForLFunctions.HTGeometry.PaperHomogeneousNormalRelations

/-!
# Polynomial families of normal directions

The paper's coefficient-kernel and nonnegative-weight results preserve a whole
polynomially independent family of generators in the associated graded ring.
Concrete applications provide every field of the data below.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

/-- Fully paid data for simultaneous homogeneous normal directions. -/
structure PaperHomogeneousNormalFamilyData (K σ ι : Type*) [CommRing K]
    (I : Ideal (MvPolynomial σ K)) where
  generator : ι → MvPolynomial σ K
  degree : ℕ
  degree_pos : 0 < degree
  generator_mem : ∀ i, generator i ∈ I
  homogeneous : ∀ i, (generator i).IsHomogeneous degree
  independent : Function.Injective (MvPolynomial.aeval (R := K) generator)
  order_bound : I ≤ paperWeightOrderIdeal (fun _ : σ => (1 : ℤ)) (by intro _; exact zero_le_one) degree

variable {K σ ι : Type*} [CommRing K] {I : Ideal (MvPolynomial σ K)}

/-- An independent normal family is a special case of the general relation-preserving presentation. -/
def PaperHomogeneousNormalFamilyData.toPresentationData
    (D : PaperHomogeneousNormalFamilyData K σ ι I) :
    PaperHomogeneousNormalPresentationData K σ ι I where
  generator := D.generator
  degree := D.degree
  degree_pos := D.degree_pos
  generator_mem := D.generator_mem
  homogeneous := D.homogeneous
  order_bound := D.order_bound

/-- The generator family as actual members of the native ideal. -/
def PaperHomogeneousNormalFamilyData.idealElements (D : PaperHomogeneousNormalFamilyData K σ ι I) :
    ι → I := fun i => ⟨D.generator i, D.generator_mem i⟩

/-- Polynomial substitution into all normal directions at once. -/
def PaperHomogeneousNormalFamilyData.polynomialMap (D : PaperHomogeneousNormalFamilyData K σ ι I) :
    MvPolynomial ι K →+* PaperIdealAssociatedGraded I :=
  paperNativeReesMvPolynomialSpecialization I D.idealElements

/-- A homogeneous relation cannot gain one ideal order unless it is the zero polynomial. -/
theorem PaperHomogeneousNormalFamilyData.homogeneous_mem_succ_iff
    (D : PaperHomogeneousNormalFamilyData K σ ι I)
    (p : MvPolynomial ι K) (n : ℕ) (hp : p.IsHomogeneous n) :
    MvPolynomial.aeval D.generator p ∈ I ^ (n + 1) ↔ p = 0 := by
  exact (D.toPresentationData.homogeneous_mem_succ_iff p n hp).trans
    ⟨fun h => D.independent (by simpa only [toPresentationData, map_zero] using h),
      fun h => by rw [h, map_zero]⟩

/-- The multivariable normal map has zero kernel, by the source coefficient-kernel test. -/
theorem PaperHomogeneousNormalFamilyData.polynomialMap_eq_zero_iff
    (D : PaperHomogeneousNormalFamilyData K σ ι I) (p : MvPolynomial ι K) :
    D.polynomialMap p = 0 ↔ p = 0 :=
  (D.toPresentationData.polynomialMap_eq_zero_iff p).trans
    ⟨fun h => D.independent (by simpa only [toPresentationData, map_zero] using h),
      fun h => by rw [h, map_zero]⟩

/-- All polynomial relations between these normal directions are trivial. -/
theorem PaperHomogeneousNormalFamilyData.polynomialMap_injective
    (D : PaperHomogeneousNormalFamilyData K σ ι I) : Function.Injective D.polynomialMap := by
  intro p q h
  apply sub_eq_zero.mp
  apply (D.polynomialMap_eq_zero_iff (p - q)).mp
  rw [map_sub, h, sub_self]

/-- The map uses each generator's actual initial class in degree one. -/
theorem PaperHomogeneousNormalFamilyData.polynomialMap_X
    (D : PaperHomogeneousNormalFamilyData K σ ι I) (i : ι) :
    D.polynomialMap (MvPolynomial.X i : MvPolynomial ι K) =
      paperNativeReesSpecialization I
        (ReesGrading.mono I 1 (D.generator i) (by simpa only [pow_one] using D.generator_mem i)) :=
  paperNativeReesMvPolynomialSpecialization_X I D.idealElements i

end

end GaloisForLFunctions.HTGeometry
