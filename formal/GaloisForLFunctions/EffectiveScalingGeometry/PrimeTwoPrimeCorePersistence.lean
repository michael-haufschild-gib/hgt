import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeLowerCoreHomology
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeBlockPersistence

/-! The lower and upper quotient comparisons preserve original height maps.
Core ranges are invariant under actual homology persistence, and extraction
keeps each scalar cycle coordinate while the boundary relations grow. -/

noncomputable section
open scoped Classical
open CategoryTheory RHTower DifferentialGeometry.Topology
namespace GaloisForLFunctions.EffectiveScalingGeometry
variable (R : Type*) [CommRing R]

/-- The original height map restricts to every actual core homology summand. -/
def twoPrimeHomologyCoreMap (k : ℕ) (c : TwoPrimeCoreFace) {N M : ℕ} (h : N ≤ M) :
    TwoPrimeHomologyCore R k N c →ₗ[R] TwoPrimeHomologyCore R k M c where
  toFun x := ⟨(primeCutoffHomology R (primeValueFunctional R) k).map (homOfLE h) x.val,by
    obtain ⟨y,hy⟩ := x.property
    refine ⟨(primeCutoffHomology R (primeValueFunctional R) k).map (homOfLE h) y,?_⟩
    have he := congrArg (fun f :
        (primeCutoffHomology R (primeValueFunctional R) k).obj N ⟶
          (primeCutoffHomology R (primeValueFunctional R) k).obj M => f y)
      ((twoPrimeCoreHomologyProjectionNat R k c).naturality (homOfLE h))
    change twoPrimeCoreHomologyProjection R k M c
      ((primeCutoffHomology R (primeValueFunctional R) k).map (homOfLE h) y) =
      (primeCutoffHomology R (primeValueFunctional R) k).map (homOfLE h)
        (twoPrimeCoreHomologyProjection R k N c y) at he
    exact he.trans (congrArg
      ((primeCutoffHomology R (primeValueFunctional R) k).map (homOfLE h)) hy)⟩
  map_add' x y := Subtype.ext
    (((primeCutoffHomology R (primeValueFunctional R) k).map (homOfLE h)).hom.map_add x.val y.val)
  map_smul' a x := Subtype.ext
    (((primeCutoffHomology R (primeValueFunctional R) k).map (homOfLE h)).hom.map_smul a x.val)

/-- The original height map retains the extracted upper block class. -/
theorem twoPrimeUpperHomologyExtraction_natural (c : TwoPrimeCoreFace) {N M : ℕ} (h : N ≤ M)
    (x : (primeCutoffComplex R (primeValueFunctional R) N).homology (c.val.card+1)) :
    twoPrimeUpperHomologyExtraction R c M
      ((primeCutoffHomology R (primeValueFunctional R) (c.val.card+1)).map (homOfLE h) x) =
      ShortComplex.homologyMap (twoPrimeUpperBlockInclusion R (twoPrimeCoreHeight c) h)
        (twoPrimeUpperHomologyExtraction R c N x) := by
  obtain ⟨z,rfl⟩ := moduleHomologyClass_surjective
    ((primeCutoffComplex R (primeValueFunctional R) N).sc (c.val.card+1)) x
  change ShortComplex.homologyMap (twoPrimeUpperOriginalRetraction R c M)
    (ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.down ℕ) (c.val.card+1)).map
        (primeCutoffInclusion R (primeValueFunctional R) h)) _) =
      ShortComplex.homologyMap (twoPrimeUpperBlockInclusion R (twoPrimeCoreHeight c) h)
        (ShortComplex.homologyMap (twoPrimeUpperOriginalRetraction R c N) _)
  rw [moduleHomologyClass_map,moduleHomologyClass_map,moduleHomologyClass_map,moduleHomologyClass_map]
  apply congrArg (moduleHomologyClass (twoPrimeUpperBlock R (twoPrimeCoreHeight c) M))
  apply Subtype.ext
  rfl

/-- The actual upper core quotient comparison preserves every original height map. -/
theorem twoPrimeUpperCoreCoefficientEquiv_natural (c : TwoPrimeCoreFace) {N M : ℕ} (h : N ≤ M)
    (x : TwoPrimeHomologyCore R (c.val.card+1) N c) :
    twoPrimeUpperCoreCoefficientEquiv R c M (twoPrimeHomologyCoreMap R (c.val.card+1) c h x) =
      twoPrimeUpperHomologyMap R (twoPrimeCoreHeight c) h
        (twoPrimeUpperCoreCoefficientEquiv R c N x) := by
  change twoPrimeUpperHomologyEquiv R (twoPrimeCoreHeight c) M
    (twoPrimeUpperHomologyExtraction R c M
      ((primeCutoffHomology R (primeValueFunctional R) (c.val.card+1)).map (homOfLE h) x.val)) =
      twoPrimeUpperHomologyMap R (twoPrimeCoreHeight c) h
        (twoPrimeUpperHomologyEquiv R (twoPrimeCoreHeight c) N
          (twoPrimeUpperHomologyExtraction R c N x.val))
  rw [twoPrimeUpperHomologyExtraction_natural,twoPrimeUpperHomologyEquiv_natural]

#print axioms twoPrimeUpperHomologyExtraction_natural
#print axioms twoPrimeUpperCoreCoefficientEquiv_natural
/-- The original height map retains the extracted lower block class. -/
theorem twoPrimeLowerHomologyExtraction_natural (c : TwoPrimeCoreFace) {N M : ℕ} (h : N ≤ M)
    (x : (primeCutoffComplex R (primeValueFunctional R) N).homology c.val.card) :
    twoPrimeLowerHomologyExtraction R c M
      ((primeCutoffHomology R (primeValueFunctional R) c.val.card).map (homOfLE h) x) =
      ShortComplex.homologyMap (twoPrimeLowerBlockInclusion R (twoPrimeCoreHeight c) h)
        (twoPrimeLowerHomologyExtraction R c N x) := by
  obtain ⟨z,rfl⟩ := moduleHomologyClass_surjective
    ((primeCutoffComplex R (primeValueFunctional R) N).sc c.val.card) x
  change ShortComplex.homologyMap (twoPrimeLowerOriginalExtraction R c M)
    (ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.down ℕ) c.val.card).map
        (primeCutoffInclusion R (primeValueFunctional R) h)) _) =
      ShortComplex.homologyMap (twoPrimeLowerBlockInclusion R (twoPrimeCoreHeight c) h)
        (ShortComplex.homologyMap (twoPrimeLowerOriginalExtraction R c N) _)
  rw [moduleHomologyClass_map,moduleHomologyClass_map,moduleHomologyClass_map,moduleHomologyClass_map]
  apply congrArg (moduleHomologyClass (twoPrimeLowerBlock R (twoPrimeCoreHeight c) M))
  apply Subtype.ext
  rfl

/-- The actual lower core quotient comparison preserves every original height map. -/
theorem twoPrimeLowerCoreCoefficientEquiv_natural (c : TwoPrimeCoreFace) {N M : ℕ} (h : N ≤ M)
    (x : TwoPrimeHomologyCore R c.val.card N c) :
    twoPrimeLowerCoreCoefficientEquiv R c M (twoPrimeHomologyCoreMap R c.val.card c h x) =
      twoPrimeLowerHomologyMap R (twoPrimeCoreHeight c) h
        (twoPrimeLowerCoreCoefficientEquiv R c N x) := by
  change twoPrimeLowerHomologyEquiv R (twoPrimeCoreHeight c) M
    (twoPrimeLowerHomologyExtraction R c M
      ((primeCutoffHomology R (primeValueFunctional R) c.val.card).map (homOfLE h) x.val)) =
      twoPrimeLowerHomologyMap R (twoPrimeCoreHeight c) h
        (twoPrimeLowerHomologyEquiv R (twoPrimeCoreHeight c) N
          (twoPrimeLowerHomologyExtraction R c N x.val))
  rw [twoPrimeLowerHomologyExtraction_natural,twoPrimeLowerHomologyEquiv_natural]

#print axioms twoPrimeLowerHomologyExtraction_natural
#print axioms twoPrimeLowerCoreCoefficientEquiv_natural

#print axioms twoPrimeHomologyCoreMap
end GaloisForLFunctions.EffectiveScalingGeometry
