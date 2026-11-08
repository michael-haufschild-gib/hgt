import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeBlockRetractions
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeHomologyCoreSum
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeBlockHomology

/-! The actual middle-degree core summand is canonically its truncated upper-block
homology and scalar quotient. The comparison uses original cycle-class maps;
its section and projection identities retain the same chain representatives. -/

noncomputable section
open scoped Classical
open CategoryTheory RHTower DifferentialGeometry.Topology
namespace GaloisForLFunctions.EffectiveScalingGeometry
variable (R : Type*) [CommRing R]

/-- Realize an upper block in the original short complex defining homology. -/
def twoPrimeUpperOriginalRealization (c : TwoPrimeCoreFace) (N : ℕ) :
    twoPrimeUpperBlock R (twoPrimeCoreHeight c) N ⟶
      (primeCutoffComplex R (primeValueFunctional R) N).sc (c.val.card+1) :=
  twoPrimeUpperBlockRealization R c N ≫
    ((primeCutoffComplex R (primeValueFunctional R) N).isoSc'
      (c.val.card+2) (c.val.card+1) c.val.card (by simp) (by simp)).inv

/-- Extract the upper block from the original short complex defining homology. -/
def twoPrimeUpperOriginalRetraction (c : TwoPrimeCoreFace) (N : ℕ) :
    (primeCutoffComplex R (primeValueFunctional R) N).sc (c.val.card+1) ⟶
      twoPrimeUpperBlock R (twoPrimeCoreHeight c) N :=
  ((primeCutoffComplex R (primeValueFunctional R) N).isoSc'
    (c.val.card+2) (c.val.card+1) c.val.card (by simp) (by simp)).hom ≫
      twoPrimeUpperBlockRetraction R c N

/-- The original homology inclusion of an upper block. -/
def twoPrimeUpperHomologyRealization (c : TwoPrimeCoreFace) (N : ℕ) :
    (twoPrimeUpperBlock R (twoPrimeCoreHeight c) N).homology →ₗ[R]
      (primeCutoffComplex R (primeValueFunctional R) N).homology (c.val.card+1) :=
  (ShortComplex.homologyMap (twoPrimeUpperOriginalRealization R c N)).hom

/-- The original homology extraction onto an upper block. -/
def twoPrimeUpperHomologyExtraction (c : TwoPrimeCoreFace) (N : ℕ) :
    (primeCutoffComplex R (primeValueFunctional R) N).homology (c.val.card+1) →ₗ[R]
      (twoPrimeUpperBlock R (twoPrimeCoreHeight c) N).homology :=
  (ShortComplex.homologyMap (twoPrimeUpperOriginalRetraction R c N)).hom

/-- Extracting an included upper homology class returns that same class. -/
theorem twoPrimeUpperHomology_section (c : TwoPrimeCoreFace) (N : ℕ)
    (x : (twoPrimeUpperBlock R (twoPrimeCoreHeight c) N).homology) :
    twoPrimeUpperHomologyExtraction R c N (twoPrimeUpperHomologyRealization R c N x) = x := by
  obtain ⟨z,rfl⟩ := moduleHomologyClass_surjective
    (twoPrimeUpperBlock R (twoPrimeCoreHeight c) N) x
  change ShortComplex.homologyMap (twoPrimeUpperOriginalRetraction R c N)
    (ShortComplex.homologyMap (twoPrimeUpperOriginalRealization R c N) _) = _
  rw [moduleHomologyClass_map,moduleHomologyClass_map]
  apply congrArg (moduleHomologyClass (twoPrimeUpperBlock R (twoPrimeCoreHeight c) N))
  apply Subtype.ext
  exact twoPrimeBlockMiddleExtraction_realization R c N z.val

/-- Including the extracted class is exactly the original homology core projection. -/
theorem twoPrimeUpperHomology_projection (c : TwoPrimeCoreFace) (N : ℕ)
    (x : (primeCutoffComplex R (primeValueFunctional R) N).homology (c.val.card+1)) :
    twoPrimeUpperHomologyRealization R c N (twoPrimeUpperHomologyExtraction R c N x) =
      twoPrimeCoreHomologyProjection R (c.val.card+1) N c x := by
  obtain ⟨z,rfl⟩ := moduleHomologyClass_surjective
    ((primeCutoffComplex R (primeValueFunctional R) N).sc (c.val.card+1)) x
  change ShortComplex.homologyMap (twoPrimeUpperOriginalRealization R c N)
    (ShortComplex.homologyMap (twoPrimeUpperOriginalRetraction R c N) _) = _
  rw [moduleHomologyClass_map,moduleHomologyClass_map,twoPrimeCoreHomologyProjection_class]
  apply congrArg (moduleHomologyClass
    ((primeCutoffComplex R (primeValueFunctional R) N).sc (c.val.card+1)))
  apply Subtype.ext
  exact LinearMap.congr_fun (twoPrimeMiddle_realization_extraction R c N) z.val

/-- The actual upper core summand is its truncated arithmetic block homology. -/
def twoPrimeUpperCoreHomologyEquiv (c : TwoPrimeCoreFace) (N : ℕ) :
    TwoPrimeHomologyCore R (c.val.card+1) N c ≃ₗ[R]
      (twoPrimeUpperBlock R (twoPrimeCoreHeight c) N).homology where
  toFun x := twoPrimeUpperHomologyExtraction R c N x.val
  invFun y := ⟨twoPrimeUpperHomologyRealization R c N y,by
    refine ⟨twoPrimeUpperHomologyRealization R c N y,?_⟩
    exact (twoPrimeUpperHomology_projection R c N
      (twoPrimeUpperHomologyRealization R c N y)).symm.trans
      (congrArg (twoPrimeUpperHomologyRealization R c N) (twoPrimeUpperHomology_section R c N y))⟩
  left_inv x := by
    apply Subtype.ext
    exact (twoPrimeUpperHomology_projection R c N x.val).trans
      ((twoPrimeCoreHomologyProjection_range R (c.val.card+1) N c c x).trans (if_pos rfl))
  right_inv y := twoPrimeUpperHomology_section R c N y
  map_add' x y := (twoPrimeUpperHomologyExtraction R c N).map_add x.val y.val
  map_smul' a x := (twoPrimeUpperHomologyExtraction R c N).map_smul a x.val

/-- Exact scalar quotient coordinates for the original upper core contribution. -/
def twoPrimeUpperCoreCoefficientEquiv (c : TwoPrimeCoreFace) (N : ℕ) :
    TwoPrimeHomologyCore R (c.val.card+1) N c ≃ₗ[R]
      TwoPrimeUpperHomology R (twoPrimeCoreHeight c) N :=
  (twoPrimeUpperCoreHomologyEquiv R c N).trans
    (twoPrimeUpperHomologyEquiv R (twoPrimeCoreHeight c) N)

#print axioms twoPrimeUpperHomology_section
#print axioms twoPrimeUpperHomology_projection
#print axioms twoPrimeUpperCoreCoefficientEquiv
end GaloisForLFunctions.EffectiveScalingGeometry
