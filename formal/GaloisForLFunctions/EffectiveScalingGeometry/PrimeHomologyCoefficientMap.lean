import GaloisForLFunctions.EffectiveScalingGeometry.PrimeIntegralCoefficients
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeAugmentedHomology

/-!
# Canonical coefficient maps on actual prime homology

Integral coefficient extension sends cycles to cycles and boundaries to
boundaries. Descending through the actual boundary quotient gives the induced
homology map, whose class formula uses the original chain extension. The maps
commute with height inclusions in every augmented degree. The adjacent-complex
comparison transports these statements to the original homology functor.
-/

noncomputable section
open CategoryTheory RHTower
open DifferentialGeometry.Topology
namespace GaloisForLFunctions.EffectiveScalingGeometry
variable (R : Type*) [CommRing R]

/-- The explicit adjacent complex in every augmented exterior degree. -/
def primeCoefficientShortPersistence : (k : ℕ) → ℕ ⥤ ShortComplex (ModuleCat R)
  | 0 => primeZeroShortPersistence R
  | k+1 => primeShortPersistence R k

abbrev primeCoefficientShortComplex (k N : ℕ) := (primeCoefficientShortPersistence R k).obj N

local instance primeIntegerShortCycleModule (k N : ℕ) :
    Module ℤ (primeCoefficientShortComplex ℤ k N).g.hom.ker :=
  (primeCoefficientShortComplex ℤ k N).g.hom.ker.module

/-- Canonical chain extension sends actual integral cycles to actual cycles. -/
def primeIntegralShortCycleMap (k N : ℕ) :
    (primeCoefficientShortComplex ℤ k N).g.hom.ker →ₗ[ℤ]
      (primeCoefficientShortComplex R k N).g.hom.ker := by
  cases k with
  | zero =>
    exact
      { toFun := fun x => ⟨primeIntegralCutoffMap R 0 N x.val,rfl⟩
        map_add' := fun x y => Subtype.ext ((primeIntegralCutoffMap R 0 N).map_add x.val y.val)
        map_smul' := fun a x => Subtype.ext ((primeIntegralCutoffMap R 0 N).map_smul a x.val) }
  | succ k =>
    refine
      { toFun := fun x => ⟨primeIntegralCutoffMap R (k+1) N x.val,?_⟩
        map_add' := fun x y => Subtype.ext ((primeIntegralCutoffMap R (k+1) N).map_add x.val y.val)
        map_smul' := fun a x => Subtype.ext ((primeIntegralCutoffMap R (k+1) N).map_smul a x.val) }
    change primeCutoffDifferential R (primeChainAugmentation R) k N
      (primeIntegralCutoffMap R (k+1) N x.val) = 0
    rw [primeIntegralCutoffMap_boundary]
    have hx : primeCutoffDifferential ℤ (primeChainAugmentation ℤ) k N x.val = 0 := x.property
    rw [hx,map_zero]

/-- Take the actual coefficient-ring class of the canonically extended cycle. -/
def primeIntegralShortClassMap (k N : ℕ) :
    (primeCoefficientShortComplex ℤ k N).g.hom.ker →ₗ[ℤ]
      (primeCoefficientShortComplex R k N).homology :=
  ((moduleHomologyClass (primeCoefficientShortComplex R k N)).restrictScalars ℤ).comp
    (primeIntegralShortCycleMap R k N)

/-- Integral boundaries become actual boundaries after coefficient extension. -/
theorem primeIntegralShortClassMap_kills_boundaries (k N : ℕ) :
    (primeCoefficientShortComplex ℤ k N).moduleCatToCycles.range ≤
      (primeIntegralShortClassMap R k N).ker := by
  rintro _ ⟨y,rfl⟩
  change moduleHomologyClass (primeCoefficientShortComplex R k N)
    (primeIntegralShortCycleMap R k N ((primeCoefficientShortComplex ℤ k N).moduleCatToCycles y)) = 0
  apply (moduleHomologyClass_eq_zero_iff _ _).mpr
  cases k with
  | zero =>
    exact ⟨primeIntegralCutoffMap R 1 N y,primeIntegralCutoffMap_boundary R 0 N y⟩
  | succ k =>
    exact ⟨primeIntegralCutoffMap R ((k+1)+1) N y,primeIntegralCutoffMap_boundary R (k+1) N y⟩

/-- Descend the actual class map through the integral boundary quotient. -/
def primeIntegralShortQuotientMap (k N : ℕ) :=
  (primeCoefficientShortComplex ℤ k N).moduleCatToCycles.range.liftQ
    (primeIntegralShortClassMap R k N) (primeIntegralShortClassMap_kills_boundaries R k N)

/-- The map on actual short-complex homology induced by canonical chain extension. -/
def primeIntegralShortHomologyMap (k N : ℕ) :
    (primeCoefficientShortComplex ℤ k N).homology →ₗ[ℤ]
      (primeCoefficientShortComplex R k N).homology :=
  (primeIntegralShortQuotientMap R k N).comp
    (primeCoefficientShortComplex ℤ k N).moduleCatHomologyIso.hom.hom

/-- The induced map takes a class to the class of the same extended cycle. -/
theorem primeIntegralShortHomologyMap_class (k N : ℕ)
    (c : (primeCoefficientShortComplex ℤ k N).g.hom.ker) :
    primeIntegralShortHomologyMap R k N (moduleHomologyClass (primeCoefficientShortComplex ℤ k N) c) =
      moduleHomologyClass (primeCoefficientShortComplex R k N) (primeIntegralShortCycleMap R k N c) := by
  change primeIntegralShortQuotientMap R k N
    ((primeCoefficientShortComplex ℤ k N).moduleCatHomologyIso.hom
      (moduleHomologyClass (primeCoefficientShortComplex ℤ k N) c)) = _
  rw [moduleHomologyClass_quotient]
  rfl

/-- The same cycle is obtained in either order of coefficient and height extension. -/
theorem primeIntegralShortCycleMap_natural (k : ℕ) {N M : ℕ} (h : N ≤ M)
    (c : (primeCoefficientShortComplex ℤ k N).g.hom.ker) :
    moduleCycleMap ((primeCoefficientShortPersistence R k).map (homOfLE h))
      (primeIntegralShortCycleMap R k N c) =
    primeIntegralShortCycleMap R k M
      (moduleCycleMap ((primeCoefficientShortPersistence ℤ k).map (homOfLE h)) c) := by
  cases k <;> apply Subtype.ext <;> apply Subtype.ext <;> rfl

/-- Canonical coefficient extension commutes with actual short-homology persistence. -/
theorem primeIntegralShortHomologyMap_natural (k : ℕ) {N M : ℕ} (h : N ≤ M)
    (x : (primeCoefficientShortComplex ℤ k N).homology) :
    ShortComplex.homologyMap ((primeCoefficientShortPersistence R k).map (homOfLE h))
      (primeIntegralShortHomologyMap R k N x) =
    primeIntegralShortHomologyMap R k M
      (ShortComplex.homologyMap ((primeCoefficientShortPersistence ℤ k).map (homOfLE h)) x) := by
  obtain ⟨c,rfl⟩ := moduleHomologyClass_surjective (primeCoefficientShortComplex ℤ k N) x
  rw [primeIntegralShortHomologyMap_class,moduleHomologyClass_map,moduleHomologyClass_map,
    primeIntegralShortHomologyMap_class]
  exact congrArg (moduleHomologyClass (primeCoefficientShortComplex R k M))
    (primeIntegralShortCycleMap_natural R k h c)

/-- Forgetting the unused degrees identifies actual and adjacent-complex homology. -/
def primeHomologyToCoefficientShortIso : (k : ℕ) →
    primeCutoffHomology R (primeChainAugmentation R) k ≅
      primeCoefficientShortPersistence R k ⋙ ShortComplex.homologyFunctor (ModuleCat R)
  | 0 =>
    Functor.isoWhiskerLeft (primeCutoffPersistence R (primeChainAugmentation R))
      (HomologicalComplex.homologyFunctorIso' (ModuleCat R) (ComplexShape.down ℕ)
        1 0 0 (by simp) (by simp)) ≪≫
    (Functor.associator (primeCutoffPersistence R (primeChainAugmentation R))
      (HomologicalComplex.shortComplexFunctor' (ModuleCat R) (ComplexShape.down ℕ) 1 0 0)
      (ShortComplex.homologyFunctor (ModuleCat R))).symm ≪≫
    Functor.isoWhiskerRight (primeZeroShortPersistenceComparison R)
      (ShortComplex.homologyFunctor (ModuleCat R))
  | k+1 =>
    Functor.isoWhiskerLeft (primeCutoffPersistence R (primeChainAugmentation R))
      (HomologicalComplex.homologyFunctorIso' (ModuleCat R) (ComplexShape.down ℕ)
        (k+2) (k+1) k (by simp) (by simp)) ≪≫
    (Functor.associator (primeCutoffPersistence R (primeChainAugmentation R))
      (HomologicalComplex.shortComplexFunctor' (ModuleCat R) (ComplexShape.down ℕ) (k+2) (k+1) k)
      (ShortComplex.homologyFunctor (ModuleCat R))).symm ≪≫
    Functor.isoWhiskerRight (primeShortPersistenceComparison R k)
      (ShortComplex.homologyFunctor (ModuleCat R))

def primeCoefficientShortCriticalIso : (k : ℕ) →
    primeCoefficientShortPersistence R k ⋙ ShortComplex.homologyFunctor (ModuleCat R) ≅
      primeCriticalPersistence R k
  | 0 => primeZeroShortHomologyCriticalIso R
  | k+1 => primeShortHomologyCriticalIso R k

/-- The surviving-coordinate comparison factors through the actual adjacent complex. -/
theorem primeHomologyCriticalIso_factor (k N : ℕ)
    (x : (primeCutoffHomology R (primeChainAugmentation R) k).obj N) :
    ((primeHomologyCriticalIso R k).app N).hom x =
      ((primeCoefficientShortCriticalIso R k).app N).hom
        (((primeHomologyToCoefficientShortIso R k).app N).hom x) := by
  cases k <;> rfl

abbrev primeHomologyShortEquiv (k N : ℕ) :=
  ((primeHomologyToCoefficientShortIso R k).app N).toLinearEquiv

/-- Actual augmented homology classes of restricted cycles. -/
def primeActualHomologyClass (k N : ℕ) :
    (primeCoefficientShortComplex R k N).g.hom.ker →ₗ[R]
      (primeCutoffHomology R (primeChainAugmentation R) k).obj N :=
  (primeHomologyShortEquiv R k N).symm.toLinearMap.comp
    (moduleHomologyClass (primeCoefficientShortComplex R k N))

theorem primeActualHomologyClass_surjective (k N : ℕ) :
    Function.Surjective (primeActualHomologyClass R k N) :=
  (primeHomologyShortEquiv R k N).symm.surjective.comp
    (moduleHomologyClass_surjective (primeCoefficientShortComplex R k N))

theorem primeHomologyShortEquiv_natural (k : ℕ) {N M : ℕ} (h : N ≤ M)
    (x : (primeCutoffHomology R (primeChainAugmentation R) k).obj N) :
    primeHomologyShortEquiv R k M
      ((primeCutoffHomology R (primeChainAugmentation R) k).map (homOfLE h) x) =
      ShortComplex.homologyMap ((primeCoefficientShortPersistence R k).map (homOfLE h))
        (primeHomologyShortEquiv R k N x) :=
  congrArg (fun f => f x) ((primeHomologyToCoefficientShortIso R k).hom.naturality (homOfLE h))

/-- Raising height takes an actual cycle class to the class of its inclusion. -/
theorem primeActualHomologyClass_natural (k : ℕ) {N M : ℕ} (h : N ≤ M)
    (c : (primeCoefficientShortComplex R k N).g.hom.ker) :
    (primeCutoffHomology R (primeChainAugmentation R) k).map (homOfLE h)
      (primeActualHomologyClass R k N c) =
    primeActualHomologyClass R k M
      (moduleCycleMap ((primeCoefficientShortPersistence R k).map (homOfLE h)) c) := by
  apply (primeHomologyShortEquiv R k M).injective
  rw [primeHomologyShortEquiv_natural]
  simp only [primeActualHomologyClass,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply]
  exact moduleHomologyClass_map _ c

/-- Canonical coefficient extension on actual augmented homology. -/
def primeIntegralHomologyMap (k N : ℕ) :
    (primeCutoffHomology ℤ (primeChainAugmentation ℤ) k).obj N →ₗ[ℤ]
      (primeCutoffHomology R (primeChainAugmentation R) k).obj N :=
  ((primeHomologyShortEquiv R k N).symm.toLinearMap.restrictScalars ℤ).comp
    ((primeIntegralShortHomologyMap R k N).comp
      (primeHomologyShortEquiv ℤ k N).toLinearMap)

/-- The canonical map acts on actual classes by extending their cycles. -/
theorem primeIntegralHomologyMap_class (k N : ℕ)
    (c : (primeCoefficientShortComplex ℤ k N).g.hom.ker) :
    primeIntegralHomologyMap R k N (primeActualHomologyClass ℤ k N c) =
      primeActualHomologyClass R k N (primeIntegralShortCycleMap R k N c) := by
  change (primeHomologyShortEquiv R k N).symm
    (primeIntegralShortHomologyMap R k N
      (primeHomologyShortEquiv ℤ k N ((primeHomologyShortEquiv ℤ k N).symm
        (moduleHomologyClass (primeCoefficientShortComplex ℤ k N) c)))) = _
  rw [LinearEquiv.apply_symm_apply,primeIntegralShortHomologyMap_class]
  rfl

/-- Coefficient extension commutes with the original homology persistence maps. -/
theorem primeIntegralHomologyMap_natural (k : ℕ) {N M : ℕ} (h : N ≤ M)
    (x : (primeCutoffHomology ℤ (primeChainAugmentation ℤ) k).obj N) :
    (primeCutoffHomology R (primeChainAugmentation R) k).map (homOfLE h)
      (primeIntegralHomologyMap R k N x) =
    primeIntegralHomologyMap R k M
      ((primeCutoffHomology ℤ (primeChainAugmentation ℤ) k).map (homOfLE h) x) := by
  obtain ⟨c,rfl⟩ := primeActualHomologyClass_surjective ℤ k N x
  rw [primeIntegralHomologyMap_class,primeActualHomologyClass_natural,
    primeActualHomologyClass_natural,primeIntegralHomologyMap_class,
    primeIntegralShortCycleMap_natural]

#print axioms primeIntegralShortHomologyMap_class
#print axioms primeIntegralShortHomologyMap_natural
#print axioms primeIntegralHomologyMap_class
#print axioms primeIntegralHomologyMap_natural
end GaloisForLFunctions.EffectiveScalingGeometry
