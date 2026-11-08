import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeHomologyProjections
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeBlockExtractions

/-!
# Canonical integer coefficients for prime-weighted homology

The integer exterior map commutes with prime-valued boundaries, the transformed
basis and every core projection. Passing actual cycles and boundaries through
this map constructs canonical coefficient extension on original homology.
It retains scalar normal coordinates and commutes with height inclusions.
-/

noncomputable section
open scoped Classical
open CategoryTheory RHTower DifferentialGeometry.Topology
namespace GaloisForLFunctions.EffectiveScalingGeometry
attribute [local instance] primeLabelLinearOrder
variable (R : Type*) [CommRing R]

local instance primeWeightedIntegralChainModule (k : ℕ) : Module ℤ (PrimeChainSpace ℤ k) :=
  (PrimeChainSpace ℤ k).module

/-- Prime-valued deletion commutes with canonical integral coefficient extension. -/
theorem primeIntegralChainMap_valueBoundary (k : ℕ) :
    ((primeValueBoundary R k).restrictScalars ℤ).comp (primeIntegralChainMap R (k+1)) =
      (primeIntegralChainMap R k).comp (primeValueBoundary ℤ k) := by
  apply (primeChainBasis ℤ (k+1)).ext
  intro s
  simp only [LinearMap.comp_apply,LinearMap.restrictScalars_apply,
    primeChainBasis_eq_atom,primeIntegralChainMap_atom,primeValueBoundary_atom,map_sum,map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [Nat.cast_smul_eq_nsmul,Nat.cast_smul_eq_nsmul,map_nsmul,primeIntegralChainMap_atom]

/-- The transformed exterior basis is defined over the integers. -/
theorem primeIntegralChainMap_twoPrimeBasis (k : ℕ) (s : Set.powersetCard Nat.Primes k) :
    primeIntegralChainMap R k (primeTwoPrimeBasis ℤ k s) = primeTwoPrimeBasis R k s := by
  change primeIntegralChainMap R k (primeTwoPrimeGauge ℤ k (primeChainBasis ℤ k s)) =
    primeTwoPrimeGauge R k (primeChainBasis R k s)
  rw [primeIntegralChainMap_twoPrimeGauge,primeIntegralChainMap_basis]

/-- Every normal-basis coordinate is its canonical integer scalar image. -/
theorem primeIntegralChainMap_twoPrimeCoordinate (k : ℕ) (s : Set.powersetCard Nat.Primes k)
    (x : PrimeChainSpace ℤ k) :
    (primeTwoPrimeBasis R k).repr (primeIntegralChainMap R k x) s =
      (((primeTwoPrimeBasis ℤ k).repr x s : ℤ) : R) := by
  have he : ((primeTwoPrimeBasis R k).repr.toLinearMap.restrictScalars ℤ).comp
      (primeIntegralChainMap R k) =
      (Finsupp.mapRange.linearMap ((Int.castRingHom R).toAddMonoidHom.toIntLinearMap)).comp
        (primeTwoPrimeBasis ℤ k).repr.toLinearMap := by
    apply (primeTwoPrimeBasis ℤ k).ext
    intro t
    apply Finsupp.ext
    intro u
    change (primeTwoPrimeBasis R k).repr (primeIntegralChainMap R k (primeTwoPrimeBasis ℤ k t)) u =
      (((primeTwoPrimeBasis ℤ k).repr (primeTwoPrimeBasis ℤ k t) u : ℤ) : R)
    rw [primeIntegralChainMap_twoPrimeBasis,Module.Basis.repr_self,Module.Basis.repr_self]
    by_cases h : t=u
    · simp only [Finsupp.single_apply,if_pos h,Int.cast_one]
    · simp only [Finsupp.single_apply,if_neg h,Int.cast_zero]
  exact congrArg (fun z => z s) (LinearMap.congr_fun he x)

/-- Canonical coefficient extension preserves each actual core projection. -/
theorem primeIntegralChainMap_twoPrimeCore (k : ℕ) (c : TwoPrimeCoreFace) :
    (primeIntegralChainMap R k).comp (twoPrimeCoreProjection ℤ k c) =
      ((twoPrimeCoreProjection R k c).restrictScalars ℤ).comp (primeIntegralChainMap R k) := by
  apply (primeTwoPrimeBasis ℤ k).ext
  intro s
  simp only [LinearMap.comp_apply,LinearMap.restrictScalars_apply,primeIntegralChainMap_twoPrimeBasis,
    twoPrimeCoreProjection_basis]
  by_cases h : twoPrimeFaceCore s.val=c
  · simp only [if_pos h,primeIntegralChainMap_twoPrimeBasis]
  · simp only [if_neg h,map_zero]

/-- Weighted cutoff differentials use the same integral coefficients. -/
theorem primeIntegralCutoffMap_valueBoundary (k N : ℕ) (x : primeChainCutoff ℤ (k+1) N) :
    primeCutoffDifferential R (primeValueFunctional R) k N (primeIntegralCutoffMap R (k+1) N x) =
      primeIntegralCutoffMap R k N (primeCutoffDifferential ℤ (primeValueFunctional ℤ) k N x) :=
  Subtype.ext (LinearMap.congr_fun (primeIntegralChainMap_valueBoundary R k) x.val)

/-- Tagged scalar extraction commutes with canonical integral coefficient extension. -/
theorem primeIntegralCutoffMap_twoPrimeScalar (c : TwoPrimeCoreFace) (t : TwoPrimeFaceTag)
    (N : ℕ) (x : primeChainCutoff ℤ (c.val.card+t.degree) N) :
    (twoPrimeBlockScalarExtraction R c t N
      (primeIntegralCutoffMap R (c.val.card+t.degree) N x)).val =
      (((twoPrimeBlockScalarExtraction ℤ c t N x).val : ℤ) : R) :=
  primeIntegralChainMap_twoPrimeCoordinate R (c.val.card+t.degree)
    ⟨twoPrimeTaggedFace c t,twoPrimeTaggedFace_card c t⟩ x.val

/-- Both middle coordinates extend by the canonical integer scalar map. -/
theorem primeIntegralCutoffMap_twoPrimeMiddle (c : TwoPrimeCoreFace) (N : ℕ)
    (x : primeChainCutoff ℤ (c.val.card+1) N) :
    (twoPrimeBlockMiddleExtraction R c N (primeIntegralCutoffMap R (c.val.card+1) N x)).val =
      ((((twoPrimeBlockMiddleExtraction ℤ c N x).val.1 : ℤ) : R),
       (((twoPrimeBlockMiddleExtraction ℤ c N x).val.2 : ℤ) : R)) :=
  Prod.ext (primeIntegralCutoffMap_twoPrimeScalar R c .two N x)
    (primeIntegralCutoffMap_twoPrimeScalar R c .three N x)

/-- Coefficient extension intertwines every differential of the actual augmented complex. -/
theorem primeIntegralCutoffMap_value_d (i j N : ℕ) (x : primeChainCutoff ℤ i N) :
    (primeCutoffComplex R (primeValueFunctional R) N).d i j (primeIntegralCutoffMap R i N x) =
      primeIntegralCutoffMap R j N
        ((primeCutoffComplex ℤ (primeValueFunctional ℤ) N).d i j x) := by
  by_cases h : j+1=i
  · subst i
    simp only [primeCutoffComplex,ChainComplex.of_d]
    exact primeIntegralCutoffMap_valueBoundary R j N x
  · have hR := (primeCutoffComplex R (primeValueFunctional R) N).shape i j h
    have hZ := (primeCutoffComplex ℤ (primeValueFunctional ℤ) N).shape i j h
    rw [hR,hZ]
    exact (map_zero (primeIntegralCutoffMap R j N)).symm

local instance primeWeightedIntegralCycleModule (k N : ℕ) :
    Module ℤ ((primeCutoffComplex ℤ (primeValueFunctional ℤ) N).sc k).g.hom.ker :=
  ((primeCutoffComplex ℤ (primeValueFunctional ℤ) N).sc k).g.hom.ker.module

/-- Extend an actual prime-weighted integral cycle canonically to the coefficient ring. -/
def primeWeightedIntegralCycleMap (k N : ℕ) :
    ((primeCutoffComplex ℤ (primeValueFunctional ℤ) N).sc k).g.hom.ker →ₗ[ℤ]
      ((primeCutoffComplex R (primeValueFunctional R) N).sc k).g.hom.ker where
  toFun x := ⟨primeIntegralCutoffMap R k N x.val,by
    have he := primeIntegralCutoffMap_value_d R k ((ComplexShape.down ℕ).next k) N x.val
    rw [show (primeCutoffComplex ℤ (primeValueFunctional ℤ) N).d k
      ((ComplexShape.down ℕ).next k) x.val = 0 from x.property] at he
    exact he.trans ((primeIntegralCutoffMap R ((ComplexShape.down ℕ).next k) N).map_zero)⟩
  map_add' x y := Subtype.ext ((primeIntegralCutoffMap R k N).map_add x.val y.val)
  map_smul' a x := Subtype.ext ((primeIntegralCutoffMap R k N).map_smul a x.val)

def primeWeightedIntegralClassMap (k N : ℕ) :
    ((primeCutoffComplex ℤ (primeValueFunctional ℤ) N).sc k).g.hom.ker →ₗ[ℤ]
      (primeCutoffComplex R (primeValueFunctional R) N).homology k :=
  ((moduleHomologyClass ((primeCutoffComplex R (primeValueFunctional R) N).sc k)).restrictScalars ℤ).comp
    (primeWeightedIntegralCycleMap R k N)

/-- Canonical coefficient extension takes weighted boundaries to weighted boundaries. -/
theorem primeWeightedIntegralClassMap_kills_boundaries (k N : ℕ) :
    ((primeCutoffComplex ℤ (primeValueFunctional ℤ) N).sc k).moduleCatToCycles.range ≤
      (primeWeightedIntegralClassMap R k N).ker := by
  rintro _ ⟨y,rfl⟩
  change moduleHomologyClass ((primeCutoffComplex R (primeValueFunctional R) N).sc k)
    (primeWeightedIntegralCycleMap R k N
      (((primeCutoffComplex ℤ (primeValueFunctional ℤ) N).sc k).moduleCatToCycles y)) = 0
  apply (moduleHomologyClass_eq_zero_iff _ _).mpr
  exact ⟨primeIntegralCutoffMap R ((ComplexShape.down ℕ).prev k) N y,
    primeIntegralCutoffMap_value_d R ((ComplexShape.down ℕ).prev k) k N y⟩

def primeWeightedIntegralQuotientMap (k N : ℕ) :=
  ((primeCutoffComplex ℤ (primeValueFunctional ℤ) N).sc k).moduleCatToCycles.range.liftQ
    (primeWeightedIntegralClassMap R k N) (primeWeightedIntegralClassMap_kills_boundaries R k N)

/-- Canonical integral coefficient extension on the original prime-weighted homology. -/
def primeWeightedIntegralHomologyMap (k N : ℕ) :
    (primeCutoffComplex ℤ (primeValueFunctional ℤ) N).homology k →ₗ[ℤ]
      (primeCutoffComplex R (primeValueFunctional R) N).homology k :=
  (primeWeightedIntegralQuotientMap R k N).comp
    ((primeCutoffComplex ℤ (primeValueFunctional ℤ) N).sc k).moduleCatHomologyIso.hom.hom

/-- The coefficient map sends each original class to the class of the extended cycle. -/
theorem primeWeightedIntegralHomologyMap_class (k N : ℕ)
    (z : ((primeCutoffComplex ℤ (primeValueFunctional ℤ) N).sc k).g.hom.ker) :
    primeWeightedIntegralHomologyMap R k N
      (moduleHomologyClass ((primeCutoffComplex ℤ (primeValueFunctional ℤ) N).sc k) z) =
    moduleHomologyClass ((primeCutoffComplex R (primeValueFunctional R) N).sc k)
      (primeWeightedIntegralCycleMap R k N z) := by
  change primeWeightedIntegralQuotientMap R k N
    (((primeCutoffComplex ℤ (primeValueFunctional ℤ) N).sc k).moduleCatHomologyIso.hom
      (moduleHomologyClass ((primeCutoffComplex ℤ (primeValueFunctional ℤ) N).sc k) z)) = _
  rw [moduleHomologyClass_quotient]
  rfl

/-- Coefficient extension commutes with actual core homology projections. -/
theorem primeWeightedIntegralHomologyMap_core (k N : ℕ) (c : TwoPrimeCoreFace)
    (x : (primeCutoffComplex ℤ (primeValueFunctional ℤ) N).homology k) :
    primeWeightedIntegralHomologyMap R k N (twoPrimeCoreHomologyProjection ℤ k N c x) =
      twoPrimeCoreHomologyProjection R k N c (primeWeightedIntegralHomologyMap R k N x) := by
  obtain ⟨z,rfl⟩ := moduleHomologyClass_surjective
    ((primeCutoffComplex ℤ (primeValueFunctional ℤ) N).sc k) x
  rw [twoPrimeCoreHomologyProjection_class,primeWeightedIntegralHomologyMap_class,
    primeWeightedIntegralHomologyMap_class,twoPrimeCoreHomologyProjection_class]
  apply congrArg (moduleHomologyClass ((primeCutoffComplex R (primeValueFunctional R) N).sc k))
  apply Subtype.ext
  apply Subtype.ext
  exact LinearMap.congr_fun (primeIntegralChainMap_twoPrimeCore R k c) z.val.val

/-- Canonical coefficient extension commutes with the original height persistence. -/
theorem primeWeightedIntegralHomologyMap_natural (k : ℕ) {N M : ℕ} (h : N ≤ M)
    (x : (primeCutoffComplex ℤ (primeValueFunctional ℤ) N).homology k) :
    (primeCutoffHomology R (primeValueFunctional R) k).map (homOfLE h)
      (primeWeightedIntegralHomologyMap R k N x) =
      primeWeightedIntegralHomologyMap R k M
        ((primeCutoffHomology ℤ (primeValueFunctional ℤ) k).map (homOfLE h) x) := by
  obtain ⟨z,rfl⟩ := moduleHomologyClass_surjective
    ((primeCutoffComplex ℤ (primeValueFunctional ℤ) N).sc k) x
  change ShortComplex.homologyMap
    ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.down ℕ) k).map
      (primeCutoffInclusion R (primeValueFunctional R) h))
    (primeWeightedIntegralHomologyMap R k N _) =
      primeWeightedIntegralHomologyMap R k M
        (ShortComplex.homologyMap
          ((HomologicalComplex.shortComplexFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k).map
            (primeCutoffInclusion ℤ (primeValueFunctional ℤ) h)) _)
  rw [primeWeightedIntegralHomologyMap_class,moduleHomologyClass_map,
    moduleHomologyClass_map,primeWeightedIntegralHomologyMap_class]
  apply congrArg (moduleHomologyClass ((primeCutoffComplex R (primeValueFunctional R) M).sc k))
  apply Subtype.ext
  apply Subtype.ext
  rfl

#print axioms primeWeightedIntegralHomologyMap_natural
#print axioms primeIntegralCutoffMap_twoPrimeScalar
#print axioms primeIntegralCutoffMap_twoPrimeMiddle
#print axioms primeIntegralChainMap_valueBoundary
#print axioms primeIntegralChainMap_twoPrimeCoordinate
#print axioms primeIntegralChainMap_twoPrimeCore
#print axioms primeWeightedIntegralHomologyMap_class
#print axioms primeWeightedIntegralHomologyMap_core
end GaloisForLFunctions.EffectiveScalingGeometry
