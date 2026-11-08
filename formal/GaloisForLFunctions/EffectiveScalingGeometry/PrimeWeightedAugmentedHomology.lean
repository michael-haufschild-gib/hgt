import GaloisForLFunctions.EffectiveScalingGeometry.PrimeWeightedHomologyCoordinates
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeWeightedAugmentedBoundary

/-!
# Actual augmented integral prime-weighted homology

The empty-degree boundary formula identifies actual homology with the same
free and parity coefficient model as positive degrees. The comparison uses
the original cycle class and commutes with every height inclusion. Combining
both degree ranges gives a natural isomorphism for the entire augmented
homology persistence functor, including the empty class's transition from an
integer generator to an order-two class.
-/

noncomputable section
open CategoryTheory RHTower
namespace GaloisForLFunctions.EffectiveScalingGeometry

/-- The augmented empty-face degree has zero outgoing differential. -/
def primeValueZeroShortComplex (N : ℕ) : ShortComplex (ModuleCat ℤ) where
  X₁ := ModuleCat.of ℤ (primeChainCutoff ℤ 1 N)
  X₂ := ModuleCat.of ℤ (primeChainCutoff ℤ 0 N)
  X₃ := ModuleCat.of ℤ (primeChainCutoff ℤ 0 N)
  f := ModuleCat.ofHom (primeCutoffDifferential ℤ (primeValueFunctional ℤ) 0 N)
  g := 0
  zero := by simp only [CategoryTheory.Limits.comp_zero]

/-- Every empty-face chain is a cycle and an odd chain. -/
def primeValueZeroCycleOddEquiv (N : ℕ) :
    (primeValueZeroShortComplex N).g.hom.ker ≃ₗ[ℤ] primeOddCutoff ℤ 0 N where
  toFun x := ⟨x.val.val, (primeOddCutoff_zero ℤ N).symm ▸ x.val.property⟩
  invFun x := ⟨⟨x.val, (primeOddCutoff_zero ℤ N) ▸ x.property⟩, rfl⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def primeValueZeroHomologyProjection (N : ℕ) :
    (primeValueZeroShortComplex N).g.hom.ker →ₗ[ℤ] primeValueCoordinates 0 N :=
  (primeValueHomologyProjection 0 N).comp (primeValueZeroCycleOddEquiv N).toLinearMap

theorem primeValueZeroHomologyProjection_surjective (N : ℕ) :
    Function.Surjective (primeValueZeroHomologyProjection N) :=
  (primeValueHomologyProjection_surjective 0 N).comp (primeValueZeroCycleOddEquiv N).surjective

theorem primeValueZeroHomologyProjection_eq_zero_iff (N : ℕ)
    (x : (primeValueZeroShortComplex N).g.hom.ker) :
    primeValueZeroHomologyProjection N x = 0 ↔ x.val.val ∈ primeValueCoordinateLattice 0 N := by
  exact primeValueHomologyProjection_eq_zero_iff 0 N (primeValueZeroCycleOddEquiv N x)

/-- Actual augmented boundaries are precisely the coordinate lattice in empty degree. -/
theorem primeValueZeroHomologyProjection_ker (N : ℕ) :
    (primeValueZeroHomologyProjection N).ker = (primeValueZeroShortComplex N).moduleCatToCycles.range := by
  ext x
  change primeValueZeroHomologyProjection N x = 0 ↔ _
  rw [primeValueZeroHomologyProjection_eq_zero_iff,← primeValueZeroBoundary_eq_lattice]
  constructor
  · rintro ⟨y,hy,he⟩
    exact ⟨⟨y,hy⟩,Subtype.ext (Subtype.ext he)⟩
  · rintro ⟨y,rfl⟩
    exact Submodule.mem_map.mpr ⟨y.val,y.property,rfl⟩

def primeValueZeroCycleQuotientEquiv (N : ℕ) :=
  @LinearMap.quotKerEquivOfSurjective ℤ ↥(primeValueZeroShortComplex N).g.hom.ker
    (primeValueCoordinates 0 N) (inferInstanceAs (Ring ℤ))
    (primeValueZeroShortComplex N).g.hom.ker.addCommGroup
    (inferInstanceAs (AddCommGroup (primeValueCoordinates 0 N)))
    (primeValueZeroShortComplex N).g.hom.ker.module
    (inferInstanceAs (Module ℤ (primeValueCoordinates 0 N)))
    (primeValueZeroHomologyProjection N) (primeValueZeroHomologyProjection_surjective N)

def primeValueZeroBoundaryQuotientEquiv (N : ℕ) :=
  @Submodule.quotEquivOfEq ℤ ↥(primeValueZeroShortComplex N).g.hom.ker
    (inferInstanceAs (Ring ℤ)) (primeValueZeroShortComplex N).g.hom.ker.addCommGroup
    (primeValueZeroShortComplex N).g.hom.ker.module
    (primeValueZeroShortComplex N).moduleCatToCycles.range
    (primeValueZeroHomologyProjection N).ker (primeValueZeroHomologyProjection_ker N).symm

/-- Actual empty-degree weighted homology has its free and parity coefficients. -/
def primeValueZeroHomologyEquiv (N : ℕ) :=
  (primeValueZeroShortComplex N).moduleCatHomologyIso.toLinearEquiv.trans
    ((primeValueZeroBoundaryQuotientEquiv N).trans (primeValueZeroCycleQuotientEquiv N))

theorem primeValueZeroHomologyEquiv_class (N : ℕ)
    (x : (primeValueZeroShortComplex N).g.hom.ker) :
    primeValueZeroHomologyEquiv N
      (DifferentialGeometry.Topology.moduleHomologyClass (primeValueZeroShortComplex N) x) =
      primeValueZeroHomologyProjection N x := by
  unfold primeValueZeroHomologyEquiv
  simp only [LinearEquiv.trans_apply]
  change primeValueZeroCycleQuotientEquiv N (primeValueZeroBoundaryQuotientEquiv N
    ((primeValueZeroShortComplex N).moduleCatHomologyIso.hom
      (DifferentialGeometry.Topology.moduleHomologyClass (primeValueZeroShortComplex N) x))) = _
  rw [DifferentialGeometry.Topology.moduleHomologyClass_quotient]
  rfl

def primeValueZeroShortInclusion {N M : ℕ} (h : N ≤ M) :
    primeValueZeroShortComplex N ⟶ primeValueZeroShortComplex M where
  τ₁ := ModuleCat.ofHom (Submodule.inclusion (primeChainCutoff_mono ℤ 1 h))
  τ₂ := ModuleCat.ofHom (Submodule.inclusion (primeChainCutoff_mono ℤ 0 h))
  τ₃ := ModuleCat.ofHom (Submodule.inclusion (primeChainCutoff_mono ℤ 0 h))
  comm₁₂ := by rfl
  comm₂₃ := by rfl

def primeValueZeroShortPersistence : ℕ ⥤ ShortComplex (ModuleCat ℤ) where
  obj N := primeValueZeroShortComplex N
  map h := primeValueZeroShortInclusion h.le
  map_id _ := by ext <;> rfl
  map_comp _ _ := by ext <;> rfl

theorem primeValueZeroHomologyProjection_natural {N M : ℕ} (h : N ≤ M) :
    (primeValueCoordinateMap 0 N M).comp (primeValueZeroHomologyProjection N) =
      (primeValueZeroHomologyProjection M).comp
        (DifferentialGeometry.Topology.moduleCycleMap (primeValueZeroShortInclusion h)) := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (primeValueHomologyProjection_natural 0 h) (primeValueZeroCycleOddEquiv N x)

theorem primeValueZeroHomologyEquiv_natural {N M : ℕ} (h : N ≤ M)
    (x : (primeValueZeroShortComplex N).homology) :
    primeValueZeroHomologyEquiv M (ShortComplex.homologyMap (primeValueZeroShortInclusion h) x) =
      primeValueCoordinateMap 0 N M (primeValueZeroHomologyEquiv N x) := by
  obtain ⟨c,rfl⟩ := DifferentialGeometry.Topology.moduleHomologyClass_surjective
    (primeValueZeroShortComplex N) x
  rw [DifferentialGeometry.Topology.moduleHomologyClass_map,
    primeValueZeroHomologyEquiv_class,primeValueZeroHomologyEquiv_class]
  exact (LinearMap.congr_fun (primeValueZeroHomologyProjection_natural h) c).symm

def primeValueZeroHomologyCoordinateIso :
    primeValueZeroShortPersistence ⋙ ShortComplex.homologyFunctor (ModuleCat ℤ) ≅
      primeValueCoordinatePersistence 0 :=
  NatIso.ofComponents (fun N => (primeValueZeroHomologyEquiv N).toModuleIso)
    (fun h => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact primeValueZeroHomologyEquiv_natural h.le x)

/-- The degree-zero adjacent complex is the actual augmented complex. -/
def primeValueZeroShortComplexComparison (N : ℕ) :
    (primeCutoffComplex ℤ (primeValueFunctional ℤ) N).sc' 1 0 0 ≅
      primeValueZeroShortComplex N :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      simp only [Iso.refl_hom]
      change ModuleCat.ofHom (primeCutoffDifferential ℤ (primeValueFunctional ℤ) 0 N) =
        (primeCutoffComplex ℤ (primeValueFunctional ℤ) N).d 1 0
      rfl)
    (by
      simp only [Iso.refl_hom]
      change 0 = (primeCutoffComplex ℤ (primeValueFunctional ℤ) N).d 0 0
      rfl)

def primeValueZeroShortPersistenceComparison :
    primeCutoffPersistence ℤ (primeValueFunctional ℤ) ⋙
      HomologicalComplex.shortComplexFunctor' (ModuleCat ℤ) (ComplexShape.down ℕ) 1 0 0 ≅
        primeValueZeroShortPersistence :=
  NatIso.ofComponents (primeValueZeroShortComplexComparison) (fun _ => by ext <;> rfl)

/-- Natural coordinates for the actual augmented degree-zero homology. -/
def primeValueHomologyCoordinateIsoZero :
    primeCutoffHomology ℤ (primeValueFunctional ℤ) 0 ≅ primeValueCoordinatePersistence 0 :=
  Functor.isoWhiskerLeft (primeCutoffPersistence ℤ (primeValueFunctional ℤ))
      (HomologicalComplex.homologyFunctorIso' (ModuleCat ℤ) (ComplexShape.down ℕ)
        1 0 0 (by simp) (by simp)) ≪≫
    (Functor.associator (primeCutoffPersistence ℤ (primeValueFunctional ℤ))
      (HomologicalComplex.shortComplexFunctor' (ModuleCat ℤ) (ComplexShape.down ℕ) 1 0 0)
      (ShortComplex.homologyFunctor (ModuleCat ℤ))).symm ≪≫
    Functor.isoWhiskerRight (primeValueZeroShortPersistenceComparison)
      (ShortComplex.homologyFunctor (ModuleCat ℤ)) ≪≫
    primeValueZeroHomologyCoordinateIso

/-- Actual integral prime-weighted homology has the free-to-parity persistence in every augmented degree. -/
def primeValueHomologyCoordinateIso : (k : ℕ) →
    primeCutoffHomology ℤ (primeValueFunctional ℤ) k ≅ primeValueCoordinatePersistence k
  | 0 => primeValueHomologyCoordinateIsoZero
  | k+1 => primeValueHomologyCoordinateIsoSucc k

#print axioms primeValueZeroHomologyProjection_ker
#print axioms primeValueHomologyCoordinateIsoZero
#print axioms primeValueHomologyCoordinateIso
end GaloisForLFunctions.EffectiveScalingGeometry
