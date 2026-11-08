import GaloisForLFunctions.EffectiveScalingGeometry.PrimeHomologyCoordinates
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeCycleBasis

/-!
# Augmented prime persistence and the empty-face interval

The empty face contributes exactly on `[1,2)`. Its actual categorical homology
is identified with the same surviving-coordinate model as the positive degrees.
The zero outgoing differential makes every empty chain a cycle; the exact
boundary-height law identifies the discarded half cutoff. The comparison
commutes with height inclusions. Combined with the positive-degree theorem,
this gives a natural isomorphism for actual augmented homology in every degree,
over every commutative coefficient ring.
-/

noncomputable section
open CategoryTheory RHTower
namespace GaloisForLFunctions.EffectiveScalingGeometry
variable (R : Type*) [CommRing R]

/-- The unique empty prime support survives exactly on the interval `[1,2)`. -/
theorem primeCriticalFaces_zero_iff (N : ℕ) (s : Set.powersetCard Nat.Primes 0) :
    s ∈ primeCriticalFaces 0 N ↔ N = 1 := by
  have hs : s.val = ∅ := Finset.card_eq_zero.mp s.property
  have hp : primeFaceProduct s = 1 := by
    unfold primeFaceProduct
    rw [hs]
    exact Finset.prod_empty
  have hn : primeTwoLabel ∉ s.val := by
    rw [hs]
    exact Finset.notMem_empty _
  change primeFaceProduct s ≤ N ∧ primeTwoLabel ∉ s.val ∧ N < 2 * primeFaceProduct s ↔ N = 1
  rw [hp]
  constructor
  · intro h
    omega
  · rintro rfl
    exact ⟨le_rfl,hn,by omega⟩

/-- The augmented empty-face degree has zero outgoing differential. -/
def primeZeroShortComplex (N : ℕ) : ShortComplex (ModuleCat R) where
  X₁ := ModuleCat.of R (primeChainCutoff R 1 N)
  X₂ := ModuleCat.of R (primeChainCutoff R 0 N)
  X₃ := ModuleCat.of R (primeChainCutoff R 0 N)
  f := ModuleCat.ofHom (primeCutoffDifferential R (primeChainAugmentation R) 0 N)
  g := 0
  zero := by simp only [CategoryTheory.Limits.comp_zero]

/-- Every empty-face chain is a cycle and an odd chain. -/
def primeZeroCycleOddEquiv (N : ℕ) :
    (primeZeroShortComplex R N).g.hom.ker ≃ₗ[R] primeOddCutoff R 0 N where
  toFun x := ⟨x.val.val, (primeOddCutoff_zero R N).symm ▸ x.val.property⟩
  invFun x := ⟨⟨x.val, (primeOddCutoff_zero R N) ▸ x.property⟩, rfl⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def primeZeroCriticalProjection (N : ℕ) :
    (primeZeroShortComplex R N).g.hom.ker →ₗ[R] primeCriticalCoordinates R 0 N :=
  (primeCriticalProjection R 0 N).comp (primeZeroCycleOddEquiv R N).toLinearMap

theorem primeZeroCriticalProjection_surjective (N : ℕ) :
    Function.Surjective (primeZeroCriticalProjection R N) :=
  (primeCriticalProjection_surjective R 0 N).comp (primeZeroCycleOddEquiv R N).surjective

theorem primeZeroCriticalProjection_eq_zero_iff (N : ℕ)
    (x : (primeZeroShortComplex R N).g.hom.ker) :
    primeZeroCriticalProjection R N x = 0 ↔ x.val.val ∈ primeChainCutoff R 0 (N/2) := by
  change primeCriticalProjection R 0 N (primeZeroCycleOddEquiv R N x) = 0 ↔ _
  rw [← LinearMap.mem_ker,primeCriticalProjection_ker]
  change x.val.val ∈ primeOddCutoff R 0 (N/2) ↔ _
  rw [primeOddCutoff_zero]

/-- Actual augmented boundaries kill precisely the half-cutoff empty chains. -/
theorem primeZeroCriticalProjection_ker (N : ℕ) :
    (primeZeroCriticalProjection R N).ker = (primeZeroShortComplex R N).moduleCatToCycles.range := by
  ext x
  change primeZeroCriticalProjection R N x = 0 ↔ _
  rw [primeZeroCriticalProjection_eq_zero_iff]
  constructor
  · intro h
    have hx : x.val.val ∈ (primeChainCutoff R 1 N).map (primeChainBoundary R 0) := by
      rw [primeChainBoundary_zero_image_eq_half]
      exact h
    obtain ⟨y,hy,he⟩ := Submodule.mem_map.mp hx
    exact ⟨⟨y,hy⟩,Subtype.ext (Subtype.ext he)⟩
  · rintro ⟨y,rfl⟩
    exact primeChainBoundary_half_mem R 0 N y.val y.property

def primeZeroCycleQuotientEquiv (N : ℕ) :=
  @LinearMap.quotKerEquivOfSurjective R ↥(primeZeroShortComplex R N).g.hom.ker
    ↥(primeCriticalCoordinates R 0 N) (inferInstanceAs (Ring R))
    (primeZeroShortComplex R N).g.hom.ker.addCommGroup
    (Finsupp.supported R R (primeCriticalFaces 0 N)).addCommGroup
    (primeZeroShortComplex R N).g.hom.ker.module
    (Finsupp.supported R R (primeCriticalFaces 0 N)).module
    (primeZeroCriticalProjection R N) (primeZeroCriticalProjection_surjective R N)

def primeZeroBoundaryQuotientEquiv (N : ℕ) :=
  @Submodule.quotEquivOfEq R ↥(primeZeroShortComplex R N).g.hom.ker
    (inferInstanceAs (Ring R)) (primeZeroShortComplex R N).g.hom.ker.addCommGroup
    (primeZeroShortComplex R N).g.hom.ker.module
    (primeZeroShortComplex R N).moduleCatToCycles.range
    (primeZeroCriticalProjection R N).ker (primeZeroCriticalProjection_ker R N).symm

/-- Actual homology in the empty-face degree has its surviving coefficients. -/
def primeZeroShortHomologyEquiv (N : ℕ) :=
  (primeZeroShortComplex R N).moduleCatHomologyIso.toLinearEquiv.trans
    ((primeZeroBoundaryQuotientEquiv R N).trans (primeZeroCycleQuotientEquiv R N))

theorem primeZeroShortHomologyEquiv_class (N : ℕ)
    (x : (primeZeroShortComplex R N).g.hom.ker) :
    primeZeroShortHomologyEquiv R N
      (DifferentialGeometry.Topology.moduleHomologyClass (primeZeroShortComplex R N) x) =
      primeZeroCriticalProjection R N x := by
  unfold primeZeroShortHomologyEquiv
  simp only [LinearEquiv.trans_apply]
  change primeZeroCycleQuotientEquiv R N (primeZeroBoundaryQuotientEquiv R N
    ((primeZeroShortComplex R N).moduleCatHomologyIso.hom
      (DifferentialGeometry.Topology.moduleHomologyClass (primeZeroShortComplex R N) x))) = _
  rw [DifferentialGeometry.Topology.moduleHomologyClass_quotient]
  rfl

def primeZeroShortInclusion {N M : ℕ} (h : N ≤ M) :
    primeZeroShortComplex R N ⟶ primeZeroShortComplex R M where
  τ₁ := ModuleCat.ofHom (Submodule.inclusion (primeChainCutoff_mono R 1 h))
  τ₂ := ModuleCat.ofHom (Submodule.inclusion (primeChainCutoff_mono R 0 h))
  τ₃ := ModuleCat.ofHom (Submodule.inclusion (primeChainCutoff_mono R 0 h))
  comm₁₂ := by rfl
  comm₂₃ := by rfl

def primeZeroShortPersistence : ℕ ⥤ ShortComplex (ModuleCat R) where
  obj N := primeZeroShortComplex R N
  map h := primeZeroShortInclusion R h.le
  map_id _ := by ext <;> rfl
  map_comp _ _ := by ext <;> rfl

theorem primeZeroCriticalProjection_natural {N M : ℕ} (h : N ≤ M) :
    (primeCriticalMap R 0 N M).comp (primeZeroCriticalProjection R N) =
      (primeZeroCriticalProjection R M).comp
        (DifferentialGeometry.Topology.moduleCycleMap (primeZeroShortInclusion R h)) := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (primeCriticalProjection_natural R 0 h) (primeZeroCycleOddEquiv R N x)

theorem primeZeroShortHomologyEquiv_natural {N M : ℕ} (h : N ≤ M)
    (x : (primeZeroShortComplex R N).homology) :
    primeZeroShortHomologyEquiv R M (ShortComplex.homologyMap (primeZeroShortInclusion R h) x) =
      primeCriticalMap R 0 N M (primeZeroShortHomologyEquiv R N x) := by
  obtain ⟨c,rfl⟩ := DifferentialGeometry.Topology.moduleHomologyClass_surjective
    (primeZeroShortComplex R N) x
  rw [DifferentialGeometry.Topology.moduleHomologyClass_map,
    primeZeroShortHomologyEquiv_class,primeZeroShortHomologyEquiv_class]
  exact (LinearMap.congr_fun (primeZeroCriticalProjection_natural R h) c).symm

def primeZeroShortHomologyCriticalIso :
    primeZeroShortPersistence R ⋙ ShortComplex.homologyFunctor (ModuleCat R) ≅
      primeCriticalPersistence R 0 :=
  NatIso.ofComponents (fun N => (primeZeroShortHomologyEquiv R N).toModuleIso)
    (fun h => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact primeZeroShortHomologyEquiv_natural R h.le x)

/-- The degree-zero adjacent complex is the actual augmented complex. -/
def primeZeroShortComplexComparison (N : ℕ) :
    (primeCutoffComplex R (primeChainAugmentation R) N).sc' 1 0 0 ≅
      primeZeroShortComplex R N :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      simp only [Iso.refl_hom]
      change ModuleCat.ofHom (primeCutoffDifferential R (primeChainAugmentation R) 0 N) =
        (primeCutoffComplex R (primeChainAugmentation R) N).d 1 0
      rfl)
    (by
      simp only [Iso.refl_hom]
      change 0 = (primeCutoffComplex R (primeChainAugmentation R) N).d 0 0
      rfl)

def primeZeroShortPersistenceComparison :
    primeCutoffPersistence R (primeChainAugmentation R) ⋙
      HomologicalComplex.shortComplexFunctor' (ModuleCat R) (ComplexShape.down ℕ) 1 0 0 ≅
        primeZeroShortPersistence R :=
  NatIso.ofComponents (primeZeroShortComplexComparison R) (fun _ => by ext <;> rfl)

/-- Natural coordinates for the actual augmented degree-zero homology. -/
def primeHomologyCriticalIsoZero :
    primeCutoffHomology R (primeChainAugmentation R) 0 ≅ primeCriticalPersistence R 0 :=
  Functor.isoWhiskerLeft (primeCutoffPersistence R (primeChainAugmentation R))
      (HomologicalComplex.homologyFunctorIso' (ModuleCat R) (ComplexShape.down ℕ)
        1 0 0 (by simp) (by simp)) ≪≫
    (Functor.associator (primeCutoffPersistence R (primeChainAugmentation R))
      (HomologicalComplex.shortComplexFunctor' (ModuleCat R) (ComplexShape.down ℕ) 1 0 0)
      (ShortComplex.homologyFunctor (ModuleCat R))).symm ≪≫
    Functor.isoWhiskerRight (primeZeroShortPersistenceComparison R)
      (ShortComplex.homologyFunctor (ModuleCat R)) ≪≫
    primeZeroShortHomologyCriticalIso R

/-- The actual augmented homology persistence is the surviving-face functor in every degree. -/
def primeHomologyCriticalIso : (k : ℕ) →
    primeCutoffHomology R (primeChainAugmentation R) k ≅ primeCriticalPersistence R k
  | 0 => primeHomologyCriticalIsoZero R
  | k+1 => primeHomologyCriticalIsoSucc R k

#print axioms primeCriticalFaces_zero_iff
#print axioms primeZeroCriticalProjection_ker
#print axioms primeHomologyCriticalIsoZero
#print axioms primeHomologyCriticalIso
end GaloisForLFunctions.EffectiveScalingGeometry
