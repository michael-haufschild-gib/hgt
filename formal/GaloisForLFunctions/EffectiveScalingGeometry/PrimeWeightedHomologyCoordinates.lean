import GaloisForLFunctions.EffectiveScalingGeometry.PrimeWeightedCoordinatePersistence
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ModuleHomologyMaps

/-!
# Actual integral prime-weighted homology in positive degrees

The actual categorical homology persistence is naturally isomorphic to the
free and parity coefficient functor. Restricted cycles have the bounded odd
coordinates, and the joint coefficient projection has kernel exactly the
actual boundary range. The first isomorphism theorem therefore descends the
coordinates through homology classes. The comparison commutes with height
inclusions, including the reduction of free coefficients to parity classes.
-/

noncomputable section
open CategoryTheory RHTower
namespace GaloisForLFunctions.EffectiveScalingGeometry

/-- The actual three adjacent cutoff modules in positive exterior degree. -/
def primeValuePositiveShortComplex (k N : ℕ) : ShortComplex (ModuleCat ℤ) where
  X₁ := ModuleCat.of ℤ (primeChainCutoff ℤ ((k+1)+1) N)
  X₂ := ModuleCat.of ℤ (primeChainCutoff ℤ (k+1) N)
  X₃ := ModuleCat.of ℤ (primeChainCutoff ℤ k N)
  f := ModuleCat.ofHom (primeCutoffDifferential ℤ (primeValueFunctional ℤ) (k+1) N)
  g := ModuleCat.ofHom (primeCutoffDifferential ℤ (primeValueFunctional ℤ) k N)
  zero := ModuleCat.hom_ext (primeCutoffDifferential_sq ℤ (primeValueFunctional ℤ) k N)

/-- Restricted-kernel cycles are exactly ambient cycles within the cutoff. -/
def primeValueRestrictedCycleEquiv (k N : ℕ) :
    (primeValuePositiveShortComplex k N).g.hom.ker ≃ₗ[ℤ] primeValueCutoffCycles ℤ k N where
  toFun x := ⟨x.val.val, x.val.property, congrArg Subtype.val x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, Subtype.ext x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Actual cycles mapped to the coefficients that survive at this height. -/
def primeValueCycleHomologyProjection (k N : ℕ) :
    (primeValuePositiveShortComplex k N).g.hom.ker →ₗ[ℤ] primeValueCoordinates (k+1) N :=
  (primeValueHomologyProjection (k+1) N).comp
    ((primeValueCycleOddEquiv k N).toLinearMap.comp
      (primeValueRestrictedCycleEquiv k N).toLinearMap)

theorem primeValueCycleHomologyProjection_surjective (k N : ℕ) :
    Function.Surjective (primeValueCycleHomologyProjection k N) :=
  (primeValueHomologyProjection_surjective (k+1) N).comp
    ((primeValueCycleOddEquiv k N).surjective.comp
      (primeValueRestrictedCycleEquiv k N).surjective)

/-- The joint coefficient map kills exactly the actual weighted boundaries. -/
theorem primeValueCycleHomologyProjection_ker (k N : ℕ) :
    (primeValueCycleHomologyProjection k N).ker =
      (primeValuePositiveShortComplex k N).moduleCatToCycles.range := by
  ext x
  change primeValueHomologyProjection (k+1) N
    (primeValueCycleOddEquiv k N (primeValueRestrictedCycleEquiv k N x)) = 0 ↔ _
  rw [primeValueHomologyProjection_eq_zero_iff,← primeValueBoundaryCoordinates_eq_lattice]
  change primeValueOddCoordinates ℤ k x.val.val ∈ primeValueBoundaryCoordinates k N ↔ _
  constructor
  · rintro ⟨b,⟨y,hy,rfl⟩,he⟩
    refine ⟨⟨y,hy⟩,?_⟩
    apply (primeValueRestrictedCycleEquiv k N).injective
    apply (primeValueCycleOddEquiv k N).injective
    exact Subtype.ext he
  · rintro ⟨y,rfl⟩
    exact Submodule.mem_map.mpr
      ⟨primeValueBoundary ℤ (k+1) y.val,Submodule.mem_map.mpr ⟨y.val,y.property,rfl⟩,rfl⟩

/-- The first isomorphism theorem on the actual restricted cycles. -/
def primeValuePositiveCycleQuotientEquiv (k N : ℕ) :=
  @LinearMap.quotKerEquivOfSurjective ℤ
    ↥(primeValuePositiveShortComplex k N).g.hom.ker
    (primeValueCoordinates (k+1) N) (inferInstanceAs (Ring ℤ))
    (primeValuePositiveShortComplex k N).g.hom.ker.addCommGroup
    (inferInstanceAs (AddCommGroup (primeValueCoordinates (k+1) N)))
    (primeValuePositiveShortComplex k N).g.hom.ker.module
    (inferInstanceAs (Module ℤ (primeValueCoordinates (k+1) N)))
    (primeValueCycleHomologyProjection k N) (primeValueCycleHomologyProjection_surjective k N)

/-- Replacing the actual boundary range by its identified kernel. -/
def primeValuePositiveBoundaryQuotientEquiv (k N : ℕ) :=
  @Submodule.quotEquivOfEq ℤ ↥(primeValuePositiveShortComplex k N).g.hom.ker
    (inferInstanceAs (Ring ℤ)) (primeValuePositiveShortComplex k N).g.hom.ker.addCommGroup
    (primeValuePositiveShortComplex k N).g.hom.ker.module
    (primeValuePositiveShortComplex k N).moduleCatToCycles.range
    (primeValueCycleHomologyProjection k N).ker (primeValueCycleHomologyProjection_ker k N).symm

/-- Categorical weighted homology has its free and parity coefficients. -/
def primeValuePositiveHomologyEquiv (k N : ℕ) :=
  (primeValuePositiveShortComplex k N).moduleCatHomologyIso.toLinearEquiv.trans
    ((primeValuePositiveBoundaryQuotientEquiv k N).trans (primeValuePositiveCycleQuotientEquiv k N))

/-- The comparison uses the actual cycle class, with its unchanged coefficients. -/
theorem primeValuePositiveHomologyEquiv_class (k N : ℕ)
    (x : (primeValuePositiveShortComplex k N).g.hom.ker) :
    primeValuePositiveHomologyEquiv k N
      (DifferentialGeometry.Topology.moduleHomologyClass (primeValuePositiveShortComplex k N) x) =
      primeValueCycleHomologyProjection k N x := by
  unfold primeValuePositiveHomologyEquiv
  simp only [LinearEquiv.trans_apply]
  change primeValuePositiveCycleQuotientEquiv k N
    (primeValuePositiveBoundaryQuotientEquiv k N
      ((primeValuePositiveShortComplex k N).moduleCatHomologyIso.hom
        (DifferentialGeometry.Topology.moduleHomologyClass (primeValuePositiveShortComplex k N) x))) = _
  rw [DifferentialGeometry.Topology.moduleHomologyClass_quotient]
  rfl

/-- The three literal inclusions define the short-complex persistence map. -/
def primeValuePositiveShortInclusion (k : ℕ) {N M : ℕ} (h : N ≤ M) :
    primeValuePositiveShortComplex k N ⟶ primeValuePositiveShortComplex k M where
  τ₁ := ModuleCat.ofHom (Submodule.inclusion (primeChainCutoff_mono ℤ ((k+1)+1) h))
  τ₂ := ModuleCat.ofHom (Submodule.inclusion (primeChainCutoff_mono ℤ (k+1) h))
  τ₃ := ModuleCat.ofHom (Submodule.inclusion (primeChainCutoff_mono ℤ k h))
  comm₁₂ := by rfl
  comm₂₃ := by rfl

/-- The same prime-cutoff persistence, restricted to three adjacent degrees. -/
def primeValuePositiveShortPersistence (k : ℕ) : ℕ ⥤ ShortComplex (ModuleCat ℤ) where
  obj N := primeValuePositiveShortComplex k N
  map h := primeValuePositiveShortInclusion k h.le
  map_id _ := by ext <;> rfl
  map_comp _ _ := by ext <;> rfl

theorem primeValueCycleHomologyProjection_natural (k : ℕ) {N M : ℕ} (h : N ≤ M) :
    (primeValueCoordinateMap (k+1) N M).comp (primeValueCycleHomologyProjection k N) =
      (primeValueCycleHomologyProjection k M).comp
        (DifferentialGeometry.Topology.moduleCycleMap (primeValuePositiveShortInclusion k h)) := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (primeValueHomologyProjection_natural (k+1) h)
    (primeValueCycleOddEquiv k N (primeValueRestrictedCycleEquiv k N x))

/-- Actual homology transitions retain coefficients and reduce them modulo two at torsion onset. -/
theorem primeValuePositiveHomologyEquiv_natural (k : ℕ) {N M : ℕ} (h : N ≤ M)
    (x : (primeValuePositiveShortComplex k N).homology) :
    primeValuePositiveHomologyEquiv k M (ShortComplex.homologyMap (primeValuePositiveShortInclusion k h) x) =
      primeValueCoordinateMap (k+1) N M (primeValuePositiveHomologyEquiv k N x) := by
  obtain ⟨c,rfl⟩ := DifferentialGeometry.Topology.moduleHomologyClass_surjective
    (primeValuePositiveShortComplex k N) x
  rw [DifferentialGeometry.Topology.moduleHomologyClass_map,
    primeValuePositiveHomologyEquiv_class,primeValuePositiveHomologyEquiv_class]
  exact (LinearMap.congr_fun (primeValueCycleHomologyProjection_natural k h) c).symm

/-- The explicit weighted short-complex homology has natural free and parity coordinates. -/
def primeValuePositiveHomologyCoordinateIso (k : ℕ) :
    primeValuePositiveShortPersistence k ⋙ ShortComplex.homologyFunctor (ModuleCat ℤ) ≅
      primeValueCoordinatePersistence (k+1) :=
  NatIso.ofComponents (fun N => (primeValuePositiveHomologyEquiv k N).toModuleIso)
    (fun h => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact primeValuePositiveHomologyEquiv_natural k h.le x)

/-- Evaluating the adjacent differentials changes no chain or inclusion. -/
def primeValuePositiveShortComplexComparison (k N : ℕ) :
    (primeCutoffComplex ℤ (primeValueFunctional ℤ) N).sc' (k+2) (k+1) k ≅
      primeValuePositiveShortComplex k N :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      simp only [Iso.refl_hom]
      change ModuleCat.ofHom (primeCutoffDifferential ℤ (primeValueFunctional ℤ) (k+1) N) =
        (primeCutoffComplex ℤ (primeValueFunctional ℤ) N).d ((k+1)+1) (k+1)
      simp only [primeCutoffComplex,ChainComplex.of_d])
    (by
      simp only [Iso.refl_hom]
      change ModuleCat.ofHom (primeCutoffDifferential ℤ (primeValueFunctional ℤ) k N) =
        (primeCutoffComplex ℤ (primeValueFunctional ℤ) N).d (k+1) k
      simp only [primeCutoffComplex,ChainComplex.of_d])

/-- The adjacent-degree comparison commutes with every height inclusion. -/
def primeValuePositiveShortPersistenceComparison (k : ℕ) :
    primeCutoffPersistence ℤ (primeValueFunctional ℤ) ⋙
      HomologicalComplex.shortComplexFunctor' (ModuleCat ℤ) (ComplexShape.down ℕ)
        (k+2) (k+1) k ≅ primeValuePositiveShortPersistence k :=
  NatIso.ofComponents (primeValuePositiveShortComplexComparison k) (fun _ => by ext <;> rfl)

/-- Natural free and parity coordinates for actual positive-degree weighted homology. -/
def primeValueHomologyCoordinateIsoSucc (k : ℕ) :
    primeCutoffHomology ℤ (primeValueFunctional ℤ) (k+1) ≅ primeValueCoordinatePersistence (k+1) :=
  Functor.isoWhiskerLeft (primeCutoffPersistence ℤ (primeValueFunctional ℤ))
      (HomologicalComplex.homologyFunctorIso' (ModuleCat ℤ) (ComplexShape.down ℕ)
        (k+2) (k+1) k (by simp) (by simp)) ≪≫
    (Functor.associator (primeCutoffPersistence ℤ (primeValueFunctional ℤ))
      (HomologicalComplex.shortComplexFunctor' (ModuleCat ℤ) (ComplexShape.down ℕ) (k+2) (k+1) k)
      (ShortComplex.homologyFunctor (ModuleCat ℤ))).symm ≪≫
    Functor.isoWhiskerRight (primeValuePositiveShortPersistenceComparison k)
      (ShortComplex.homologyFunctor (ModuleCat ℤ)) ≪≫
    primeValuePositiveHomologyCoordinateIso k

#print axioms primeValueCycleHomologyProjection_ker
#print axioms primeValuePositiveHomologyEquiv
#print axioms primeValueHomologyCoordinateIsoSucc
end GaloisForLFunctions.EffectiveScalingGeometry
