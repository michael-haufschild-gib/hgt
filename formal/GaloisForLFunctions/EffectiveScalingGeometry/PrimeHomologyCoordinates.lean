import GaloisForLFunctions.EffectiveScalingGeometry.PrimeCriticalCoordinates
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeBoundaryHeight
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ModuleHomologyMaps

/-!
# Natural coordinates for actual prime-cutoff homology

In every positive exterior degree, the actual categorical homology persistence
functor is naturally isomorphic to the surviving odd-face coefficients.
A face of product `m` contributes precisely at heights `m ≤ N < 2m`.
The comparison sends actual cycle classes to their unchanged odd coefficients.
It uses the exact boundary-height law, then transports the concrete quotient
through the original chain complex's short-complex homology comparison.
All maps and isomorphisms work over every commutative ring.
-/

noncomputable section
open CategoryTheory RHTower
namespace GaloisForLFunctions.EffectiveScalingGeometry
variable (R : Type*) [CommRing R]

/-- The actual three adjacent cutoff modules in positive exterior degree. -/
def primeCutoffShortComplex (k N : ℕ) : ShortComplex (ModuleCat R) where
  X₁ := ModuleCat.of R (primeChainCutoff R ((k+1)+1) N)
  X₂ := ModuleCat.of R (primeChainCutoff R (k+1) N)
  X₃ := ModuleCat.of R (primeChainCutoff R k N)
  f := ModuleCat.ofHom (primeCutoffDifferential R (primeChainAugmentation R) (k+1) N)
  g := ModuleCat.ofHom (primeCutoffDifferential R (primeChainAugmentation R) k N)
  zero := ModuleCat.hom_ext (primeCutoffDifferential_sq R (primeChainAugmentation R) k N)

/-- Restricted-kernel cycles are exactly ambient cycles within the cutoff. -/
def primeRestrictedCycleEquiv (k N : ℕ) :
    (primeCutoffShortComplex R k N).g.hom.ker ≃ₗ[R] primeCutoffCycles R k N where
  toFun x := ⟨x.val.val, x.val.property, congrArg Subtype.val x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, Subtype.ext x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Actual cycles mapped to the coefficients that survive at this height. -/
def primeCycleCriticalProjection (k N : ℕ) :
    (primeCutoffShortComplex R k N).g.hom.ker →ₗ[R] primeCriticalCoordinates R (k+1) N :=
  (primeCriticalProjection R (k+1) N).comp
    ((primeCutoffCycleOddEquiv R k N).toLinearMap.comp
      (primeRestrictedCycleEquiv R k N).toLinearMap)

/-- The odd coordinate equivalence detects every smaller cutoff. -/
theorem primeCycleOdd_mem_cutoff_iff (k N M : ℕ) (x : primeCutoffCycles R k N) :
    (primeCutoffCycleOddEquiv R k N x).val ∈ primeOddCutoff R (k+1) M ↔
      x.val ∈ primeChainCutoff R (k+1) M := by
  change oddChainProjection R (k+1) x.val ∈ primeOddCutoff R (k+1) M ↔ _
  constructor
  · intro h
    have hh := primeCycleProjector_cutoff R k M h.1
    have he : primeCycleProjector R k (oddChainProjection R (k+1) x.val) = x.val :=
      (LinearMap.congr_fun (primeCycleProjector_comp_oddProjection R k) x.val).trans
        (primeCycleProjector_fixes_cycles R k ⟨x.val,x.property.2⟩)
    change primeCycleProjector R k (oddChainProjection R (k+1) x.val) ∈
      primeChainCutoff R (k+1) M at hh
    rwa [he] at hh
  · intro h
    exact ⟨oddChainProjection_cutoff R (k+1) M h, ⟨x.val,rfl⟩⟩

theorem primeCycleCriticalProjection_surjective (k N : ℕ) :
    Function.Surjective (primeCycleCriticalProjection R k N) :=
  (primeCriticalProjection_surjective R (k+1) N).comp
    ((primeCutoffCycleOddEquiv R k N).surjective.comp
      (primeRestrictedCycleEquiv R k N).surjective)

theorem primeCycleCriticalProjection_eq_zero_iff (k N : ℕ)
    (x : (primeCutoffShortComplex R k N).g.hom.ker) :
    primeCycleCriticalProjection R k N x = 0 ↔
      x.val.val ∈ primeChainCutoff R (k+1) (N/2) := by
  change primeCriticalProjection R (k+1) N
    (primeCutoffCycleOddEquiv R k N (primeRestrictedCycleEquiv R k N x)) = 0 ↔ _
  rw [← LinearMap.mem_ker, primeCriticalProjection_ker]
  exact primeCycleOdd_mem_cutoff_iff R k N (N/2) (primeRestrictedCycleEquiv R k N x)

/-- The coordinate projection kills exactly the actual boundaries. -/
theorem primeCycleCriticalProjection_ker (k N : ℕ) :
    (primeCycleCriticalProjection R k N).ker =
      (primeCutoffShortComplex R k N).moduleCatToCycles.range := by
  ext x
  change primeCycleCriticalProjection R k N x = 0 ↔ _
  rw [primeCycleCriticalProjection_eq_zero_iff]
  constructor
  · intro h
    have hx : x.val.val ∈
        (primeChainCutoff R ((k+1)+1) N).map (primeChainBoundary R (k+1)) := by
      rw [primeChainBoundary_image_eq_half_cycles]
      exact ⟨h, congrArg Subtype.val x.property⟩
    obtain ⟨y,hy,he⟩ := Submodule.mem_map.mp hx
    exact ⟨⟨y,hy⟩, Subtype.ext (Subtype.ext he)⟩
  · rintro ⟨y,rfl⟩
    exact primeChainBoundary_half_mem R (k+1) N y.val y.property

/-- The first isomorphism theorem on the actual restricted cycles. -/
def primeShortCycleQuotientEquiv (k N : ℕ) :=
  @LinearMap.quotKerEquivOfSurjective R
    ↥(primeCutoffShortComplex R k N).g.hom.ker
    ↥(primeCriticalCoordinates R (k+1) N) (inferInstanceAs (Ring R))
    (primeCutoffShortComplex R k N).g.hom.ker.addCommGroup
    (Finsupp.supported R R (primeCriticalFaces (k+1) N)).addCommGroup
    (primeCutoffShortComplex R k N).g.hom.ker.module
    (Finsupp.supported R R (primeCriticalFaces (k+1) N)).module
    (primeCycleCriticalProjection R k N) (primeCycleCriticalProjection_surjective R k N)

/-- Replacing the actual boundary range by its identified kernel. -/
def primeShortBoundaryQuotientEquiv (k N : ℕ) :=
  @Submodule.quotEquivOfEq R ↥(primeCutoffShortComplex R k N).g.hom.ker
    (inferInstanceAs (Ring R)) (primeCutoffShortComplex R k N).g.hom.ker.addCommGroup
    (primeCutoffShortComplex R k N).g.hom.ker.module
    (primeCutoffShortComplex R k N).moduleCatToCycles.range
    (primeCycleCriticalProjection R k N).ker (primeCycleCriticalProjection_ker R k N).symm

/-- Categorical homology has precisely the odd coordinates in `(N/2,N]`. -/
def primeShortHomologyEquiv (k N : ℕ) :=
  (primeCutoffShortComplex R k N).moduleCatHomologyIso.toLinearEquiv.trans
    ((primeShortBoundaryQuotientEquiv R k N).trans (primeShortCycleQuotientEquiv R k N))

/-- The comparison uses the actual cycle class, with its unchanged coefficients. -/
theorem primeShortHomologyEquiv_class (k N : ℕ)
    (x : (primeCutoffShortComplex R k N).g.hom.ker) :
    primeShortHomologyEquiv R k N
      (DifferentialGeometry.Topology.moduleHomologyClass (primeCutoffShortComplex R k N) x) =
      primeCycleCriticalProjection R k N x := by
  unfold primeShortHomologyEquiv
  simp only [LinearEquiv.trans_apply]
  change primeShortCycleQuotientEquiv R k N
    (primeShortBoundaryQuotientEquiv R k N
      ((primeCutoffShortComplex R k N).moduleCatHomologyIso.hom
        (DifferentialGeometry.Topology.moduleHomologyClass (primeCutoffShortComplex R k N) x))) = _
  rw [DifferentialGeometry.Topology.moduleHomologyClass_quotient]
  rfl

/-- The three literal inclusions define the short-complex persistence map. -/
def primeShortInclusion (k : ℕ) {N M : ℕ} (h : N ≤ M) :
    primeCutoffShortComplex R k N ⟶ primeCutoffShortComplex R k M where
  τ₁ := ModuleCat.ofHom (Submodule.inclusion (primeChainCutoff_mono R ((k+1)+1) h))
  τ₂ := ModuleCat.ofHom (Submodule.inclusion (primeChainCutoff_mono R (k+1) h))
  τ₃ := ModuleCat.ofHom (Submodule.inclusion (primeChainCutoff_mono R k h))
  comm₁₂ := by rfl
  comm₂₃ := by rfl

/-- The same prime-cutoff persistence, restricted to three adjacent degrees. -/
def primeShortPersistence (k : ℕ) : ℕ ⥤ ShortComplex (ModuleCat R) where
  obj N := primeCutoffShortComplex R k N
  map h := primeShortInclusion R k h.le
  map_id _ := by ext <;> rfl
  map_comp _ _ := by ext <;> rfl

theorem primeCycleCriticalProjection_natural (k : ℕ) {N M : ℕ} (h : N ≤ M) :
    (primeCriticalMap R (k+1) N M).comp (primeCycleCriticalProjection R k N) =
      (primeCycleCriticalProjection R k M).comp
        (DifferentialGeometry.Topology.moduleCycleMap (primeShortInclusion R k h)) := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (primeCriticalProjection_natural R (k+1) h)
    (primeCutoffCycleOddEquiv R k N (primeRestrictedCycleEquiv R k N x))

/-- The original homology map retains exactly the same surviving coordinates. -/
theorem primeShortHomologyEquiv_natural (k : ℕ) {N M : ℕ} (h : N ≤ M)
    (x : (primeCutoffShortComplex R k N).homology) :
    primeShortHomologyEquiv R k M (ShortComplex.homologyMap (primeShortInclusion R k h) x) =
      primeCriticalMap R (k+1) N M (primeShortHomologyEquiv R k N x) := by
  obtain ⟨c,rfl⟩ := DifferentialGeometry.Topology.moduleHomologyClass_surjective
    (primeCutoffShortComplex R k N) x
  rw [DifferentialGeometry.Topology.moduleHomologyClass_map,
    primeShortHomologyEquiv_class,primeShortHomologyEquiv_class]
  exact (LinearMap.congr_fun (primeCycleCriticalProjection_natural R k h) c).symm

/-- The explicit short-complex homology has natural surviving coordinates. -/
def primeShortHomologyCriticalIso (k : ℕ) :
    primeShortPersistence R k ⋙ ShortComplex.homologyFunctor (ModuleCat R) ≅
      primeCriticalPersistence R (k+1) :=
  NatIso.ofComponents (fun N => (primeShortHomologyEquiv R k N).toModuleIso)
    (fun h => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact primeShortHomologyEquiv_natural R k h.le x)

/-- Evaluating the adjacent differentials changes no chain or inclusion. -/
def primeShortComplexComparison (k N : ℕ) :
    (primeCutoffComplex R (primeChainAugmentation R) N).sc' (k+2) (k+1) k ≅
      primeCutoffShortComplex R k N :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      simp only [Iso.refl_hom]
      change ModuleCat.ofHom (primeCutoffDifferential R (primeChainAugmentation R) (k+1) N) =
        (primeCutoffComplex R (primeChainAugmentation R) N).d ((k+1)+1) (k+1)
      simp only [primeCutoffComplex,ChainComplex.of_d])
    (by
      simp only [Iso.refl_hom]
      change ModuleCat.ofHom (primeCutoffDifferential R (primeChainAugmentation R) k N) =
        (primeCutoffComplex R (primeChainAugmentation R) N).d (k+1) k
      simp only [primeCutoffComplex,ChainComplex.of_d])

/-- The adjacent-degree comparison commutes with every height inclusion. -/
def primeShortPersistenceComparison (k : ℕ) :
    primeCutoffPersistence R (primeChainAugmentation R) ⋙
      HomologicalComplex.shortComplexFunctor' (ModuleCat R) (ComplexShape.down ℕ)
        (k+2) (k+1) k ≅ primeShortPersistence R k :=
  NatIso.ofComponents (primeShortComplexComparison R k) (fun _ => by ext <;> rfl)

/-- Natural barcode coordinates for actual positive-degree homology persistence. -/
def primeHomologyCriticalIsoSucc (k : ℕ) :
    primeCutoffHomology R (primeChainAugmentation R) (k+1) ≅ primeCriticalPersistence R (k+1) :=
  Functor.isoWhiskerLeft (primeCutoffPersistence R (primeChainAugmentation R))
      (HomologicalComplex.homologyFunctorIso' (ModuleCat R) (ComplexShape.down ℕ)
        (k+2) (k+1) k (by simp) (by simp)) ≪≫
    (Functor.associator (primeCutoffPersistence R (primeChainAugmentation R))
      (HomologicalComplex.shortComplexFunctor' (ModuleCat R) (ComplexShape.down ℕ) (k+2) (k+1) k)
      (ShortComplex.homologyFunctor (ModuleCat R))).symm ≪≫
    Functor.isoWhiskerRight (primeShortPersistenceComparison R k)
      (ShortComplex.homologyFunctor (ModuleCat R)) ≪≫
    primeShortHomologyCriticalIso R k

#print axioms primeCycleCriticalProjection_ker
#print axioms primeShortHomologyEquiv
#print axioms primeHomologyCriticalIsoSucc
end GaloisForLFunctions.EffectiveScalingGeometry
