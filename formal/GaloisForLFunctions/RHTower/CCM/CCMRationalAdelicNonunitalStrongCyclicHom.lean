import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicTwistedCyclicSource
import GaloisForLFunctions.RHTower.CCM.CCMRationalNonunitalStrongCyclicTarget
import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicTensorStrongClassSpaceLanding
import GaloisForLFunctions.RHTower.CyclicBarAlgHomMorphism

/-!
# Exact restriction into the literal nonunital CCM target

The instance-sealed twisted crossed product maps to continuous fields of
genuine trace-class operators.  Its unitization therefore maps to the single
global unitization of that nonunital field algebra.  The induced all-degree
cyclic map preserves global augmentation, and its diagonal trace is the
proved rational-orbit trace.  Hence the genuine reduced adelic source lands
in the literal Definition 4.9 double-kernel target.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions.RHTower

private abbrev Crossed :=
  CCMRationalAdelicTwistedCrossedProduct
private abbrev Source :=
  CCMRationalAdelicTwistedCyclicSourceAlgebra
private abbrev Section := CCMRationalClassSpaceSection
private abbrev IdealField :=
  CCMRationalContinuousTraceNormIdealField
private abbrev FieldUnit :=
  CCMRationalContinuousTraceNormIdealFieldUnitization

/-! ## Exact algebraic restriction -/

/-- Trace-class field representation on the instance-sealed twisted carrier. -/
def ccmRationalAdelicTwistedCrossedContinuousTraceNormHom :
    Crossed →ₙₐ[ℂ] IdealField where
  toFun F :=
    ccmRationalAdelicCrossedContinuousTraceNormHom F.toFinsupp
  map_zero' := by
    apply ContinuousMap.ext
    intro b
    exact congrFun ccmRationalAdelicCrossedTraceNormClassSection_zero b
  map_add' F G := by
    apply ContinuousMap.ext
    intro b
    exact congrFun
      (ccmRationalAdelicCrossedTraceNormClassSection_add
        F.toFinsupp G.toFinsupp) b
  map_smul' z F := by
    apply ContinuousMap.ext
    intro b
    exact congrFun
      (ccmRationalAdelicCrossedTraceNormClassSection_smul
        z F.toFinsupp) b
  map_mul' F G := by
    apply ContinuousMap.ext
    intro b
    exact congrFun
      (ccmRationalAdelicCrossedTraceNormClassSection_mul
        F.toFinsupp G.toFinsupp) b

/-- Exact algebra homomorphism from the sealed source unitization to the
target's single global unitization. -/
def ccmRationalAdelicNonunitalIdealFieldUnitizationHom :
    Source →ₐ[ℂ] FieldUnit :=
  Unitization.lift
    ((Unitization.inrNonUnitalAlgHom ℂ IdealField).comp
      ccmRationalAdelicTwistedCrossedContinuousTraceNormHom)

@[simp]
theorem ccmRationalAdelicNonunitalIdealFieldUnitizationHom_inl
    (z : ℂ) :
    ccmRationalAdelicNonunitalIdealFieldUnitizationHom
        (Unitization.inl z) = Unitization.inl z := by
  simp [ccmRationalAdelicNonunitalIdealFieldUnitizationHom]
  rw [Unitization.algebraMap_eq_inl]

@[simp]
theorem ccmRationalAdelicNonunitalIdealFieldUnitizationHom_inr
    (F : Crossed) :
    ccmRationalAdelicNonunitalIdealFieldUnitizationHom (F : Source) =
      (ccmRationalAdelicTwistedCrossedContinuousTraceNormHom F :
        FieldUnit) := by
  simp [ccmRationalAdelicNonunitalIdealFieldUnitizationHom]

/-- Evaluation of exact global-unitization restriction agrees with the
legacy pointwise restriction evaluated on the identical coefficient data. -/
theorem
    ccmRationalAdelicNonunitalIdealFieldUnitizationEvaluation_restriction
    (x : Source) (b : Section) :
    ccmRationalContinuousTraceNormIdealFieldUnitizationEvaluation b
        (ccmRationalAdelicNonunitalIdealFieldUnitizationHom x) =
      ccmRationalAdelicSourceContinuousTraceNormFieldHom
        (ccmRationalAdelicTwistedSourceToLegacy x) b := by
  induction x using Unitization.ind with
  | inl_add_inr z F =>
      simp [ccmRationalAdelicNonunitalIdealFieldUnitizationHom,
        ccmRationalAdelicTwistedCrossedContinuousTraceNormHom,
        ccmRationalAdelicTwistedSourceToLegacy,
        ccmRationalContinuousTraceNormIdealFieldUnitizationEvaluation,
        ccmRationalAdelicSourceContinuousTraceNormFieldHom,
        ccmRationalAdelicCrossedContinuousTraceNormL1Hom,
        ccmRationalContinuousTraceNormOperatorFieldInrHom,
        Unitization.algebraMap_eq_inl]
      rw [Algebra.smul_def, mul_one]
      rfl

/-- Restriction preserves the scalar part of the single global
unitizations. -/
@[simp]
theorem ccmRationalAdelicNonunitalIdealFieldUnitizationHom_fst
    (x : Source) :
    (ccmRationalAdelicNonunitalIdealFieldUnitizationHom x).fst = x.fst := by
  induction x using Unitization.ind with
  | inl_add_inr z F =>
      simp [ccmRationalAdelicNonunitalIdealFieldUnitizationHom,
        Unitization.algebraMap_eq_inl]

/-! ## Augmentation and diagonal-trace transport -/

/-- Target global cyclic augmentation after restriction is exactly source
unitization augmentation. -/
theorem ccmRationalNonunitalFieldAugmentation_restriction
    (n : ℕ) (x : CyclicBarTensor ℂ Source n) :
    cyclicBarTraceAugmentation ccmRationalNonunitalFieldAugmentation n
        (cyclicBarAlgHomDegree
          ccmRationalAdelicNonunitalIdealFieldUnitizationHom n x) =
      cyclicBarTraceAugmentation
        ccmRationalAdelicTwistedUnitizationAugmentation n x := by
  have hproduct := LinearMap.congr_fun
    (cyclicBarTotalProduct_algHom
      ccmRationalAdelicNonunitalIdealFieldUnitizationHom n) x
  have hproduct' :
      cyclicBarTotalProduct n
          (cyclicBarAlgHomDegree
            ccmRationalAdelicNonunitalIdealFieldUnitizationHom n x) =
        ccmRationalAdelicNonunitalIdealFieldUnitizationHom
          (cyclicBarTotalProduct n x) := by
    change _ =
      ccmRationalAdelicNonunitalIdealFieldUnitizationHom.toLinearMap
        (cyclicBarTotalProduct n x)
    simpa only [LinearMap.comp_apply] using hproduct.symm
  change
    (cyclicBarTotalProduct n
      (cyclicBarAlgHomDegree
        ccmRationalAdelicNonunitalIdealFieldUnitizationHom n x)).fst =
      (cyclicBarTotalProduct n x).fst
  rw [hproduct']
  exact ccmRationalAdelicNonunitalIdealFieldUnitizationHom_fst _

/-- New target diagonal trace is precisely the established adelic
class-space orbit trace of the identical coefficient data. -/
theorem ccmRationalNonunitalStrongDiagonalTrace_restriction
    (n : ℕ) (x : CyclicBarTensor ℂ Source n) :
    ccmRationalNonunitalStrongDiagonalTrace n
        (cyclicBarAlgHomDegree
          ccmRationalAdelicNonunitalIdealFieldUnitizationHom n x) =
      ccmRationalAdelicSourceClassSpaceTrace
        (ccmRationalAdelicTwistedSourceToLegacy
          (cyclicBarTotalProduct n x)) := by
  funext b
  have hproduct := LinearMap.congr_fun
    (cyclicBarTotalProduct_algHom
      ccmRationalAdelicNonunitalIdealFieldUnitizationHom n) x
  have hproduct' :
      cyclicBarTotalProduct n
          (cyclicBarAlgHomDegree
            ccmRationalAdelicNonunitalIdealFieldUnitizationHom n x) =
        ccmRationalAdelicNonunitalIdealFieldUnitizationHom
          (cyclicBarTotalProduct n x) := by
    change _ =
      ccmRationalAdelicNonunitalIdealFieldUnitizationHom.toLinearMap
        (cyclicBarTotalProduct n x)
    simpa only [LinearMap.comp_apply] using hproduct.symm
  change ccmRationalNonunitalFieldPointTrace b
      (cyclicBarTotalProduct n
        (cyclicBarAlgHomDegree
          ccmRationalAdelicNonunitalIdealFieldUnitizationHom n x)) = _
  rw [hproduct', ccmRationalNonunitalFieldPointTrace_apply,
    ccmRationalAdelicNonunitalIdealFieldUnitizationEvaluation_restriction]
  rfl

/-- Degree-zero strong landing transported across the additive carrier
identification.  Multiplication has already happened in the sealed source. -/
theorem ccmRationalAdelicTwisted_sourceClassSpaceTrace_mem_strong_of_endpoints
    (y : Source)
    (hscalar : y.fst = 0)
    (hzero : ccmRationalAdelicTwistedEpsilonZero y = 0)
    (hone : ccmRationalAdelicTwistedEpsilonOne y = 0) :
    ccmRationalAdelicSourceClassSpaceTrace
        (ccmRationalAdelicTwistedSourceToLegacy y) ∈
      CCMRationalStrongClassSpaceScalarTarget := by
  apply ccmRationalAdelic_sourceClassSpaceTrace_mem_strong_of_endpoints
  · simpa using hscalar
  · simpa using hzero
  · simpa using hone

/-! ## Exact cyclic restriction -/

/-- Ambient cyclic restriction into the globally unitized ideal-field bar. -/
def ccmRationalAdelicReducedNonunitalIdealFieldUnitizedCyclicHom :
    CyclicModule.Hom CCMRationalAdelicTwistedReducedSourceCyclicModule
      CCMRationalContinuousTraceNormIdealFieldUnitizedCyclicModule :=
  CyclicModule.Hom.comp
    ccmRationalAdelicTwistedReducedSourceCyclicInclusion
    (cyclicBarAlgHomCyclicHom
      ccmRationalAdelicNonunitalIdealFieldUnitizationHom)

/-- Exact strong landing of every chain in the sealed reduced source. -/
theorem ccmRationalAdelicTwisted_reduced_source_image_mem_strong
    (n : ℕ)
    (x : CCMRationalAdelicTwistedReducedSourceCyclicModule.simplicial.degree n) :
    ccmRationalNonunitalStrongDiagonalTrace n
        (cyclicBarAlgHomDegree
          ccmRationalAdelicNonunitalIdealFieldUnitizationHom n x.1.1) ∈
      CCMRationalStrongClassSpaceScalarTarget := by
  rw [ccmRationalNonunitalStrongDiagonalTrace_restriction]
  apply ccmRationalAdelicTwisted_sourceClassSpaceTrace_mem_strong_of_endpoints
  · have haug := x.1.2.1
    change cyclicBarTraceAugmentation
      ccmRationalAdelicTwistedUnitizationAugmentation n x.1.1 = 0 at haug
    exact haug
  · have hx0 := x.2.1
    change cyclicBarTraceAugmentation
      ccmRationalAdelicTwistedEpsilonZero n x.1.1 = 0 at hx0
    exact hx0
  · have hx1 := x.2.2
    change cyclicBarTraceAugmentation
      ccmRationalAdelicTwistedEpsilonOne n x.1.1 = 0 at hx1
    exact hx1

/-- Degreewise exact restriction into literal Definition 4.9 target. -/
def ccmRationalAdelicReducedNonunitalStrongCyclicDegree (n : ℕ) :
    CCMRationalAdelicTwistedReducedSourceCyclicModule.simplicial.degree n →ₗ[ℂ]
      CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n where
  toFun x :=
    ⟨cyclicBarAlgHomDegree
        ccmRationalAdelicNonunitalIdealFieldUnitizationHom n x.1.1,
      (mem_ccmRationalNonunitalStrongCyclicTarget_iff n _).mpr ⟨by
        rw [ccmRationalNonunitalFieldAugmentation_restriction]
        exact x.1.2.1,
        ccmRationalAdelicTwisted_reduced_source_image_mem_strong n x⟩⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add
      (cyclicBarAlgHomDegree
        ccmRationalAdelicNonunitalIdealFieldUnitizationHom n) x.1.1 y.1.1
  map_smul' z x := by
    apply Subtype.ext
    exact map_smul
      (cyclicBarAlgHomDegree
        ccmRationalAdelicNonunitalIdealFieldUnitizationHom n) z x.1.1

@[simp]
theorem ccmRationalAdelicReducedNonunitalStrongCyclicDegree_coe
    (n : ℕ)
    (x : CCMRationalAdelicTwistedReducedSourceCyclicModule.simplicial.degree n) :
    (ccmRationalAdelicReducedNonunitalStrongCyclicDegree n x).1 =
      cyclicBarAlgHomDegree
        ccmRationalAdelicNonunitalIdealFieldUnitizationHom n x.1.1 :=
  rfl

/-- Component of exact restriction at an arbitrary presented simplex. -/
def ccmRationalAdelicReducedNonunitalStrongCyclicComponent :
    ∀ j : SimplexCategoryGenRelᵒᵖ,
      CCMRationalAdelicTwistedReducedSourceCyclicModule.simplicial.obj j ⟶
        CCMRationalNonunitalStrongCyclicTarget.simplicial.obj j
  | .op (.mk n) =>
      ModuleCat.ofHom
        (ccmRationalAdelicReducedNonunitalStrongCyclicDegree n)

/-- Simplicial exact restriction into Definition 4.9. -/
def ccmRationalAdelicReducedNonunitalStrongCyclicSimplicialHom :
    CCMRationalAdelicTwistedReducedSourceCyclicModule.simplicial ⟶
      CCMRationalNonunitalStrongCyclicTarget.simplicial where
  app := ccmRationalAdelicReducedNonunitalStrongCyclicComponent
  naturality {j k} g := by
    rcases j with ⟨⟨j⟩⟩
    rcases k with ⟨⟨k⟩⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have h :=
      ccmRationalAdelicReducedNonunitalIdealFieldUnitizedCyclicHom.simplicial.naturality g
    exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp h) x

/-- **Exact full restriction to literal CCM Definition 4.9.** -/
def ccmRationalAdelicReducedNonunitalStrongCyclicHom :
    CyclicModule.Hom CCMRationalAdelicTwistedReducedSourceCyclicModule
      CCMRationalNonunitalStrongCyclicTarget where
  simplicial :=
    ccmRationalAdelicReducedNonunitalStrongCyclicSimplicialHom
  cyclic_naturality n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have h :=
      ccmRationalAdelicReducedNonunitalIdealFieldUnitizedCyclicHom.cyclic_naturality n
    exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp h) x

end GaloisForLFunctions.RHTower
