import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicNonunitalStrongCyclicHom
import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicReducedSourceClassSpaceAction

/-!
# Class-space action on the literal nonunital CCM cyclic target

Right translation acts on the nonunital ideal-field algebra before its one
global unit is adjoined.  It preserves global augmentation and transports the
module-valued diagonal trace by class-space pullback.  The same action is
constructed on the instance-sealed twisted adelic source, where both endpoint
kernels are preserved.  Exact restriction is equivariant as an equality of
cyclic chains.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions.RHTower

private abbrev Section := CCMRationalClassSpaceSection
private abbrev IdealField :=
  CCMRationalContinuousTraceNormIdealField
private abbrev FieldUnit :=
  CCMRationalContinuousTraceNormIdealFieldUnitization
private abbrev Crossed :=
  CCMRationalAdelicTwistedCrossedProduct
private abbrev Source :=
  CCMRationalAdelicTwistedCyclicSourceAlgebra

/-! ## Target action -/

/-- Right pullback on continuous fields in the genuine trace-class ideal. -/
def ccmRationalContinuousTraceNormIdealFieldRightAction
    (c : Section) (F : IdealField) : IdealField where
  toFun b := F (b * c)
  continuous_toFun :=
    F.continuous.comp (continuous_id.mul continuous_const)

@[simp]
theorem ccmRationalContinuousTraceNormIdealFieldRightAction_apply
    (c b : Section) (F : IdealField) :
    ccmRationalContinuousTraceNormIdealFieldRightAction c F b = F (b * c) :=
  rfl

/-- Right pullback as a nonunital algebra endomorphism of ideal fields. -/
def ccmRationalContinuousTraceNormIdealFieldRightActionHom
    (c : Section) : IdealField →ₙₐ[ℂ] IdealField where
  toFun := ccmRationalContinuousTraceNormIdealFieldRightAction c
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mul' _ _ := rfl

/-- Unital extension of ideal-field translation to the one global
unitization. -/
def ccmRationalNonunitalFieldRightActionAlgHom
    (c : Section) : FieldUnit →ₐ[ℂ] FieldUnit :=
  Unitization.lift
    ((Unitization.inrNonUnitalAlgHom ℂ IdealField).comp
      (ccmRationalContinuousTraceNormIdealFieldRightActionHom c))

@[simp]
theorem ccmRationalNonunitalFieldRightActionAlgHom_fst
    (c : Section) (x : FieldUnit) :
    (ccmRationalNonunitalFieldRightActionAlgHom c x).fst = x.fst := by
  induction x using Unitization.ind with
  | inl_add_inr z F =>
      simp [ccmRationalNonunitalFieldRightActionAlgHom,
        Unitization.algebraMap_eq_inl]

@[simp]
theorem ccmRationalNonunitalFieldRightActionAlgHom_snd
    (c : Section) (x : FieldUnit) :
    (ccmRationalNonunitalFieldRightActionAlgHom c x).snd =
      ccmRationalContinuousTraceNormIdealFieldRightAction c x.snd := by
  induction x using Unitization.ind with
  | inl_add_inr z F =>
      simp [ccmRationalNonunitalFieldRightActionAlgHom,
        Unitization.algebraMap_eq_inl]
      rfl

theorem
    ccmRationalContinuousTraceNormIdealFieldUnitizationEvaluation_rightAction
    (c b : Section) (x : FieldUnit) :
    ccmRationalContinuousTraceNormIdealFieldUnitizationEvaluation b
        (ccmRationalNonunitalFieldRightActionAlgHom c x) =
      ccmRationalContinuousTraceNormIdealFieldUnitizationEvaluation (b * c) x := by
  induction x using Unitization.ind with
  | inl_add_inr z F =>
      simp [ccmRationalNonunitalFieldRightActionAlgHom,
        ccmRationalContinuousTraceNormIdealFieldUnitizationEvaluation,
        Unitization.algebraMap_eq_inl]
      rfl

theorem ccmRationalNonunitalFieldPointTrace_rightAction
    (c b : Section) (x : FieldUnit) :
    ccmRationalNonunitalFieldPointTrace b
        (ccmRationalNonunitalFieldRightActionAlgHom c x) =
      ccmRationalNonunitalFieldPointTrace (b * c) x := by
  rw [ccmRationalNonunitalFieldPointTrace_apply,
    ccmRationalNonunitalFieldPointTrace_apply,
    ccmRationalContinuousTraceNormIdealFieldUnitizationEvaluation_rightAction]

theorem ccmRationalNonunitalStrongDiagonalTrace_rightAction
    (c : Section) (n : ℕ) (x : CyclicBarTensor ℂ FieldUnit n) :
    ccmRationalNonunitalStrongDiagonalTrace n
        (cyclicBarAlgHomDegree
          (ccmRationalNonunitalFieldRightActionAlgHom c) n x) =
      fun b => ccmRationalNonunitalStrongDiagonalTrace n x (b * c) := by
  funext b
  have hproduct := LinearMap.congr_fun
    (cyclicBarTotalProduct_algHom
      (ccmRationalNonunitalFieldRightActionAlgHom c) n) x
  have hproduct' :
      cyclicBarTotalProduct n
          (cyclicBarAlgHomDegree
            (ccmRationalNonunitalFieldRightActionAlgHom c) n x) =
        ccmRationalNonunitalFieldRightActionAlgHom c
          (cyclicBarTotalProduct n x) := by
    change _ =
      (ccmRationalNonunitalFieldRightActionAlgHom c).toLinearMap
        (cyclicBarTotalProduct n x)
    simpa only [LinearMap.comp_apply] using hproduct.symm
  change ccmRationalNonunitalFieldPointTrace b
      (cyclicBarTotalProduct n
        (cyclicBarAlgHomDegree
          (ccmRationalNonunitalFieldRightActionAlgHom c) n x)) = _
  rw [hproduct', ccmRationalNonunitalFieldPointTrace_rightAction]
  rfl

theorem ccmRationalNonunitalFieldAugmentation_rightAction
    (c : Section) (n : ℕ) (x : CyclicBarTensor ℂ FieldUnit n) :
    cyclicBarTraceAugmentation ccmRationalNonunitalFieldAugmentation n
        (cyclicBarAlgHomDegree
          (ccmRationalNonunitalFieldRightActionAlgHom c) n x) =
      cyclicBarTraceAugmentation
        ccmRationalNonunitalFieldAugmentation n x := by
  have hproduct := LinearMap.congr_fun
    (cyclicBarTotalProduct_algHom
      (ccmRationalNonunitalFieldRightActionAlgHom c) n) x
  have hproduct' :
      cyclicBarTotalProduct n
          (cyclicBarAlgHomDegree
            (ccmRationalNonunitalFieldRightActionAlgHom c) n x) =
        ccmRationalNonunitalFieldRightActionAlgHom c
          (cyclicBarTotalProduct n x) := by
    change _ =
      (ccmRationalNonunitalFieldRightActionAlgHom c).toLinearMap
        (cyclicBarTotalProduct n x)
    simpa only [LinearMap.comp_apply] using hproduct.symm
  change (cyclicBarTotalProduct n
      (cyclicBarAlgHomDegree
        (ccmRationalNonunitalFieldRightActionAlgHom c) n x)).fst =
    (cyclicBarTotalProduct n x).fst
  rw [hproduct', ccmRationalNonunitalFieldRightActionAlgHom_fst]

/-- Degreewise class-space action on literal nonunital strong chains. -/
def ccmRationalNonunitalStrongCyclicRightActionDegree
    (c : Section) (n : ℕ) :
    CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n →ₗ[ℂ]
      CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n where
  toFun x :=
    ⟨cyclicBarAlgHomDegree
        (ccmRationalNonunitalFieldRightActionAlgHom c) n x.1,
      (mem_ccmRationalNonunitalStrongCyclicTarget_iff n _).mpr ⟨by
        rw [ccmRationalNonunitalFieldAugmentation_rightAction]
        exact
          (mem_ccmRationalNonunitalStrongCyclicTarget_iff n x.1).mp x.2 |>.1,
        by
          rw [ccmRationalNonunitalStrongDiagonalTrace_rightAction]
          exact CCMRationalStrongClassSpaceScalarTarget.rightTranslate_mem
            ((mem_ccmRationalNonunitalStrongCyclicTarget_iff n x.1).mp x.2 |>.2)
            c⟩⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add
      (cyclicBarAlgHomDegree
        (ccmRationalNonunitalFieldRightActionAlgHom c) n) x.1 y.1
  map_smul' z x := by
    apply Subtype.ext
    exact map_smul
      (cyclicBarAlgHomDegree
        (ccmRationalNonunitalFieldRightActionAlgHom c) n) z x.1

@[simp]
theorem ccmRationalNonunitalStrongCyclicRightActionDegree_coe
    (c : Section) (n : ℕ)
    (x : CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n) :
    (ccmRationalNonunitalStrongCyclicRightActionDegree c n x).1 =
      cyclicBarAlgHomDegree
        (ccmRationalNonunitalFieldRightActionAlgHom c) n x.1 :=
  rfl

def ccmRationalNonunitalStrongCyclicRightActionComponent
    (c : Section) : ∀ a : SimplexCategoryGenRel,
    CCMRationalNonunitalStrongCyclicTarget.simplicial.obj (.op a) ⟶
      CCMRationalNonunitalStrongCyclicTarget.simplicial.obj (.op a) :=
  SimplexCategoryGenRel.rec fun n =>
    ModuleCat.ofHom
      (ccmRationalNonunitalStrongCyclicRightActionDegree c n)

def ccmRationalNonunitalStrongCyclicRightActionSimplicial
    (c : Section) :
    CCMRationalNonunitalStrongCyclicTarget.simplicial ⟶
      CCMRationalNonunitalStrongCyclicTarget.simplicial where
  app j := ccmRationalNonunitalStrongCyclicRightActionComponent c j.unop
  naturality {j k} h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hambient :=
      (cyclicBarAlgHomSimplicialHom
        (ccmRationalNonunitalFieldRightActionAlgHom c)).naturality h
    exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hambient) x.1

/-- Exact class-space action on literal CCM Definition 4.9. -/
def ccmRationalNonunitalStrongCyclicRightAction (c : Section) :
    CyclicModule.Hom CCMRationalNonunitalStrongCyclicTarget
      CCMRationalNonunitalStrongCyclicTarget where
  simplicial := ccmRationalNonunitalStrongCyclicRightActionSimplicial c
  cyclic_naturality n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hambient :=
      (cyclicBarAlgHomCyclicHom
        (ccmRationalNonunitalFieldRightActionAlgHom c)).cyclic_naturality n
    exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hambient) x.1

/-! ## Source action -/

/-- Coefficient pullback on the sealed twisted crossed product. -/
def ccmRationalAdelicTwistedCrossedClassSpaceRightActionHom
    (c : Section) : Crossed →ₙₐ[ℂ] Crossed where
  toFun F :=
    ⟨ccmRationalAdelicCrossedClassSpaceRightAction c F.toFinsupp⟩
  map_zero' := by
    apply CCMRationalAdelicTwistedCrossedProduct.ext
    exact ccmRationalAdelicCrossedClassSpaceRightAction_zero c
  map_add' F G := by
    apply CCMRationalAdelicTwistedCrossedProduct.ext
    exact ccmRationalAdelicCrossedClassSpaceRightAction_add
      c F.toFinsupp G.toFinsupp
  map_smul' z F := by
    apply CCMRationalAdelicTwistedCrossedProduct.ext
    exact ccmRationalAdelicCrossedClassSpaceRightAction_smul
      c z F.toFinsupp
  map_mul' F G := by
    apply CCMRationalAdelicTwistedCrossedProduct.ext
    exact ccmRationalAdelicCrossedClassSpaceRightAction_mul
      c F.toFinsupp G.toFinsupp

/-- Unital class-space action on the sealed cyclic source algebra. -/
def ccmRationalAdelicTwistedSourceClassSpaceRightActionHom
    (c : Section) : Source →ₐ[ℂ] Source :=
  Unitization.lift
    ((Unitization.inrNonUnitalAlgHom ℂ Crossed).comp
      (ccmRationalAdelicTwistedCrossedClassSpaceRightActionHom c))

@[simp]
theorem ccmRationalAdelicTwistedSourceClassSpaceRightActionHom_fst
    (c : Section) (x : Source) :
    (ccmRationalAdelicTwistedSourceClassSpaceRightActionHom c x).fst =
      x.fst := by
  induction x using Unitization.ind with
  | inl_add_inr z F =>
      simp [ccmRationalAdelicTwistedSourceClassSpaceRightActionHom,
        Unitization.algebraMap_eq_inl]

@[simp]
theorem ccmRationalAdelicTwistedSourceClassSpaceRightActionHom_snd
    (c : Section) (x : Source) :
    (ccmRationalAdelicTwistedSourceClassSpaceRightActionHom c x).snd.toFinsupp =
      ccmRationalAdelicCrossedClassSpaceRightAction c x.snd.toFinsupp := by
  induction x using Unitization.ind with
  | inl_add_inr z F =>
      simp [ccmRationalAdelicTwistedSourceClassSpaceRightActionHom,
        Unitization.algebraMap_eq_inl]
      rfl

theorem ccmRationalAdelicTwistedEpsilonZero_classSpaceRightAction
    (c : Section) (x : Source) :
    ccmRationalAdelicTwistedEpsilonZero
        (ccmRationalAdelicTwistedSourceClassSpaceRightActionHom c x) =
      ccmRationalAdelicTwistedEpsilonZero x := by
  change (ccmRationalAdelicTwistedSourceClassSpaceRightActionHom c x).fst +
      ccmRationalAdelicEpsilonZeroNonunital
        (ccmRationalAdelicTwistedSourceClassSpaceRightActionHom c x).snd.toFinsupp =
    x.fst + ccmRationalAdelicEpsilonZeroNonunital x.snd.toFinsupp
  rw [ccmRationalAdelicTwistedSourceClassSpaceRightActionHom_fst,
    ccmRationalAdelicTwistedSourceClassSpaceRightActionHom_snd,
    ccmRationalAdelicEpsilonZeroNonunital_classSpaceRightAction]

theorem ccmRationalAdelicTwistedEpsilonOne_classSpaceRightAction
    (c : Section) (x : Source) :
    ccmRationalAdelicTwistedEpsilonOne
        (ccmRationalAdelicTwistedSourceClassSpaceRightActionHom c x) =
      x.fst + ((c.2.val : ℝ)⁻¹) •
        ccmRationalAdelicTwistedEpsilonOneNonunital x.snd := by
  change (ccmRationalAdelicTwistedSourceClassSpaceRightActionHom c x).fst +
      ccmRationalAdelicEpsilonOneNonunital
        (ccmRationalAdelicTwistedSourceClassSpaceRightActionHom c x).snd.toFinsupp = _
  rw [ccmRationalAdelicTwistedSourceClassSpaceRightActionHom_fst,
    ccmRationalAdelicTwistedSourceClassSpaceRightActionHom_snd,
    ccmRationalAdelicEpsilonOneNonunital_classSpaceRightAction]
  rfl

/-- Cyclic-bar action on the sealed full source. -/
def ccmRationalAdelicTwistedSourceCyclicClassSpaceRightAction
    (c : Section) :
    CyclicModule.Hom CCMRationalAdelicTwistedSourceCyclicModule
      CCMRationalAdelicTwistedSourceCyclicModule :=
  cyclicBarAlgHomCyclicHom
    (ccmRationalAdelicTwistedSourceClassSpaceRightActionHom c)

theorem ccmRationalAdelicTwistedTotalProduct_classSpaceRightAction
    (c : Section) (n : ℕ) (x : CyclicBarTensor ℂ Source n) :
    cyclicBarTotalProduct n
        (cyclicBarAlgHomDegree
          (ccmRationalAdelicTwistedSourceClassSpaceRightActionHom c) n x) =
      ccmRationalAdelicTwistedSourceClassSpaceRightActionHom c
        (cyclicBarTotalProduct n x) := by
  have h := LinearMap.congr_fun
    (cyclicBarTotalProduct_algHom
      (ccmRationalAdelicTwistedSourceClassSpaceRightActionHom c) n) x
  change _ =
    (ccmRationalAdelicTwistedSourceClassSpaceRightActionHom c).toLinearMap
      (cyclicBarTotalProduct n x)
  simpa only [LinearMap.comp_apply] using h.symm

theorem ccmRationalAdelicTwistedUnitizationAugmentation_classSpaceRightAction
    (c : Section) (n : ℕ) (x : CyclicBarTensor ℂ Source n) :
    cyclicBarTraceAugmentation
        ccmRationalAdelicTwistedUnitizationAugmentation n
        (cyclicBarAlgHomDegree
          (ccmRationalAdelicTwistedSourceClassSpaceRightActionHom c) n x) =
      cyclicBarTraceAugmentation
        ccmRationalAdelicTwistedUnitizationAugmentation n x := by
  change (cyclicBarTotalProduct n
      (cyclicBarAlgHomDegree
        (ccmRationalAdelicTwistedSourceClassSpaceRightActionHom c) n x)).fst =
    (cyclicBarTotalProduct n x).fst
  rw [ccmRationalAdelicTwistedTotalProduct_classSpaceRightAction,
    ccmRationalAdelicTwistedSourceClassSpaceRightActionHom_fst]

theorem ccmRationalAdelicTwistedEpsilonZeroCyclic_classSpaceRightAction
    (c : Section) (n : ℕ) (x : CyclicBarTensor ℂ Source n) :
    cyclicBarTraceAugmentation ccmRationalAdelicTwistedEpsilonZero n
        (cyclicBarAlgHomDegree
          (ccmRationalAdelicTwistedSourceClassSpaceRightActionHom c) n x) =
      cyclicBarTraceAugmentation ccmRationalAdelicTwistedEpsilonZero n x := by
  change ccmRationalAdelicTwistedEpsilonZero
      (cyclicBarTotalProduct n
        (cyclicBarAlgHomDegree
          (ccmRationalAdelicTwistedSourceClassSpaceRightActionHom c) n x)) = _
  rw [ccmRationalAdelicTwistedTotalProduct_classSpaceRightAction,
    ccmRationalAdelicTwistedEpsilonZero_classSpaceRightAction]
  rfl

theorem
    ccmRationalAdelicTwistedEpsilonOneCyclic_classSpaceRightAction_of_nonunital
    (c : Section) (n : ℕ) (x : CyclicBarTensor ℂ Source n)
    (hx : cyclicBarTraceAugmentation
      ccmRationalAdelicTwistedUnitizationAugmentation n x = 0) :
    cyclicBarTraceAugmentation ccmRationalAdelicTwistedEpsilonOne n
        (cyclicBarAlgHomDegree
          (ccmRationalAdelicTwistedSourceClassSpaceRightActionHom c) n x) =
      ((c.2.val : ℝ)⁻¹) •
        cyclicBarTraceAugmentation ccmRationalAdelicTwistedEpsilonOne n x := by
  have hfst : (cyclicBarTotalProduct n x).fst = 0 := hx
  change ccmRationalAdelicTwistedEpsilonOne
      (cyclicBarTotalProduct n
        (cyclicBarAlgHomDegree
          (ccmRationalAdelicTwistedSourceClassSpaceRightActionHom c) n x)) = _
  rw [ccmRationalAdelicTwistedTotalProduct_classSpaceRightAction,
    ccmRationalAdelicTwistedEpsilonOne_classSpaceRightAction]
  change (cyclicBarTotalProduct n x).fst +
      ((c.2.val : ℝ)⁻¹) •
        ccmRationalAdelicTwistedEpsilonOneNonunital
          (cyclicBarTotalProduct n x).snd =
    ((c.2.val : ℝ)⁻¹) •
      ((cyclicBarTotalProduct n x).fst +
        ccmRationalAdelicTwistedEpsilonOneNonunital
          (cyclicBarTotalProduct n x).snd)
  rw [hfst]
  simp

/-- Action on the sealed nonunital source cyclic module. -/
def ccmRationalAdelicTwistedNonunitalSourceCyclicClassSpaceRightAction
    (c : Section) :
    CyclicModule.Hom
      CCMRationalAdelicTwistedNonunitalSourceCyclicModule
      CCMRationalAdelicTwistedNonunitalSourceCyclicModule :=
  ccmRationalAdelicTwistedUnitizationAugmentationCyclicHom.doubleKernelEnd
    ccmRationalAdelicTwistedUnitizationAugmentationCyclicHom
    (ccmRationalAdelicTwistedSourceCyclicClassSpaceRightAction c)
    (fun n x hx => by
      change cyclicBarTraceAugmentation
        ccmRationalAdelicTwistedUnitizationAugmentation n
        (cyclicBarAlgHomDegree
          (ccmRationalAdelicTwistedSourceClassSpaceRightActionHom c) n x) = 0
      rw [ccmRationalAdelicTwistedUnitizationAugmentation_classSpaceRightAction]
      exact hx)
    (fun n x hx => by
      change cyclicBarTraceAugmentation
        ccmRationalAdelicTwistedUnitizationAugmentation n
        (cyclicBarAlgHomDegree
          (ccmRationalAdelicTwistedSourceClassSpaceRightActionHom c) n x) = 0
      rw [ccmRationalAdelicTwistedUnitizationAugmentation_classSpaceRightAction]
      exact hx)

theorem ccmRationalAdelicTwistedNonunitalEpsilonZero_kernel_preserved
    (c : Section) (n : ℕ)
    (x : CCMRationalAdelicTwistedNonunitalSourceCyclicModule.simplicial.degree n)
    (hx : ccmRationalAdelicTwistedNonunitalEpsilonZeroCyclicHom.simplicial.app
      (.op (.mk n)) x = 0) :
    ccmRationalAdelicTwistedNonunitalEpsilonZeroCyclicHom.simplicial.app
        (.op (.mk n))
        ((ccmRationalAdelicTwistedNonunitalSourceCyclicClassSpaceRightAction c).simplicial.app
          (.op (.mk n)) x) = 0 := by
  change cyclicBarTraceAugmentation ccmRationalAdelicTwistedEpsilonZero n
      (cyclicBarAlgHomDegree
        (ccmRationalAdelicTwistedSourceClassSpaceRightActionHom c) n x.1) = 0
  rw [ccmRationalAdelicTwistedEpsilonZeroCyclic_classSpaceRightAction]
  exact hx

theorem ccmRationalAdelicTwistedNonunitalEpsilonOne_kernel_preserved
    (c : Section) (n : ℕ)
    (x : CCMRationalAdelicTwistedNonunitalSourceCyclicModule.simplicial.degree n)
    (hx : ccmRationalAdelicTwistedNonunitalEpsilonOneCyclicHom.simplicial.app
      (.op (.mk n)) x = 0) :
    ccmRationalAdelicTwistedNonunitalEpsilonOneCyclicHom.simplicial.app
        (.op (.mk n))
        ((ccmRationalAdelicTwistedNonunitalSourceCyclicClassSpaceRightAction c).simplicial.app
          (.op (.mk n)) x) = 0 := by
  have hnon := x.2.1
  change cyclicBarTraceAugmentation ccmRationalAdelicTwistedEpsilonOne n
      (cyclicBarAlgHomDegree
        (ccmRationalAdelicTwistedSourceClassSpaceRightActionHom c) n x.1) = 0
  rw [ccmRationalAdelicTwistedEpsilonOneCyclic_classSpaceRightAction_of_nonunital
    c n x.1 hnon]
  change ((c.2.val : ℝ)⁻¹) •
      ccmRationalAdelicTwistedNonunitalEpsilonOneCyclicHom.simplicial.app
        (.op (.mk n)) x = 0
  rw [hx, smul_zero]

/-- Exact class-space action on the sealed reduced source. -/
def ccmRationalAdelicTwistedReducedSourceCyclicClassSpaceRightAction
    (c : Section) :
    CyclicModule.Hom CCMRationalAdelicTwistedReducedSourceCyclicModule
      CCMRationalAdelicTwistedReducedSourceCyclicModule :=
  ccmRationalAdelicTwistedNonunitalEpsilonZeroCyclicHom.doubleKernelEnd
    ccmRationalAdelicTwistedNonunitalEpsilonOneCyclicHom
    (ccmRationalAdelicTwistedNonunitalSourceCyclicClassSpaceRightAction c)
    (ccmRationalAdelicTwistedNonunitalEpsilonZero_kernel_preserved c)
    (ccmRationalAdelicTwistedNonunitalEpsilonOne_kernel_preserved c)

/-! ## Restriction equivariance -/

theorem ccmRationalAdelicTwistedCrossedContinuousTraceNormHom_rightAction
    (c : Section) (F : Crossed) :
    ccmRationalAdelicTwistedCrossedContinuousTraceNormHom
        (ccmRationalAdelicTwistedCrossedClassSpaceRightActionHom c F) =
      ccmRationalContinuousTraceNormIdealFieldRightAction c
        (ccmRationalAdelicTwistedCrossedContinuousTraceNormHom F) := by
  apply ContinuousMap.ext
  intro b
  let hb : (((b.2.val : NNReal) : ℝ)) ≠ 0 := by
    exact ne_of_gt (by
      exact_mod_cast (pos_iff_ne_zero.mpr b.2.ne_zero : 0 < b.2.val))
  let hbc : (((b.2.val : NNReal) : ℝ) * (c.2.val : ℝ)) ≠ 0 :=
    mul_ne_zero hb (by
      exact ne_of_gt (by
        exact_mod_cast (pos_iff_ne_zero.mpr c.2.ne_zero : 0 < c.2.val)))
  change ccmRationalAdelicMoritaTraceNormHom hb b.1.val
      (ccmRationalAdelicCrossedClassSpaceRightAction c F.toFinsupp) =
    ccmRationalAdelicMoritaTraceNormHom _ (b.1.val * c.1.val)
      F.toFinsupp
  exact ccmRationalAdelicMoritaTraceNormHom_classSpaceRightAction
    c F.toFinsupp hb b.1.val hbc

theorem ccmRationalAdelicNonunitalIdealFieldUnitizationHom_rightAction
    (c : Section) (x : Source) :
    ccmRationalAdelicNonunitalIdealFieldUnitizationHom
        (ccmRationalAdelicTwistedSourceClassSpaceRightActionHom c x) =
      ccmRationalNonunitalFieldRightActionAlgHom c
        (ccmRationalAdelicNonunitalIdealFieldUnitizationHom x) := by
  induction x using Unitization.ind with
  | inl_add_inr z F =>
      simp [ccmRationalAdelicNonunitalIdealFieldUnitizationHom,
        ccmRationalAdelicTwistedSourceClassSpaceRightActionHom,
        ccmRationalNonunitalFieldRightActionAlgHom,
        Unitization.algebraMap_eq_inl,
        ccmRationalAdelicTwistedCrossedContinuousTraceNormHom_rightAction]
      rfl

/-- Exact restriction intertwines sealed-source and literal-target
class-space actions in every cyclic degree. -/
theorem ccmRationalAdelicReducedNonunitalStrongCyclicHom_classSpaceRightAction
    (c : Section) (n : ℕ)
    (x : CCMRationalAdelicTwistedReducedSourceCyclicModule.simplicial.degree n) :
    ccmRationalAdelicReducedNonunitalStrongCyclicHom.simplicial.app
        (.op (.mk n))
        ((ccmRationalAdelicTwistedReducedSourceCyclicClassSpaceRightAction c).simplicial.app
          (.op (.mk n)) x) =
      (ccmRationalNonunitalStrongCyclicRightAction c).simplicial.app
        (.op (.mk n))
        (ccmRationalAdelicReducedNonunitalStrongCyclicHom.simplicial.app
          (.op (.mk n)) x) := by
  apply Subtype.ext
  change cyclicBarAlgHomDegree
      ccmRationalAdelicNonunitalIdealFieldUnitizationHom n
      (cyclicBarAlgHomDegree
        (ccmRationalAdelicTwistedSourceClassSpaceRightActionHom c) n x.1.1) =
    cyclicBarAlgHomDegree
      (ccmRationalNonunitalFieldRightActionAlgHom c) n
      (cyclicBarAlgHomDegree
        ccmRationalAdelicNonunitalIdealFieldUnitizationHom n x.1.1)
  rw [← cyclicBarAlgHomDegree_comp, ← cyclicBarAlgHomDegree_comp]
  have hAlg :
      ccmRationalAdelicNonunitalIdealFieldUnitizationHom.comp
          (ccmRationalAdelicTwistedSourceClassSpaceRightActionHom c) =
        (ccmRationalNonunitalFieldRightActionAlgHom c).comp
          ccmRationalAdelicNonunitalIdealFieldUnitizationHom := by
    apply AlgHom.ext
    intro y
    exact ccmRationalAdelicNonunitalIdealFieldUnitizationHom_rightAction c y
  rw [hAlg]

end GaloisForLFunctions.RHTower
