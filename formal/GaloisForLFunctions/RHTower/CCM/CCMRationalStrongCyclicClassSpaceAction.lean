import GaloisForLFunctions.RHTower.CCM.CCMRationalStrongCyclicReal
import GaloisForLFunctions.RHTower.CyclicBarAlgHomMorphism

/-!
# Class-space action on the exact CCM strong cyclic target

CCM's Lefschetz correspondence uses the multiplicative action of the idele class group on the
relative cyclic object.  For `Q`, the canonical section is a group model for `C_Q`.  This file
constructs its literal right action on the exact strong cyclic target.

The key analytic identity is algebraic after the target has been chosen correctly: translating a
continuous trace-norm field by `c` translates its main-diagonal scalar trace by `b -> b*c`.
The strong class-space Schwartz space is already proved stable under that translation, so every
cyclic degree, every simplicial map, and Connes rotation inherit the action.

No trace formula, zero spectrum, source landing, or quotient completion is assumed.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions
namespace RHTower

universe u

private abbrev Section := CCMRationalClassSpaceSection
private abbrev Field := CCMRationalContinuousTraceNormField

/-! ## Algebra-homomorphism naturality of ordered cyclic products -/

/-- Ordered multiplication of cyclic tensors is natural under every algebra homomorphism. -/
theorem cyclicBarTotalProduct_algHom
    {A B : Type u} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
    (φ : A →ₐ[ℂ] B) : ∀ n : ℕ,
    φ.toLinearMap.comp (cyclicBarTotalProduct (R := ℂ) (A := A) n) =
      (cyclicBarTotalProduct (R := ℂ) (A := B) n).comp
        (cyclicBarAlgHomDegree φ n)
  | 0 => by
      apply LinearMap.ext
      intro x
      induction x using PiTensorProduct.induction_on' with
      | tprodCoeff r f =>
          rw [PiTensorProduct.tprodCoeff_eq_smul_tprod,
            map_smul, map_smul]
          simp only [LinearMap.comp_apply]
          change
            r • φ.toLinearMap
                (cyclicBarDegreeZeroProduct
                  (PiTensorProduct.tprod ℂ f)) =
              r • cyclicBarDegreeZeroProduct
                (cyclicBarAlgHomDegree φ 0
                  (PiTensorProduct.tprod ℂ f))
          rw [cyclicBarDegreeZeroProduct_tprod,
            cyclicBarAlgHomDegree_tprod,
            cyclicBarDegreeZeroProduct_tprod]
          rfl
      | add x y hx hy =>
          simp only [map_add, hx, hy]
  | n + 1 => by
      calc
        φ.toLinearMap.comp
            ((cyclicBarTotalProduct (R := ℂ) (A := A) n).comp
              (cyclicBarFace (R := ℂ) (A := A) (0 : Fin (n + 2)))) =
          (φ.toLinearMap.comp
              (cyclicBarTotalProduct (R := ℂ) (A := A) n)).comp
            (cyclicBarFace (R := ℂ) (A := A) (0 : Fin (n + 2))) :=
              (LinearMap.comp_assoc _ _ _).symm
        _ = ((cyclicBarTotalProduct (R := ℂ) (A := B) n).comp
              (cyclicBarAlgHomDegree φ n)).comp
            (cyclicBarFace (R := ℂ) (A := A) (0 : Fin (n + 2))) := by
              rw [cyclicBarTotalProduct_algHom φ n]
        _ = (cyclicBarTotalProduct (R := ℂ) (A := B) n).comp
            ((cyclicBarAlgHomDegree φ n).comp
              (cyclicBarFace (R := ℂ) (A := A) (0 : Fin (n + 2)))) :=
              LinearMap.comp_assoc _ _ _
        _ = (cyclicBarTotalProduct (R := ℂ) (A := B) n).comp
            ((cyclicBarFace (R := ℂ) (A := B) (0 : Fin (n + 2))).comp
              (cyclicBarAlgHomDegree φ (n + 1))) := by
              rw [cyclicBarAlgHom_comp_face]
        _ = ((cyclicBarTotalProduct (R := ℂ) (A := B) n).comp
              (cyclicBarFace (R := ℂ) (A := B) (0 : Fin (n + 2)))).comp
            (cyclicBarAlgHomDegree φ (n + 1)) :=
              (LinearMap.comp_assoc _ _ _).symm

/-! ## Main-diagonal covariance -/

/-- Evaluation of point trace after right translation is evaluation at the translated point. -/
@[simp]
theorem ccmRationalContinuousTraceNormPointTrace_rightAction
    (c b : Section) (F : Field) :
    ccmRationalContinuousTraceNormPointTrace b
        (ccmRationalContinuousTraceNormFieldRightAction c F) =
      ccmRationalContinuousTraceNormPointTrace (b * c) F :=
  rfl

/-- Exact covariance of every main-diagonal cyclic trace under class-space translation. -/
theorem ccmRationalStrongDiagonalTrace_rightAction
    (c : Section) (n : ℕ) (x : CyclicBarTensor ℂ Field n) (b : Section) :
    ccmRationalStrongDiagonalTrace n
        (cyclicBarAlgHomDegree
          (ccmRationalContinuousTraceNormFieldRightActionAlgHom c) n x) b =
      ccmRationalStrongDiagonalTrace n x (b * c) := by
  have hproduct := LinearMap.congr_fun
    (cyclicBarTotalProduct_algHom
      (ccmRationalContinuousTraceNormFieldRightActionAlgHom c) n) x
  have hproduct' :
      cyclicBarTotalProduct n
          (cyclicBarAlgHomDegree
            (ccmRationalContinuousTraceNormFieldRightActionAlgHom c) n x) =
        (ccmRationalContinuousTraceNormFieldRightActionAlgHom c).toLinearMap
          (cyclicBarTotalProduct n x) := by
    simpa only [LinearMap.comp_apply] using hproduct.symm
  change
    ccmRationalContinuousTraceNormPointTrace b
        (cyclicBarTotalProduct n
          (cyclicBarAlgHomDegree
            (ccmRationalContinuousTraceNormFieldRightActionAlgHom c) n x)) =
      ccmRationalContinuousTraceNormPointTrace (b * c)
        (cyclicBarTotalProduct n x)
  rw [hproduct']
  rfl

/-- Class-space translation preserves the exact CCM strong condition in every cyclic degree. -/
theorem ccmRationalStrongCyclicObjectSubmodule_rightAction_stable
    (c : Section) (n : ℕ)
    (x : CyclicBarTensor ℂ Field n)
    (hx : x ∈ ccmRationalStrongCyclicObjectSubmodule (.mk n)) :
    cyclicBarAlgHomDegree
        (ccmRationalContinuousTraceNormFieldRightActionAlgHom c) n x ∈
      ccmRationalStrongCyclicObjectSubmodule (.mk n) := by
  change
    ccmRationalStrongDiagonalTrace n
        (cyclicBarAlgHomDegree
          (ccmRationalContinuousTraceNormFieldRightActionAlgHom c) n x) ∈
      CCMRationalStrongClassSpaceScalarTarget
  have htranslate :=
    CCMRationalStrongClassSpaceScalarTarget.rightTranslate_mem hx c
  convert htranslate using 1
  funext b
  exact ccmRationalStrongDiagonalTrace_rightAction c n x b

/-! ## Restriction to the exact strong cyclic module -/

/-- Degreewise class-space action on exact strong cyclic chains. -/
def ccmRationalStrongCyclicRightActionDegree
    (c : Section) (n : ℕ) :
    ccmRationalStrongCyclicObjectSubmodule (.mk n) →ₗ[ℂ]
      ccmRationalStrongCyclicObjectSubmodule (.mk n) :=
  ((cyclicBarAlgHomDegree
      (ccmRationalContinuousTraceNormFieldRightActionAlgHom c) n).domRestrict
        (ccmRationalStrongCyclicObjectSubmodule (.mk n))).codRestrict
    (ccmRationalStrongCyclicObjectSubmodule (.mk n)) fun x =>
      ccmRationalStrongCyclicObjectSubmodule_rightAction_stable
        c n x.1 x.2

@[simp]
theorem ccmRationalStrongCyclicRightActionDegree_coe
    (c : Section) (n : ℕ)
    (x : ccmRationalStrongCyclicObjectSubmodule (.mk n)) :
    (ccmRationalStrongCyclicRightActionDegree c n x).1 =
      cyclicBarAlgHomDegree
        (ccmRationalContinuousTraceNormFieldRightActionAlgHom c) n x.1 :=
  rfl

/-- Class-space action component at an arbitrary presented simplex object. -/
def ccmRationalStrongCyclicRightActionComponent (c : Section) :
    ∀ a : SimplexCategoryGenRel,
      ccmRationalStrongCyclicSimplicial.obj (.op a) ⟶
        ccmRationalStrongCyclicSimplicial.obj (.op a) :=
  SimplexCategoryGenRel.rec fun n =>
    ModuleCat.ofHom (ccmRationalStrongCyclicRightActionDegree c n)

@[simp]
theorem ccmRationalStrongCyclicRightActionComponent_mk
    (c : Section) (n : ℕ) :
    ccmRationalStrongCyclicRightActionComponent c (.mk n) =
      ModuleCat.ofHom (ccmRationalStrongCyclicRightActionDegree c n) :=
  rfl

/-- The restricted class-space action is natural for every presented simplicial map. -/
def ccmRationalStrongCyclicRightActionSimplicial (c : Section) :
    ccmRationalStrongCyclicSimplicial ⟶
      ccmRationalStrongCyclicSimplicial where
  app j := ccmRationalStrongCyclicRightActionComponent c j.unop
  naturality {j k} h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hambient :=
      (cyclicBarAlgHomSimplicialHom
        (ccmRationalContinuousTraceNormFieldRightActionAlgHom c)).naturality h
    exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hambient) x.1

/-- **Exact class-space action on the CCM strong cyclic target.** -/
def ccmRationalStrongCyclicRightAction (c : Section) :
    CyclicModule.Hom CCMRationalStrongCyclicTarget
      CCMRationalStrongCyclicTarget where
  simplicial := ccmRationalStrongCyclicRightActionSimplicial c
  cyclic_naturality n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hambient :=
      (cyclicBarAlgHomCyclicHom
        (ccmRationalContinuousTraceNormFieldRightActionAlgHom c)).cyclic_naturality n
    exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hambient) x.1

end RHTower
end GaloisForLFunctions
