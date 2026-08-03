import GaloisForLFunctions.RHTower.CCMRationalContinuousTraceNormField
import GaloisForLFunctions.RHTower.CCMRationalStrongClassSpace
import GaloisForLFunctions.RHTower.CyclicBarTraceMorphism

/-!
# Exact CCM strong cyclic target over the rational class space

Connes--Consani--Marcolli's strong target is not a multivariable Schwartz space.  Its degree-`n`
chains are continuous trace-norm field tensors whose normalized trace on the main diagonal lies in
the strong class-space Schwartz space.  This file implements that definition literally.

The diagonal trace first multiplies all cyclic tensor factors in their given order and then takes
the normalized trace at one common class-space point.  Trace cyclicity proves that every face,
degeneracy, and Connes rotation preserves the strong condition.  Hence the degreewise inverse
images form a genuine cyclic submodule of the cyclic bar of continuous trace-norm fields.

No independent-variable decay condition, operator-norm replacement, discrete topology, source
landing theorem, closed-range assertion, or spectral statement is inserted here.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions
namespace RHTower

private abbrev Section := CCMRationalClassSpaceSection
private abbrev Field := CCMRationalContinuousTraceNormField
private abbrev ScalarFunctions := Section → ℂ

/-- Evaluation of the normalized trace at one literal rational class-space point. -/
def ccmRationalContinuousTraceNormPointTrace (b : Section) :
    Field →ₗ[ℂ] ℂ where
  toFun F := ccmRationalMoritaTraceNormL1Trace (F b)
  map_add' F G := by
    simp only [ContinuousMap.add_apply, map_add]
  map_smul' z F := by
    simp only [ContinuousMap.smul_apply, map_smul, RingHom.id_apply]

@[simp]
theorem ccmRationalContinuousTraceNormPointTrace_apply
    (b : Section) (F : Field) :
    ccmRationalContinuousTraceNormPointTrace b F =
      ccmRationalMoritaTraceNormL1Trace (F b) :=
  rfl

/-- Pointwise normalized trace is cyclic on continuous trace-norm fields. -/
theorem ccmRationalContinuousTraceNormPointTrace_isTrace
    (b : Section) (F G : Field) :
    ccmRationalContinuousTraceNormPointTrace b (F * G) =
      ccmRationalContinuousTraceNormPointTrace b (G * F) :=
  ccmRationalMoritaTraceNormL1Trace_isTrace (F b) (G b)

/-- Main-diagonal trace in degree `n`: multiply all field factors, evaluate them at the same
class-space point, and take the normalized trace. -/
def ccmRationalStrongDiagonalTrace (n : ℕ) :
    CyclicBarTensor ℂ Field n →ₗ[ℂ] ScalarFunctions :=
  LinearMap.pi fun b =>
    (ccmRationalContinuousTraceNormPointTrace b).comp
      (cyclicBarTotalProduct n)

@[simp]
theorem ccmRationalStrongDiagonalTrace_apply
    (n : ℕ) (x : CyclicBarTensor ℂ Field n) (b : Section) :
    ccmRationalStrongDiagonalTrace n x b =
      ccmRationalContinuousTraceNormPointTrace b
        (cyclicBarTotalProduct n x) :=
  rfl

/-- Every face preserves the exact main-diagonal trace. -/
theorem ccmRationalStrongDiagonalTrace_comp_face
    (n : ℕ) (i : Fin (n + 2)) :
    (ccmRationalStrongDiagonalTrace n).comp
        (cyclicBarFace (R := ℂ) (A := Field) i) =
      ccmRationalStrongDiagonalTrace (n + 1) := by
  apply LinearMap.ext
  intro x
  funext b
  change
    cyclicBarTraceAugmentation
        (ccmRationalContinuousTraceNormPointTrace b) n
        (cyclicBarFace (R := ℂ) (A := Field) i x) =
      cyclicBarTraceAugmentation
        (ccmRationalContinuousTraceNormPointTrace b) (n + 1) x
  exact LinearMap.congr_fun
    (cyclicBarTraceAugmentation_comp_face
      (ccmRationalContinuousTraceNormPointTrace b)
      (ccmRationalContinuousTraceNormPointTrace_isTrace b) n i) x

/-- Every degeneracy preserves the exact main-diagonal trace. -/
theorem ccmRationalStrongDiagonalTrace_comp_degeneracy
    (n : ℕ) (i : Fin (n + 1)) :
    (ccmRationalStrongDiagonalTrace (n + 1)).comp
        (cyclicBarDegeneracy (R := ℂ) (A := Field) i) =
      ccmRationalStrongDiagonalTrace n := by
  apply LinearMap.ext
  intro x
  funext b
  change
    cyclicBarTraceAugmentation
        (ccmRationalContinuousTraceNormPointTrace b) (n + 1)
        (cyclicBarDegeneracy (R := ℂ) (A := Field) i x) =
      cyclicBarTraceAugmentation
        (ccmRationalContinuousTraceNormPointTrace b) n x
  exact LinearMap.congr_fun
    (cyclicBarTraceAugmentation_comp_degeneracy
      (ccmRationalContinuousTraceNormPointTrace b) n i) x

/-- Connes rotation preserves the exact main-diagonal trace. -/
theorem ccmRationalStrongDiagonalTrace_comp_rotate (n : ℕ) :
    (ccmRationalStrongDiagonalTrace n).comp
        (cyclicBarRotate (R := ℂ) (A := Field) n).toLinearMap =
      ccmRationalStrongDiagonalTrace n := by
  apply LinearMap.ext
  intro x
  funext b
  change
    cyclicBarTraceAugmentation
        (ccmRationalContinuousTraceNormPointTrace b) n
        (cyclicBarRotate (R := ℂ) (A := Field) n x) =
      cyclicBarTraceAugmentation
        (ccmRationalContinuousTraceNormPointTrace b) n x
  exact LinearMap.congr_fun
    (cyclicBarTraceAugmentation_comp_rotate
      (ccmRationalContinuousTraceNormPointTrace b)
      (ccmRationalContinuousTraceNormPointTrace_isTrace b) n) x

/-- Ambient cyclic bar of the exact algebra of continuous trace-norm fields. -/
abbrev CCMRationalContinuousTraceNormFieldCyclicModule : CyclicModule ℂ :=
  cyclicBarCyclicModule (R := ℂ) (A := Field)

/-- Main-diagonal trace component at an arbitrary presented simplex object. -/
def ccmRationalStrongDiagonalTraceComponent :
    ∀ a : SimplexCategoryGenRel,
      CCMRationalContinuousTraceNormFieldCyclicModule.simplicial.obj (.op a) ⟶
        ModuleCat.of ℂ ScalarFunctions :=
  SimplexCategoryGenRel.rec fun n =>
    ModuleCat.ofHom (ccmRationalStrongDiagonalTrace n)

@[simp]
theorem ccmRationalStrongDiagonalTraceComponent_mk (n : ℕ) :
    ccmRationalStrongDiagonalTraceComponent (.mk n) =
      ModuleCat.ofHom (ccmRationalStrongDiagonalTrace n) :=
  rfl

/-- Main-diagonal trace is natural for every morphism of the presented simplex category. -/
theorem ccmRationalStrongDiagonalTrace_naturality
    {a b : SimplexCategoryGenRel} (f : a ⟶ b) :
    CCMRationalContinuousTraceNormFieldCyclicModule.simplicial.map f.op ≫
        ccmRationalStrongDiagonalTraceComponent a =
      ccmRationalStrongDiagonalTraceComponent b := by
  let P : MorphismProperty SimplexCategoryGenRel := fun a b f =>
    CCMRationalContinuousTraceNormFieldCyclicModule.simplicial.map f.op ≫
        ccmRationalStrongDiagonalTraceComponent a =
      ccmRationalStrongDiagonalTraceComponent b
  apply SimplexCategoryGenRel.hom_induction P
  · intro n
    dsimp [P]
    simp
  · intro n m u i hu
    change
      CCMRationalContinuousTraceNormFieldCyclicModule.simplicial.map u.op ≫
          ccmRationalStrongDiagonalTraceComponent (.mk n) =
        ccmRationalStrongDiagonalTraceComponent (.mk m) at hu
    change
      CCMRationalContinuousTraceNormFieldCyclicModule.simplicial.map
            ((SimplexCategoryGenRel.δ i).op ≫ u.op) ≫
          ccmRationalStrongDiagonalTraceComponent (.mk n) =
        ccmRationalStrongDiagonalTraceComponent (.mk (m + 1))
    rw [Functor.map_comp, Category.assoc, hu]
    apply ModuleCat.hom_ext
    exact ccmRationalStrongDiagonalTrace_comp_face m i
  · intro n m u i hu
    change
      CCMRationalContinuousTraceNormFieldCyclicModule.simplicial.map u.op ≫
          ccmRationalStrongDiagonalTraceComponent (.mk n) =
        ccmRationalStrongDiagonalTraceComponent (.mk (m + 1)) at hu
    change
      CCMRationalContinuousTraceNormFieldCyclicModule.simplicial.map
            ((SimplexCategoryGenRel.σ i).op ≫ u.op) ≫
          ccmRationalStrongDiagonalTraceComponent (.mk n) =
        ccmRationalStrongDiagonalTraceComponent (.mk m)
    rw [Functor.map_comp, Category.assoc, hu]
    apply ModuleCat.hom_ext
    exact ccmRationalStrongDiagonalTrace_comp_degeneracy m i

/-- Exact CCM strong-condition submodule at an arbitrary simplex object. -/
def ccmRationalStrongCyclicObjectSubmodule (a : SimplexCategoryGenRel) :
    Submodule ℂ
      (CCMRationalContinuousTraceNormFieldCyclicModule.simplicial.obj (.op a)) :=
  CCMRationalStrongClassSpaceScalarTarget.comap
    (ccmRationalStrongDiagonalTraceComponent a).hom

@[simp]
theorem mem_ccmRationalStrongCyclicObjectSubmodule_iff
    (a : SimplexCategoryGenRel)
    (x : CCMRationalContinuousTraceNormFieldCyclicModule.simplicial.obj (.op a)) :
    x ∈ ccmRationalStrongCyclicObjectSubmodule a ↔
      ccmRationalStrongDiagonalTraceComponent a x ∈
        CCMRationalStrongClassSpaceScalarTarget :=
  Iff.rfl

/-- Presented simplicial object cut out by the exact CCM main-diagonal strong condition. -/
def ccmRationalStrongCyclicSimplicial :
    PresentedSimplicialObject (ModuleCat ℂ) where
  obj j := ModuleCat.of ℂ
    (ccmRationalStrongCyclicObjectSubmodule j.unop)
  map {j k} h := ModuleCat.ofHom
    { toFun := fun x =>
        ⟨CCMRationalContinuousTraceNormFieldCyclicModule.simplicial.map h x.1, by
          change
            ccmRationalStrongDiagonalTraceComponent k.unop
                (CCMRationalContinuousTraceNormFieldCyclicModule.simplicial.map h x.1) ∈
              CCMRationalStrongClassSpaceScalarTarget
          change
            (CCMRationalContinuousTraceNormFieldCyclicModule.simplicial.map h ≫
                ccmRationalStrongDiagonalTraceComponent k.unop) x.1 ∈
              CCMRationalStrongClassSpaceScalarTarget
          have hnat :
              CCMRationalContinuousTraceNormFieldCyclicModule.simplicial.map h ≫
                  ccmRationalStrongDiagonalTraceComponent k.unop =
                ccmRationalStrongDiagonalTraceComponent j.unop := by
            simpa using ccmRationalStrongDiagonalTrace_naturality h.unop
          rw [hnat]
          exact x.2⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp
      map_smul' := by
        intro z x
        apply Subtype.ext
        simp }
  map_id j := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp
  map_comp {i j k} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp

/-- Inclusion of exact strong simplicial chains into the ambient continuous-field cyclic bar. -/
def ccmRationalStrongCyclicSimplicialInclusion :
    ccmRationalStrongCyclicSimplicial ⟶
      CCMRationalContinuousTraceNormFieldCyclicModule.simplicial where
  app j := ModuleCat.ofHom
    (ccmRationalStrongCyclicObjectSubmodule j.unop).subtype
  naturality {j k} h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- Categorical form of invariance of the main-diagonal trace under Connes rotation. -/
theorem ccmRationalStrongDiagonalTrace_cyclic_naturality (n : ℕ) :
    CCMRationalContinuousTraceNormFieldCyclicModule.cyclic n ≫
        ccmRationalStrongDiagonalTraceComponent (.mk n) =
      ccmRationalStrongDiagonalTraceComponent (.mk n) := by
  apply ModuleCat.hom_ext
  exact ccmRationalStrongDiagonalTrace_comp_rotate n

/-- Linear Connes rotation restricted to exact strong chains.  Linearity is inherited from the
ambient cyclic operator rather than reproved through subtype coercions. -/
def ccmRationalStrongCyclicRotationLinear (n : ℕ) :
    ccmRationalStrongCyclicObjectSubmodule (.mk n) →ₗ[ℂ]
      ccmRationalStrongCyclicObjectSubmodule (.mk n) :=
  ((CCMRationalContinuousTraceNormFieldCyclicModule.cyclic n).hom.domRestrict
      (ccmRationalStrongCyclicObjectSubmodule (.mk n))).codRestrict
    (ccmRationalStrongCyclicObjectSubmodule (.mk n)) fun x => by
      change
        ccmRationalStrongDiagonalTraceComponent (.mk n)
            (CCMRationalContinuousTraceNormFieldCyclicModule.cyclic n x.1) ∈
          CCMRationalStrongClassSpaceScalarTarget
      change
        (CCMRationalContinuousTraceNormFieldCyclicModule.cyclic n ≫
            ccmRationalStrongDiagonalTraceComponent (.mk n)) x.1 ∈
          CCMRationalStrongClassSpaceScalarTarget
      rw [ccmRationalStrongDiagonalTrace_cyclic_naturality]
      exact x.2

/-- Connes rotation restricted to exact strong chains. -/
def ccmRationalStrongCyclicRotation (n : ℕ) :
    ccmRationalStrongCyclicSimplicial.degree n ⟶
      ccmRationalStrongCyclicSimplicial.degree n :=
  ModuleCat.ofHom (ccmRationalStrongCyclicRotationLinear n)

@[simp]
theorem ccmRationalStrongCyclicRotation_coe
    (n : ℕ) (x : ccmRationalStrongCyclicSimplicial.degree n) :
    (ccmRationalStrongCyclicRotation n x).1 =
      CCMRationalContinuousTraceNormFieldCyclicModule.cyclic n x.1 :=
  rfl

theorem ccmRationalStrongCyclicRotation_iterate_coe
    (n k : ℕ) (x : ccmRationalStrongCyclicSimplicial.degree n) :
    (categoricalEndIterate (ccmRationalStrongCyclicRotation n) k x).1 =
      categoricalEndIterate
        (CCMRationalContinuousTraceNormFieldCyclicModule.cyclic n) k x.1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [categoricalEndIterate_succ]
      change
        (ccmRationalStrongCyclicRotation n
          (categoricalEndIterate (ccmRationalStrongCyclicRotation n) k x)).1 =
        CCMRationalContinuousTraceNormFieldCyclicModule.cyclic n
          (categoricalEndIterate
            (CCMRationalContinuousTraceNormFieldCyclicModule.cyclic n) k x.1)
      rw [ccmRationalStrongCyclicRotation_coe, ih]

/-- **Exact CCM strong cyclic target.**  Degree `n` consists precisely of continuous trace-norm
field chains whose normalized trace on the main diagonal is strong Schwartz on `C_ℚ`. -/
def CCMRationalStrongCyclicTarget : CyclicModule ℂ where
  simplicial := ccmRationalStrongCyclicSimplicial
  cyclic := ccmRationalStrongCyclicRotation
  cyclic_order n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change
      (categoricalEndIterate
        (ccmRationalStrongCyclicRotation n) (n + 1) x).1 = x.1
    rw [ccmRationalStrongCyclicRotation_iterate_coe,
      CCMRationalContinuousTraceNormFieldCyclicModule.cyclic_order]
    rfl
  cyclic_face_zero n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact DFunLike.congr_fun
      (ModuleCat.hom_ext_iff.mp
        (CCMRationalContinuousTraceNormFieldCyclicModule.cyclic_face_zero n)) x.1
  cyclic_face_succ n i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact DFunLike.congr_fun
      (ModuleCat.hom_ext_iff.mp
        (CCMRationalContinuousTraceNormFieldCyclicModule.cyclic_face_succ n i)) x.1
  cyclic_degeneracy_zero n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact DFunLike.congr_fun
      (ModuleCat.hom_ext_iff.mp
        (CCMRationalContinuousTraceNormFieldCyclicModule.cyclic_degeneracy_zero n)) x.1
  cyclic_degeneracy_succ n i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact DFunLike.congr_fun
      (ModuleCat.hom_ext_iff.mp
        (CCMRationalContinuousTraceNormFieldCyclicModule.cyclic_degeneracy_succ n i)) x.1

/-- Canonical cyclic inclusion of the exact strong target into the ambient continuous-field bar. -/
def ccmRationalStrongCyclicTargetInclusion :
    CyclicModule.Hom CCMRationalStrongCyclicTarget
      CCMRationalContinuousTraceNormFieldCyclicModule where
  simplicial := ccmRationalStrongCyclicSimplicialInclusion
  cyclic_naturality n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

end RHTower
end GaloisForLFunctions
