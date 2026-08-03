import GaloisForLFunctions.RHTower.CCMRationalContinuousTraceNormField
import GaloisForLFunctions.RHTower.CCMRationalStrongClassSpace
import GaloisForLFunctions.RHTower.CyclicModuleConstantPreimage
import GaloisForLFunctions.RHTower.CyclicBarTraceMorphism
import GaloisForLFunctions.RHTower.KRealCyclicBarTrace

/-!
# Exact CCM strongly-Schwartz trace-class cyclic target

CCM Definition 4.9 constrains the cyclic diagonal trace, not the trace norm of the operator field.
This file implements that distinction literally.  The ambient algebra consists of continuous
genuine Schatten-`1` fields.  In degree `n`, a chain is admitted exactly when

`b ↦ Tr(T₀(b)⋯Tₙ(b))`

belongs to the full strong Schwartz space on `C_ℚ`.  The condition is packaged as a genuine cyclic
submodule and is proved stable under the exact quaternionic Real involution.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions
namespace RHTower

private abbrev Field := CCMRationalContinuousTraceNormField
private abbrev Section := CCMRationalClassSpaceSection
private abbrev ScalarFunction := Section → ℂ

/-- Normalized trace after evaluation at one point of the canonical class-space section. -/
def ccmRationalTraceNormFieldTraceAt (b : Section) : Field →ₗ[ℂ] ℂ where
  toFun F := ccmRationalMoritaTraceNormL1Trace (F b)
  map_add' F G := map_add ccmRationalMoritaTraceNormL1Trace (F b) (G b)
  map_smul' z F := map_smul ccmRationalMoritaTraceNormL1Trace z (F b)

@[simp]
theorem ccmRationalTraceNormFieldTraceAt_apply
    (b : Section) (F : Field) :
    ccmRationalTraceNormFieldTraceAt b F =
      ccmRationalMoritaTraceNormL1Trace (F b) :=
  rfl

theorem ccmRationalTraceNormFieldTraceAt_isTrace
    (b : Section) (F G : Field) :
    ccmRationalTraceNormFieldTraceAt b (F * G) =
      ccmRationalTraceNormFieldTraceAt b (G * F) :=
  ccmRationalMoritaTraceNormL1Trace_isTrace (F b) (G b)

theorem ccmRationalTraceNormFieldTraceAt_real
    (b : Section) (F : Field) :
    ccmRationalTraceNormFieldTraceAt b
        (ccmRationalContinuousTraceNormFieldReal F) =
      star (ccmRationalTraceNormFieldTraceAt b F) :=
  ccmRationalMoritaTraceNormL1Trace_real (F b)

/-- Main cyclic diagonal trace as a scalar function on the literal class-space section. -/
def ccmRationalCyclicDiagonalTrace (n : ℕ) :
    CyclicBarTensor ℂ Field n →ₗ[ℂ] ScalarFunction where
  toFun x b :=
    cyclicBarTraceAugmentation (ccmRationalTraceNormFieldTraceAt b) n x
  map_add' x y := by
    funext b
    exact map_add
      (cyclicBarTraceAugmentation (ccmRationalTraceNormFieldTraceAt b) n) x y
  map_smul' z x := by
    funext b
    exact map_smul
      (cyclicBarTraceAugmentation (ccmRationalTraceNormFieldTraceAt b) n) z x

@[simp]
theorem ccmRationalCyclicDiagonalTrace_apply
    (n : ℕ) (x : CyclicBarTensor ℂ Field n) (b : Section) :
    ccmRationalCyclicDiagonalTrace n x b =
      cyclicBarTraceAugmentation
        (ccmRationalTraceNormFieldTraceAt b) n x :=
  rfl

theorem ccmRationalCyclicDiagonalTrace_face
    {n : ℕ} (i : Fin (n + 2))
    (x : CyclicBarTensor ℂ Field (n + 1)) :
    ccmRationalCyclicDiagonalTrace n
        (cyclicBarFace (R := ℂ) (A := Field) i x) =
      ccmRationalCyclicDiagonalTrace (n + 1) x := by
  funext b
  have h := cyclicBarTraceAugmentation_comp_face
    (ccmRationalTraceNormFieldTraceAt b)
    (ccmRationalTraceNormFieldTraceAt_isTrace b) n i
  exact (LinearMap.ext_iff.mp h) x

theorem ccmRationalCyclicDiagonalTrace_degeneracy
    {n : ℕ} (i : Fin (n + 1))
    (x : CyclicBarTensor ℂ Field n) :
    ccmRationalCyclicDiagonalTrace (n + 1)
        (cyclicBarDegeneracy (R := ℂ) (A := Field) i x) =
      ccmRationalCyclicDiagonalTrace n x := by
  funext b
  have h := cyclicBarTraceAugmentation_comp_degeneracy
    (ccmRationalTraceNormFieldTraceAt b) n i
  exact (LinearMap.ext_iff.mp h) x

theorem ccmRationalCyclicDiagonalTrace_rotate
    (n : ℕ) (x : CyclicBarTensor ℂ Field n) :
    ccmRationalCyclicDiagonalTrace n
        (cyclicBarRotate (R := ℂ) (A := Field) n x) =
      ccmRationalCyclicDiagonalTrace n x := by
  funext b
  have h := cyclicBarTraceAugmentation_comp_rotate
    (ccmRationalTraceNormFieldTraceAt b)
    (ccmRationalTraceNormFieldTraceAt_isTrace b) n
  exact (LinearMap.ext_iff.mp h) x

/-- Ambient cyclic bar of continuous genuine trace-norm fields. -/
abbrev CCMRationalContinuousTraceNormFieldCyclicModule : CyclicModule ℂ :=
  cyclicBarCyclicModule (R := ℂ) (A := Field)

/-- Diagonal-trace component at an arbitrary presented simplex object. -/
def ccmRationalCyclicDiagonalTraceComponent :
    ∀ a : SimplexCategoryGenRel,
      CCMRationalContinuousTraceNormFieldCyclicModule.simplicial.obj (.op a) ⟶
        ModuleCat.of ℂ ScalarFunction :=
  SimplexCategoryGenRel.rec fun n =>
    ModuleCat.ofHom (ccmRationalCyclicDiagonalTrace n)

@[simp]
theorem ccmRationalCyclicDiagonalTraceComponent_mk (n : ℕ) :
    ccmRationalCyclicDiagonalTraceComponent (.mk n) =
      ModuleCat.ofHom (ccmRationalCyclicDiagonalTrace n) :=
  rfl

theorem ccmRationalCyclicDiagonalTrace_naturality
    {a b : SimplexCategoryGenRel} (f : a ⟶ b) :
    CCMRationalContinuousTraceNormFieldCyclicModule.simplicial.map f.op ≫
        ccmRationalCyclicDiagonalTraceComponent a =
      ccmRationalCyclicDiagonalTraceComponent b := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext c
  have h := cyclicBarTraceAugmentation_naturality
    (ccmRationalTraceNormFieldTraceAt c)
    (ccmRationalTraceNormFieldTraceAt_isTrace c) f
  exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp h) x

/-- Natural transformation given by the main cyclic diagonal trace. -/
def ccmRationalCyclicDiagonalTraceSimplicialHom :
    CCMRationalContinuousTraceNormFieldCyclicModule.simplicial ⟶
      (moduleConstantCyclicModule (R := ℂ) ScalarFunction).simplicial where
  app j := ccmRationalCyclicDiagonalTraceComponent j.unop
  naturality {j k} f := by
    change
      CCMRationalContinuousTraceNormFieldCyclicModule.simplicial.map f ≫
          ccmRationalCyclicDiagonalTraceComponent k.unop =
        ccmRationalCyclicDiagonalTraceComponent j.unop ≫ 𝟙 _
    rw [Category.comp_id]
    exact ccmRationalCyclicDiagonalTrace_naturality f.unop

@[simp]
theorem ccmRationalCyclicDiagonalTraceSimplicialHom_app (n : ℕ) :
    ccmRationalCyclicDiagonalTraceSimplicialHom.app (.op (.mk n)) =
      ModuleCat.ofHom (ccmRationalCyclicDiagonalTrace n) :=
  rfl

/-- Genuine cyclic morphism given by the main diagonal trace. -/
def ccmRationalCyclicDiagonalTraceHom :
    CyclicModule.Hom CCMRationalContinuousTraceNormFieldCyclicModule
      (moduleConstantCyclicModule (R := ℂ) ScalarFunction) where
  simplicial := ccmRationalCyclicDiagonalTraceSimplicialHom
  cyclic_naturality n := by
    simp only [cyclicBarCyclicModule_cyclic,
      ccmRationalCyclicDiagonalTraceSimplicialHom_app,
      moduleConstantCyclicModule_cyclic, Category.comp_id]
    apply ModuleCat.hom_ext
    exact LinearMap.ext fun x => ccmRationalCyclicDiagonalTrace_rotate n x

/-- Exact CCM Definition 4.9 target: inverse image of strong scalar class-space functions under
the main cyclic diagonal trace. -/
def CCMRationalStrongTraceClassCyclicModule : CyclicModule ℂ :=
  ccmRationalCyclicDiagonalTraceHom.constantPreimage
    CCMRationalStrongClassSpaceScalarTarget

/-- Inclusion of the exact strong target into the ambient continuous trace-norm cyclic bar. -/
def ccmRationalStrongTraceClassCyclicInclusion :
    CyclicModule.Hom CCMRationalStrongTraceClassCyclicModule
      CCMRationalContinuousTraceNormFieldCyclicModule :=
  ccmRationalCyclicDiagonalTraceHom.constantPreimageInclusion
    CCMRationalStrongClassSpaceScalarTarget

@[simp]
theorem mem_ccmRationalStrongTraceClassCyclicDegree_iff
    (n : ℕ) (x : CyclicBarTensor ℂ Field n) :
    x ∈ ccmRationalCyclicDiagonalTraceHom.constantPreimageSubmodule
        CCMRationalStrongClassSpaceScalarTarget (.op (.mk n)) ↔
      ccmRationalCyclicDiagonalTrace n x ∈
        CCMRationalStrongClassSpaceScalarTarget :=
  Iff.rfl

/-- The diagonal trace of the ambient cyclic Real action is pointwise complex conjugation. -/
theorem ccmRationalCyclicDiagonalTrace_real
    (n : ℕ) (x : CyclicBarTensor ℂ Field n) :
    ccmRationalCyclicDiagonalTrace n
        ((cyclicBarDegreeKReal
          ccmRationalContinuousTraceNormFieldKRealAlgebra n).sigma x) =
      fun b => star (ccmRationalCyclicDiagonalTrace n x b) := by
  funext b
  exact (cyclicBarTraceAugmentation_kReal
    ccmRationalContinuousTraceNormFieldKRealAlgebra
    (ccmRationalTraceNormFieldTraceAt b)
    (ccmRationalTraceNormFieldTraceAt_real b) n x).symm

/-- Degreewise even Real structure restricted to the exact strong trace target. -/
def ccmRationalStrongTraceClassDegreeKReal (n : ℕ) :
    KRealStructure false
      (CCMRationalStrongTraceClassCyclicModule.simplicial.degree n) where
  sigma :=
    { toFun := fun x =>
        ⟨(cyclicBarDegreeKReal
            ccmRationalContinuousTraceNormFieldKRealAlgebra n).sigma x.1, by
          change ccmRationalCyclicDiagonalTrace n
              ((cyclicBarDegreeKReal
                ccmRationalContinuousTraceNormFieldKRealAlgebra n).sigma x.1) ∈
            CCMRationalStrongClassSpaceScalarTarget
          rw [ccmRationalCyclicDiagonalTrace_real]
          have hx : ccmRationalCyclicDiagonalTrace n x.1 ∈
              CCMRationalStrongClassSpaceScalarTarget := by
            change x.1 ∈
              ccmRationalCyclicDiagonalTraceHom.constantPreimageSubmodule
                CCMRationalStrongClassSpaceScalarTarget (.op (.mk n))
            exact x.2
          exact CCMRationalStrongClassSpaceScalarTarget.real_mem hx⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact map_add
          (cyclicBarDegreeKReal
            ccmRationalContinuousTraceNormFieldKRealAlgebra n).sigma x.1 y.1
      map_smul' := by
        intro z x
        apply Subtype.ext
        exact (cyclicBarDegreeKReal
          ccmRationalContinuousTraceNormFieldKRealAlgebra n).sigma.map_smulₛₗ z x.1 }
  sq x := by
    apply Subtype.ext
    rw [(cyclicBarDegreeKReal
      ccmRationalContinuousTraceNormFieldKRealAlgebra n).sq]
    rfl

/-- Exact strong trace-class cyclic target with its inherited even Real structure. -/
def ccmRationalStrongTraceClassKReal :
    CyclicModule.KReal false CCMRationalStrongTraceClassCyclicModule where
  real := ccmRationalStrongTraceClassDegreeKReal
  face_naturality n i x := by
    apply Subtype.ext
    exact (cyclicBarKReal
      ccmRationalContinuousTraceNormFieldKRealAlgebra).face_naturality n i x.1
  degeneracy_naturality n i x := by
    apply Subtype.ext
    exact (cyclicBarKReal
      ccmRationalContinuousTraceNormFieldKRealAlgebra).degeneracy_naturality n i x.1
  cyclic_naturality n x := by
    apply Subtype.ext
    exact (cyclicBarKReal
      ccmRationalContinuousTraceNormFieldKRealAlgebra).cyclic_naturality n x.1

end RHTower
end GaloisForLFunctions
