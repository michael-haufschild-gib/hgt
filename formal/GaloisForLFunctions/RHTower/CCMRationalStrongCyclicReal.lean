import GaloisForLFunctions.RHTower.CCMRationalStrongCyclicTarget
import GaloisForLFunctions.RHTower.KRealCyclicBarTrace

/-!
# Real structure on the exact CCM strong cyclic target

The quaternionic Morita fiber carries an isometric Real involution, hence so does the algebra of
continuous trace-norm fields.  This file proves that the induced componentwise Real operation on
every cyclic tensor preserves CCM's exact main-diagonal strong condition.  The decisive identity
is unconditional and pointwise:

`Tr^natural(sigma x)(b) = conjugate (Tr^natural(x)(b))`.

Because the strong rational class-space target is closed under conjugation, the ambient even Real
cyclic structure restricts to the genuine strong cyclic submodule.  No spectral, positivity,
source-landing, or closed-cokernel premise is used.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

private abbrev Section := CCMRationalClassSpaceSection
private abbrev Field := CCMRationalContinuousTraceNormField

private abbrev FieldKReal : KRealAlgebraStructure Field :=
  ccmRationalContinuousTraceNormFieldKRealAlgebra

private abbrev AmbientDegreeKReal (n : ℕ) :
    KRealStructure false (CyclicBarTensor ℂ Field n) :=
  cyclicBarDegreeKReal FieldKReal n

/-- Pointwise normalized trace intertwines the field Real involution and scalar conjugation. -/
theorem ccmRationalContinuousTraceNormPointTrace_real
    (b : Section) (F : Field) :
    ccmRationalContinuousTraceNormPointTrace b
        (ccmRationalContinuousTraceNormFieldReal F) =
      star (ccmRationalContinuousTraceNormPointTrace b F) :=
  ccmRationalMoritaTraceNormL1Trace_real (F b)

/-- **Exact Real diagonal law.**  Real conjugation of every cyclic factor conjugates the scalar
main-diagonal trace, in every degree. -/
theorem ccmRationalStrongDiagonalTrace_real
    (n : ℕ) (x : CyclicBarTensor ℂ Field n) (b : Section) :
    ccmRationalStrongDiagonalTrace n
        ((AmbientDegreeKReal n).sigma x) b =
      star (ccmRationalStrongDiagonalTrace n x b) := by
  have h := cyclicBarTraceAugmentation_kReal
    FieldKReal
    (ccmRationalContinuousTraceNormPointTrace b)
    (ccmRationalContinuousTraceNormPointTrace_real b) n x
  exact h.symm

/-- CCM's exact strong degree submodule is stable under componentwise field Real conjugation. -/
theorem ccmRationalStrongCyclicObjectSubmodule_real_stable (n : ℕ) :
    (AmbientDegreeKReal n).StableSubmodule
      (ccmRationalStrongCyclicObjectSubmodule (.mk n)) := by
  intro x hx
  change
    ccmRationalStrongDiagonalTrace n ((AmbientDegreeKReal n).sigma x) ∈
      CCMRationalStrongClassSpaceScalarTarget
  have hconj := CCMRationalStrongClassSpaceScalarTarget.real_mem hx
  convert hconj using 1
  funext b
  exact ccmRationalStrongDiagonalTrace_real n x b

/-- Conjugate-linear Real map restricted to exact strong degree-`n` chains. -/
def ccmRationalStrongCyclicDegreeRealSigma (n : ℕ) :
    ccmRationalStrongCyclicObjectSubmodule (.mk n) →ₗ⋆[ℂ]
      ccmRationalStrongCyclicObjectSubmodule (.mk n) :=
  (((AmbientDegreeKReal n).sigma.comp
      (ccmRationalStrongCyclicObjectSubmodule (.mk n)).subtype)).codRestrict
    (ccmRationalStrongCyclicObjectSubmodule (.mk n))
      (fun x =>
        ccmRationalStrongCyclicObjectSubmodule_real_stable n x.1 x.2)

@[simp]
theorem ccmRationalStrongCyclicDegreeRealSigma_coe
    (n : ℕ) (x : ccmRationalStrongCyclicObjectSubmodule (.mk n)) :
    (ccmRationalStrongCyclicDegreeRealSigma n x).1 =
      (AmbientDegreeKReal n).sigma x.1 :=
  rfl

/-- Even Real structure on exact strong degree-`n` chains. -/
def ccmRationalStrongCyclicDegreeKReal (n : ℕ) :
    KRealStructure false
      (ccmRationalStrongCyclicSimplicial.degree n) where
  sigma := ccmRationalStrongCyclicDegreeRealSigma n
  sq x := by
    apply Subtype.ext
    change (AmbientDegreeKReal n).sigma
        ((AmbientDegreeKReal n).sigma x.1) = x.1
    exact (AmbientDegreeKReal n).sq x.1

/-- The exact strong Real operation commutes with every face. -/
theorem ccmRationalStrongCyclicDegreeKReal_face
    (n : ℕ) (i : Fin (n + 2))
    (x : ccmRationalStrongCyclicSimplicial.degree (n + 1)) :
    (ccmRationalStrongCyclicDegreeKReal n).sigma
        (ccmRationalStrongCyclicSimplicial.δ i x) =
      ccmRationalStrongCyclicSimplicial.δ i
        ((ccmRationalStrongCyclicDegreeKReal (n + 1)).sigma x) := by
  apply Subtype.ext
  exact cyclicBarDegreeKReal_face FieldKReal i x.1

/-- The exact strong Real operation commutes with every degeneracy. -/
theorem ccmRationalStrongCyclicDegreeKReal_degeneracy
    (n : ℕ) (i : Fin (n + 1))
    (x : ccmRationalStrongCyclicSimplicial.degree n) :
    (ccmRationalStrongCyclicDegreeKReal (n + 1)).sigma
        (ccmRationalStrongCyclicSimplicial.σ i x) =
      ccmRationalStrongCyclicSimplicial.σ i
        ((ccmRationalStrongCyclicDegreeKReal n).sigma x) := by
  apply Subtype.ext
  exact cyclicBarDegreeKReal_degeneracy FieldKReal i x.1

/-- The exact strong Real operation commutes with Connes rotation. -/
theorem ccmRationalStrongCyclicDegreeKReal_rotate
    (n : ℕ) (x : ccmRationalStrongCyclicSimplicial.degree n) :
    (ccmRationalStrongCyclicDegreeKReal n).sigma
        (ccmRationalStrongCyclicRotation n x) =
      ccmRationalStrongCyclicRotation n
        ((ccmRationalStrongCyclicDegreeKReal n).sigma x) := by
  apply Subtype.ext
  exact cyclicBarDegreeKReal_rotate FieldKReal n x.1

/-- **Exact even Real structure on the CCM strong cyclic target.** -/
def ccmRationalStrongCyclicKReal :
    CyclicModule.KReal false CCMRationalStrongCyclicTarget where
  real := ccmRationalStrongCyclicDegreeKReal
  face_naturality := ccmRationalStrongCyclicDegreeKReal_face
  degeneracy_naturality := ccmRationalStrongCyclicDegreeKReal_degeneracy
  cyclic_naturality := ccmRationalStrongCyclicDegreeKReal_rotate

end RHTower
end GaloisForLFunctions
