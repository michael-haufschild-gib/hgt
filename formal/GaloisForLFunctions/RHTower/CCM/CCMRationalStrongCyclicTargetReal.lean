import GaloisForLFunctions.RHTower.CCM.CCMRationalStrongCyclicTarget
import GaloisForLFunctions.RHTower.KRealCyclicBarTrace

/-!
# Real structure on the exact rational CCM strong cyclic target

Quaternionic conjugation acts fiberwise on continuous genuine trace-norm fields.  Its cyclic
diagonal trace is pointwise complex conjugation, so conjugation stability of the exact strong
class-space Schwartz target restricts the ambient cyclic Real structure to CCM Definition 4.9.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

private abbrev Field := CCMRationalContinuousTraceNormField
private abbrev Section := CCMRationalClassSpaceSection

theorem ccmRationalContinuousTraceNormPointTrace_real
    (b : Section) (F : Field) :
    ccmRationalContinuousTraceNormPointTrace b
        (ccmRationalContinuousTraceNormFieldReal F) =
      star (ccmRationalContinuousTraceNormPointTrace b F) :=
  ccmRationalMoritaTraceNormL1Trace_real (F b)

/-- The main cyclic diagonal trace intertwines quaternionic Real structure and pointwise complex
conjugation in every degree. -/
theorem ccmRationalStrongDiagonalTrace_real
    (n : ℕ) (x : CyclicBarTensor ℂ Field n) :
    ccmRationalStrongDiagonalTrace n
        ((cyclicBarDegreeKReal
          ccmRationalContinuousTraceNormFieldKRealAlgebra n).sigma x) =
      fun b => star (ccmRationalStrongDiagonalTrace n x b) := by
  funext b
  exact (cyclicBarTraceAugmentation_kReal
    ccmRationalContinuousTraceNormFieldKRealAlgebra
    (ccmRationalContinuousTraceNormPointTrace b)
    (ccmRationalContinuousTraceNormPointTrace_real b) n x).symm

/-- Degreewise even Real structure restricted to exact CCM strong chains. -/
def ccmRationalStrongCyclicTargetDegreeKReal (n : ℕ) :
    KRealStructure false (CCMRationalStrongCyclicTarget.simplicial.degree n) where
  sigma :=
    { toFun := fun x =>
        ⟨(cyclicBarDegreeKReal
            ccmRationalContinuousTraceNormFieldKRealAlgebra n).sigma x.1, by
          change ccmRationalStrongDiagonalTrace n
              ((cyclicBarDegreeKReal
                ccmRationalContinuousTraceNormFieldKRealAlgebra n).sigma x.1) ∈
            CCMRationalStrongClassSpaceScalarTarget
          rw [ccmRationalStrongDiagonalTrace_real]
          have hx : ccmRationalStrongDiagonalTrace n x.1 ∈
              CCMRationalStrongClassSpaceScalarTarget := x.2
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
    change (cyclicBarDegreeKReal
        ccmRationalContinuousTraceNormFieldKRealAlgebra n).sigma
          ((cyclicBarDegreeKReal
            ccmRationalContinuousTraceNormFieldKRealAlgebra n).sigma x.1) = x.1
    exact (cyclicBarDegreeKReal
      ccmRationalContinuousTraceNormFieldKRealAlgebra n).sq x.1

/-- Exact strong trace-class target with its inherited even Real cyclic structure. -/
def ccmRationalStrongCyclicTargetKReal :
    CyclicModule.KReal false CCMRationalStrongCyclicTarget where
  real := ccmRationalStrongCyclicTargetDegreeKReal
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
