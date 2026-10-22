import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import GaloisForLFunctions.RHTower.KRealKernelCokernel

/-!
# Real reflection on the rational archimedean Schwartz factor

On `SchwartzMap ℝ ℂ`, this file constructs

`(R f)(x) = conj (f (-x))`

as a continuous conjugate-linear involution and bundles it as an even `KRealStructure`.
This is the archimedean analytic factor of the rational CCM source involution.

No finite-adele Bruhat--Schwartz space, crossed product, cyclic homology, positivity, zero
spectrum, or Riemann-hypothesis premise occurs.
-/

noncomputable section

open scoped SchwartzMap

namespace GaloisForLFunctions
namespace RHTower

/-- Rational archimedean complex-valued Schwartz space. -/
abbrev CCMRationalArchimedeanSchwartz := SchwartzMap ℝ ℂ

/--
Real-continuous-linear realization of sign-reflection: precompose by negation, then
postcompose by complex conjugation.
-/
def ccmRationalArchimedeanSchwartzReflectionCLM :
    CCMRationalArchimedeanSchwartz →L[ℝ]
      CCMRationalArchimedeanSchwartz :=
  (SchwartzMap.postcompCLM (E := ℝ) (𝕜 := ℝ)
      (Complex.conjCLE : ℂ →L[ℝ] ℂ)).comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
      (LinearIsometryEquiv.neg ℝ (E := ℝ)))

@[simp]
theorem ccmRationalArchimedeanSchwartzReflectionCLM_apply
    (f : CCMRationalArchimedeanSchwartz) (x : ℝ) :
    ccmRationalArchimedeanSchwartzReflectionCLM f x =
      star (f (-x)) := by
  rfl

/-- Rational archimedean sign-reflection as a complex conjugate-linear map. -/
def ccmRationalArchimedeanSchwartzReflection :
    CCMRationalArchimedeanSchwartz →ₗ⋆[ℂ]
      CCMRationalArchimedeanSchwartz where
  toFun := ccmRationalArchimedeanSchwartzReflectionCLM
  map_add' f g := by
    ext x
    simp
  map_smul' z f := by
    ext x
    simp

@[simp]
theorem ccmRationalArchimedeanSchwartzReflection_apply
    (f : CCMRationalArchimedeanSchwartz) (x : ℝ) :
    ccmRationalArchimedeanSchwartzReflection f x =
      star (f (-x)) :=
  rfl

/-- The rational archimedean Schwartz reflection is an involution. -/
theorem ccmRationalArchimedeanSchwartzReflection_sq
    (f : CCMRationalArchimedeanSchwartz) :
    ccmRationalArchimedeanSchwartzReflection
      (ccmRationalArchimedeanSchwartzReflection f) = f := by
  ext x
  simp

/-- The rational archimedean Schwartz reflection is continuous in the Schwartz topology. -/
theorem ccmRationalArchimedeanSchwartzReflection_continuous :
    Continuous ccmRationalArchimedeanSchwartzReflection :=
  ccmRationalArchimedeanSchwartzReflectionCLM.continuous

/-- Even `KRealStructure` on the rational archimedean Schwartz factor. -/
def ccmRationalArchimedeanSchwartzKRealEven :
    KRealStructure false CCMRationalArchimedeanSchwartz where
  sigma := ccmRationalArchimedeanSchwartzReflection
  sq f := by
    simpa [kRealParityAction] using
      ccmRationalArchimedeanSchwartzReflection_sq f

end RHTower
end GaloisForLFunctions
