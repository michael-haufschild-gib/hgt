import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Algebra.Support
import GaloisForLFunctions.RHTower.KRealKernelCokernel

/-!
# Real reflection on compactly supported locally constant functions

For any topological abelian group `X`, this file constructs

`(R f)(x) = conj (f (-x))`

on compactly supported locally constant complex-valued functions. It proves that the carrier
is preserved and that `R` is a conjugate-linear involution.

This is the algebraic Bruhat-function factor needed at finite adeles. Mathlib does not yet
provide its LF topology, so no continuity claim is made here. No arithmetic spectrum,
positivity, or Riemann-hypothesis premise occurs.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

variable (X : Type*) [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X]

/-- Compactly supported locally constant complex-valued functions on `X`. -/
def compactlySupportedLocallyConstant :
    Submodule ℂ (LocallyConstant X ℂ) where
  carrier := {f | HasCompactSupport (f : X → ℂ)}
  zero_mem' := by
    simp [HasCompactSupport]
  add_mem' := by
    intro f g hf hg
    exact hf.add hg
  smul_mem' := by
    intro z f hf
    change HasCompactSupport ((z • f : LocallyConstant X ℂ) : X → ℂ)
    have hcomp := hf.comp_left (show z * (0 : ℂ) = 0 by simp)
    have hfun :
        ((fun y : ℂ => z * y) ∘ (f : X → ℂ)) =
          ((z • f : LocallyConstant X ℂ) : X → ℂ) := by
      funext x
      rfl
    rw [hfun] at hcomp
    exact hcomp

/-- Negation as a continuous self-map of a topological abelian group. -/
def locallyConstantNegContinuous : C(X, X) :=
  ⟨fun x => -x, continuous_neg⟩

/-- Sign-reflection on the ambient locally constant function space. -/
def compactlySupportedLocallyConstantReflectionRaw
    (f : LocallyConstant X ℂ) : LocallyConstant X ℂ :=
  (LocallyConstant.comap (locallyConstantNegContinuous X) f).map
    (starRingEnd ℂ)

@[simp]
theorem compactlySupportedLocallyConstantReflectionRaw_apply
    (f : LocallyConstant X ℂ) (x : X) :
    compactlySupportedLocallyConstantReflectionRaw X f x = star (f (-x)) :=
  rfl

/-- Homeomorphic pullback and conjugation preserve compact support. -/
theorem compactlySupportedLocallyConstantReflectionRaw_hasCompactSupport
    (f : compactlySupportedLocallyConstant X) :
    HasCompactSupport
      (compactlySupportedLocallyConstantReflectionRaw X f.1 : X → ℂ) := by
  change HasCompactSupport
    ((fun z : ℂ => star z) ∘
      ((f.1 : X → ℂ) ∘ (Homeomorph.neg X : X → X)))
  exact (f.2.comp_homeomorph (Homeomorph.neg X)).comp_left (by simp)

/-- Conjugate-linear sign-reflection on compactly supported locally constant functions. -/
def compactlySupportedLocallyConstantReflection :
    compactlySupportedLocallyConstant X →ₗ⋆[ℂ]
      compactlySupportedLocallyConstant X where
  toFun f :=
    ⟨compactlySupportedLocallyConstantReflectionRaw X f.1,
      compactlySupportedLocallyConstantReflectionRaw_hasCompactSupport X f⟩
  map_add' f g := by
    apply Subtype.ext
    ext x
    simp
  map_smul' z f := by
    apply Subtype.ext
    ext x
    simp

@[simp]
theorem compactlySupportedLocallyConstantReflection_apply
    (f : compactlySupportedLocallyConstant X) (x : X) :
    (compactlySupportedLocallyConstantReflection X f).1 x =
      star (f.1 (-x)) :=
  compactlySupportedLocallyConstantReflectionRaw_apply X f.1 x

/-- Sign-reflection is an involution on the compactly supported carrier. -/
theorem compactlySupportedLocallyConstantReflection_sq
    (f : compactlySupportedLocallyConstant X) :
    compactlySupportedLocallyConstantReflection X
      (compactlySupportedLocallyConstantReflection X f) = f := by
  apply Subtype.ext
  ext x
  rw [compactlySupportedLocallyConstantReflection_apply,
    compactlySupportedLocallyConstantReflection_apply]
  simp

/-- Even `KRealStructure` on compactly supported locally constant functions. -/
def compactlySupportedLocallyConstantKRealEven :
    KRealStructure false (compactlySupportedLocallyConstant X) where
  sigma := compactlySupportedLocallyConstantReflection X
  sq f := by
    simpa [kRealParityAction] using
      compactlySupportedLocallyConstantReflection_sq X f

end RHTower
end GaloisForLFunctions
