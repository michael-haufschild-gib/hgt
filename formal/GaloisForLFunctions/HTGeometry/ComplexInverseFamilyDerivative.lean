import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic

/-!
# Derivative of a complex Banach-algebra inverse family

Inverting a complex-differentiable family of units is complex differentiable, with the exact
noncommutative derivative `-(C⁻¹ C′ C⁻¹)`.  This is the scalar-field-generic analytic bridge
needed by holomorphic operator resolvents.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]

/-- Pointwise ring inverse of a complex-differentiable Banach-algebra family. -/
def complexInvFamily (C : ℂ → R) (s : ℂ) : R := Ring.inverse (C s)

/-- Candidate derivative of the inverse family. -/
def complexInvFamilyDeriv (C C₁ : ℂ → R) (s : ℂ) : R :=
  -(complexInvFamily C s * C₁ s * complexInvFamily C s)

/-- Inversion of a complex-differentiable family is differentiable at every unit value. -/
theorem hasDerivAt_complexInvFamily {C C₁ : ℂ → R} {s : ℂ}
    (hC : HasDerivAt C (C₁ s) s) (hu : IsUnit (C s)) :
    HasDerivAt (complexInvFamily C) (complexInvFamilyDeriv C C₁ s) s := by
  obtain ⟨u, huC⟩ := hu
  have huEq : C s = (u : R) := huC.symm
  have hinv : complexInvFamily C s = ((u⁻¹ : Rˣ) : R) := by
    rw [complexInvFamily, huEq, Ring.inverse_unit]
  have hpoint : HasFDerivAt Ring.inverse
      (-(ContinuousLinearMap.mulLeftRight ℂ R ((u⁻¹ : Rˣ) : R) ((u⁻¹ : Rˣ) : R)))
      (C s) := by
    rw [huEq]
    exact hasFDerivAt_ringInverse u
  have h := hpoint.comp_hasDerivAt s hC
  refine h.congr_deriv ?_
  rw [complexInvFamilyDeriv, hinv]
  simp [ContinuousLinearMap.mulLeftRight_apply]

end GaloisForLFunctions.HTGeometry
