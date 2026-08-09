import GaloisForLFunctions.HTGeometry.HalfPlaneSigmaCompact
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# The right half-plane as a space of functions

The subtype carrying the right half-plane, with the two topological instances a compact-open
argument needs: local compactness, which an open subset of `ℂ` inherits, and σ-compactness, which
Lean does not infer and which the explicit exhaustion supplies.

The Cauchy coordinate `z ↦ (z + a)⁻¹` is a continuous function on it — the single generator whose
powers approximate every holomorphic function.

* `HTGeometry.rightHalfPlane`, `HTGeometry.isOpen_rightHalfPlane`;
* the instances `LocallyCompactSpace` and `SigmaCompactSpace` on the subtype;
* `HTGeometry.cauchyCoord`.
-/

open Metric

namespace HTGeometry

/-- The right half-plane. -/
def rightHalfPlane : Set ℂ := {z : ℂ | 0 < z.re}

theorem isOpen_rightHalfPlane : IsOpen rightHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re

@[simp] theorem mem_rightHalfPlane {z : ℂ} : z ∈ rightHalfPlane ↔ 0 < z.re := Iff.rfl

instance : LocallyCompactSpace (rightHalfPlane : Set ℂ) :=
  isOpen_rightHalfPlane.locallyCompactSpace

instance : SigmaCompactSpace (rightHalfPlane : Set ℂ) := by
  have h : IsSigmaCompact (rightHalfPlane : Set ℂ) := isSigmaCompact_rightHalfPlane
  rw [isSigmaCompact_iff_isSigmaCompact_univ] at h
  exact ⟨h⟩

/-- On the half-plane the shifted point never vanishes. -/
theorem add_ne_zero_of_mem_rightHalfPlane {a : ℝ} (ha : 0 < a) (z : (rightHalfPlane : Set ℂ)) :
    (z : ℂ) + (a : ℂ) ≠ 0 := by
  intro hcon
  have hre : (z : ℂ).re + a = 0 := by
    have hc := congrArg Complex.re hcon
    simpa using hc
  have hz : 0 < (z : ℂ).re := z.2
  linarith

/-- The Cauchy coordinate on the right half-plane. -/
noncomputable def cauchyCoord (a : ℝ) (ha : 0 < a) :
    C((rightHalfPlane : Set ℂ), ℂ) where
  toFun := fun z => ((z : ℂ) + (a : ℂ))⁻¹
  continuous_toFun := by
    refine Continuous.inv₀ (by fun_prop) ?_
    exact add_ne_zero_of_mem_rightHalfPlane ha

@[simp] theorem cauchyCoord_apply {a : ℝ} (ha : 0 < a) (z : (rightHalfPlane : Set ℂ)) :
    cauchyCoord a ha z = ((z : ℂ) + (a : ℂ))⁻¹ := rfl

end HTGeometry
