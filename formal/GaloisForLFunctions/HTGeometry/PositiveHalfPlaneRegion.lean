import Mathlib.Analysis.Complex.Convex
import GaloisForLFunctions.HTGeometry.FiniteGaugeTailCharge

/-!
# The positive half-plane, explicitly

Membership in the positive half-plane is the most frequently consumed premise of the area, and it
had no named producer.  The region is `{s | 0 < Re s}`: membership is that inequality, it contains
every positive real, and it is an open convex — hence preconnected — set, which is what the
identity-theorem arguments over it need.
-/

open Complex

namespace GaloisForLFunctions

@[simp] theorem mem_positiveHalfPlane {s : ℂ} : s ∈ positiveHalfPlane ↔ 0 < s.re := Iff.rfl

theorem isOpen_positiveHalfPlane : IsOpen positiveHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re

theorem convex_positiveHalfPlane : Convex ℝ positiveHalfPlane :=
  convex_halfSpace_re_gt 0

theorem isPreconnected_positiveHalfPlane : IsPreconnected positiveHalfPlane :=
  convex_positiveHalfPlane.isPreconnected

/-- Every positive real lies in the half-plane. -/
theorem ofReal_mem_positiveHalfPlane {x : ℝ} (hx : 0 < x) :
    ((x : ℂ)) ∈ positiveHalfPlane := by
  simpa using hx

theorem one_mem_positiveHalfPlane : (1 : ℂ) ∈ positiveHalfPlane := by
  simp

theorem positiveHalfPlane_nonempty : positiveHalfPlane.Nonempty :=
  ⟨1, one_mem_positiveHalfPlane⟩

/-- The half-plane is stable under adding a nonnegative real part. -/
theorem add_mem_positiveHalfPlane {s w : ℂ} (hs : s ∈ positiveHalfPlane)
    (hw : 0 ≤ w.re) : s + w ∈ positiveHalfPlane := by
  rw [mem_positiveHalfPlane] at hs ⊢
  rw [Complex.add_re]
  linarith

end GaloisForLFunctions
