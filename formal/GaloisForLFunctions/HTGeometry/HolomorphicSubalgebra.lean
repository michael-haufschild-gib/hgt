import GaloisForLFunctions.HTGeometry.RightHalfPlaneSpace
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# The holomorphic subalgebra of continuous functions on the half-plane

A continuous function on the half-plane is *holomorphic* when it is the restriction of a function
differentiable on the half-plane.  Carrying the witness `F` avoids having to define
differentiability on a subtype, and the closure properties are inherited from the witnesses: sums,
products and scalar multiples of differentiable functions are differentiable.

The Cauchy coordinate belongs to this subalgebra, being the restriction of `w ↦ (w + a)⁻¹`, whose
denominator does not vanish on the half-plane.

* `HTGeometry.holoAlgebra`;
* `HTGeometry.cauchyCoord_mem_holoAlgebra`.
-/

namespace HTGeometry

/-- The subalgebra of continuous functions on the half-plane that extend holomorphically. -/
def holoAlgebra : Subalgebra ℂ C((rightHalfPlane : Set ℂ), ℂ) where
  carrier := {f | ∃ F : ℂ → ℂ, DifferentiableOn ℂ F rightHalfPlane ∧
    ∀ z : (rightHalfPlane : Set ℂ), f z = F (z : ℂ)}
  mul_mem' := by
    rintro f g ⟨F, hF, hf⟩ ⟨G, hG, hg⟩
    refine ⟨fun w => F w * G w, hF.mul hG, fun z => ?_⟩
    simp [hf z, hg z]
  one_mem' := ⟨fun _ => 1, differentiableOn_const 1, fun _ => rfl⟩
  add_mem' := by
    rintro f g ⟨F, hF, hf⟩ ⟨G, hG, hg⟩
    refine ⟨fun w => F w + G w, hF.add hG, fun z => ?_⟩
    simp [hf z, hg z]
  zero_mem' := ⟨fun _ => 0, differentiableOn_const 0, fun _ => rfl⟩
  algebraMap_mem' := by
    intro c
    refine ⟨fun _ => c, differentiableOn_const c, fun z => ?_⟩
    rfl

theorem mem_holoAlgebra_iff {f : C((rightHalfPlane : Set ℂ), ℂ)} :
    f ∈ holoAlgebra ↔ ∃ F : ℂ → ℂ, DifferentiableOn ℂ F rightHalfPlane ∧
      ∀ z : (rightHalfPlane : Set ℂ), f z = F (z : ℂ) := Iff.rfl

/-- **The Cauchy coordinate is holomorphic.** -/
theorem cauchyCoord_mem_holoAlgebra {a : ℝ} (ha : 0 < a) :
    cauchyCoord a ha ∈ holoAlgebra := by
  refine ⟨fun w => (w + (a : ℂ))⁻¹, ?_, fun z => rfl⟩
  intro w hw
  have hwne : w + (a : ℂ) ≠ 0 := by
    intro hcon
    have hre : w.re + a = 0 := by
      have hc := congrArg Complex.re hcon
      simpa using hc
    have hpos : 0 < w.re := hw
    linarith
  have hdiff : DifferentiableAt ℂ (fun v : ℂ => (v + (a : ℂ))⁻¹) w := by
    have hbase : DifferentiableAt ℂ (fun v : ℂ => v + (a : ℂ)) w := by fun_prop
    exact hbase.inv hwne
  exact hdiff.differentiableWithinAt

end HTGeometry
