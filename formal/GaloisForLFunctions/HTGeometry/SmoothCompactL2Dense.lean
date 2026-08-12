import Mathlib

/-!
# Smooth compactly supported representatives are dense in real `L²`

The classes in `Lp ℝ 2` admitting a smooth compactly supported representative form a submodule,
and mathlib's `Lp.dense_hasCompactSupport_contDiff` says that submodule is dense.  A weak-limit
argument needs the subspace form: convergence of inner products against this submodule, plus a
uniform bound, upgrades to weak convergence against the whole space.
-/

open MeasureTheory
open scoped ContDiff

namespace GaloisForLFunctions.HTGeometry

/-- The submodule of real `L²` classes with a smooth compactly supported representative. -/
noncomputable def smoothCompactSubmodule : Submodule ℝ (Lp ℝ 2 (volume : Measure ℝ)) where
  carrier := {f | ∃ g : ℝ → ℝ, f =ᵐ[volume] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g}
  add_mem' := by
    rintro f₁ f₂ ⟨g₁, hfg₁, hc₁, hs₁⟩ ⟨g₂, hfg₂, hc₂, hs₂⟩
    refine ⟨g₁ + g₂, ?_, hc₁.add hc₂, hs₁.add hs₂⟩
    filter_upwards [Lp.coeFn_add f₁ f₂, hfg₁, hfg₂] with x h1 h2 h3
    simp only [h1, Pi.add_apply, h2, h3]
  zero_mem' := by
    refine ⟨0, ?_, ?_, contDiff_const⟩
    · filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := (volume : Measure ℝ))] with x hx
      simp only [Pi.zero_apply] at hx ⊢
      exact hx
    · simpa using HasCompactSupport.zero (α := ℝ) (β := ℝ)
  smul_mem' := by
    rintro c f ⟨g, hfg, hc, hs⟩
    refine ⟨c • g, ?_, ?_, hs.const_smul c⟩
    · filter_upwards [Lp.coeFn_smul c f, hfg] with x h1 h2
      simp only [h1, Pi.smul_apply, h2]
    · have := hc.comp_left (g := fun y : ℝ => c * y) (by norm_num)
      refine this.mono ?_
      intro x hx
      simpa [Function.comp_def, Pi.smul_apply, smul_eq_mul] using hx

/-- **Density.** -/
theorem dense_smoothCompactSubmodule :
    Dense (smoothCompactSubmodule : Set (Lp ℝ 2 (volume : Measure ℝ))) := by
  have h := MeasureTheory.Lp.dense_hasCompactSupport_contDiff
    (F := ℝ) (μ := (volume : Measure ℝ)) (p := 2) (by norm_num)
  exact h

end GaloisForLFunctions.HTGeometry
