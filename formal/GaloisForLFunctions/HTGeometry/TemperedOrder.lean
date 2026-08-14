import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Tempered distributions have finite order

A continuous linear functional on Schwartz space is bounded by finitely many Schwartz seminorms:
there are a finite index set and a constant with

`‖u φ‖ ≤ C · max_{(k,n) ∈ s} ‖·‖^k ‖D^n ·‖ (φ)`.

This is the finite-order property, the starting point of every local structure theorem for tempered
distributions.
-/

open SchwartzMap

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- **A tempered distribution has finite order.** -/
theorem exists_schwartz_seminorm_bound (u : 𝓢(ℝ, ℂ) →L[ℂ] X) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ φ : 𝓢(ℝ, ℂ), ‖u φ‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) φ := by
  have hq : Continuous ((normSeminorm ℂ X).comp (u : 𝓢(ℝ, ℂ) →ₗ[ℂ] X)) := by
    have : ⇑((normSeminorm ℂ X).comp (u : 𝓢(ℝ, ℂ) →ₗ[ℂ] X)) = fun φ => ‖u φ‖ := rfl
    rw [this]
    exact u.continuous.norm
  obtain ⟨s, C, hC, hle⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ ℝ ℂ)
    ((normSeminorm ℂ X).comp (u : 𝓢(ℝ, ℂ) →ₗ[ℂ] X)) hq
  refine ⟨s, (C : ℝ), ?_, fun φ => ?_⟩
  · exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hC)
  · have h := hle φ
    simpa [smul_apply, Seminorm.comp_apply, coe_normSeminorm, NNReal.smul_def] using h

end GaloisForLFunctions.HTGeometry
