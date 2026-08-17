import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The projective speed is scalar invariant, and the two-port wedge expansion

The angular budget of a moving frame is measured by the norm of the component of the derivative
transverse to the frame direction, normalized by the frame length.  Multiplying the frame by a
nonvanishing scalar changes neither the direction it spans nor that normalized transverse length —
the scalar cancels between numerator and denominator, and the extra term `m'F` produced by the
product rule is parallel to the frame and is removed by the projection.  This is why no pointwise
estimate for the common multiplier can control the budget.

The two-port expansion is exact.  Writing the frame as `e^{iax}u + e^{-iax}v` and wedging with its
derivative, the two same-port cross terms cancel their own phases and produce `-2ia (u ∧ v)`, while
everything else is the remainder: the two self-port terms carry `e^{±2iax}` and the two mixed
derivative terms carry no phase at all.
-/

open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.RHTower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The transverse component of a vector relative to a frame direction. -/
def transverseComponent (F v : E) : E := v - (ℂ ∙ F).starProjection v

/-- The normalized angular speed of a moving frame. -/
def projectiveSpeed (F v : E) : ℝ := ‖transverseComponent F v‖ / ‖F‖

/-! ## `(80)`: the scalar multiplier cancels -/

theorem span_smul_eq {m : ℂ} (hm : m ≠ 0) (F : E) : (ℂ ∙ (m • F)) = ℂ ∙ F := by
  apply le_antisymm
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self F)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    refine Submodule.mem_span_singleton.mpr ⟨m⁻¹, ?_⟩
    rw [smul_smul, inv_mul_cancel₀ hm, one_smul]

theorem transverseComponent_smul (m : ℂ) (hm : m ≠ 0) (F v : E) :
    transverseComponent (m • F) (m • v) = m • transverseComponent F v := by
  have hspan : (ℂ ∙ (m • F)) = ℂ ∙ F := span_smul_eq hm F
  simp only [transverseComponent, hspan, map_smul, smul_sub]

theorem transverseComponent_add_parallel (c : ℂ) (F v : E) :
    transverseComponent F (c • F + v) = transverseComponent F v := by
  have hmem : (ℂ ∙ F).starProjection (c • F) = c • F :=
    Submodule.starProjection_eq_self_iff.mpr
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self F))
  rw [transverseComponent, transverseComponent, map_add, hmem]
  abel

/-- **`(80)`: the normalized angular speed is invariant under a nonvanishing scalar multiplier,
including the term produced by the product rule.** -/
theorem projectiveSpeed_scalar_invariant {m : ℂ} (hm : m ≠ 0) (m' : ℂ) (F F' : E) :
    projectiveSpeed (m • F) (m' • F + m • F') = projectiveSpeed F F' := by
  have hstep : transverseComponent (m • F) (m' • F + m • F')
      = m • transverseComponent F F' := by
    have hpar : m' • F = (m' / m) • (m • F) := by
      rw [smul_smul, div_mul_cancel₀ _ hm]
    rw [hpar, transverseComponent_add_parallel, transverseComponent_smul m hm]
  rw [projectiveSpeed, projectiveSpeed, hstep, norm_smul, norm_smul]
  rw [mul_div_mul_left _ _ (by simpa using hm : ‖m‖ ≠ 0)]

/-! ## `(83)`: the two-port wedge expansion -/

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- **`(83)`: the exact two-port wedge expansion.**  The two opposite-port cross terms have
cancelling phases and contribute `-2α (u ∧ v)`; everything else is the remainder. -/
theorem wedge_expansion {w : E → E → W}
    (hadd₁ : ∀ x y z, w (x + y) z = w x z + w y z)
    (hadd₂ : ∀ x y z, w x (y + z) = w x y + w x z)
    (hsmul₁ : ∀ (c : ℂ) (x y), w (c • x) y = c • w x y)
    (hsmul₂ : ∀ (c : ℂ) (x y), w x (c • y) = c • w x y)
    (halt : ∀ x, w x x = 0)
    {p α : ℂ} (hp : p ≠ 0) (u v u' v' : E) :
    w (p • u + p⁻¹ • v)
        ((α * p) • u + p • u' + ((-(α * p⁻¹)) • v + p⁻¹ • v'))
      = (-2 * α) • w u v
        + ((p ^ 2) • w u u' + (p⁻¹ ^ 2) • w v v' + (w u v' + w v u')) := by
  have hvu : w v u = -w u v := by
    have h := halt (u + v)
    rw [hadd₁, hadd₂, hadd₂, halt u, halt v] at h
    have hsum : w u v + w v u = 0 := by simpa using h
    linear_combination (norm := module) hsum
  have e2 : p * (-(α * p⁻¹)) = -α := by field_simp
  have e3 : p⁻¹ * (α * p) = α := by field_simp
  have e4 : p * p⁻¹ = (1 : ℂ) := mul_inv_cancel₀ hp
  have e5 : p⁻¹ * p = (1 : ℂ) := inv_mul_cancel₀ hp
  have e7 : p * p = p ^ 2 := by ring
  have e8 : p⁻¹ * p⁻¹ = p⁻¹ ^ 2 := by ring
  simp only [hadd₁, hadd₂, hsmul₁, hsmul₂, smul_smul, e2, e3, e4, e5, e7, e8,
    halt, smul_zero, zero_add, hvu]
  module

/-! ## `(85)`: the angular budget lower bound -/

/-- **`(85)`: a positive wedge floor forces angular speed of order the aperture.** -/
theorem projectiveSpeed_ge {a δ S β N Ω : ℝ} (hS : 0 < S) (hβ : 0 < β)
    (hβS : β ≤ S) (hN : 0 ≤ N) (hlow : δ * a * S ^ 2 ≤ N) (hΩ : Ω = N / β ^ 2) :
    δ * a ≤ Ω := by
  have hβ2 : (0 : ℝ) < β ^ 2 := by positivity
  have hS2 : (0 : ℝ) < S ^ 2 := by positivity
  have hmono : N / S ^ 2 ≤ N / β ^ 2 := by
    apply div_le_div_of_nonneg_left hN hβ2
    nlinarith [hβS, hβ, hS]
  have hlow' : δ * a ≤ N / S ^ 2 := by
    rw [le_div_iff₀ hS2]
    linarith
  rw [hΩ]
  linarith

end GaloisForLFunctions.RHTower
