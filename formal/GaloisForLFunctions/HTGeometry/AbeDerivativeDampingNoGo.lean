import GaloisForLFunctions.HTGeometry.AbeUniformDampingNoGo
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Pointwise damping alone cannot dominate differentiated tails

Abe's point-separation argument uses pointwise strict damping together with a
parameter-independent summable majorant, so Tannery's theorem handles the
undifferentiated complement sum.  At positive jet order, differentiating the
damping exponential produces powers of the parameter.  A strict negative
phase that may approach zero cannot absorb even the first such power uniformly.

The first theorem records the valid value-level Tannery step.  The second is a
closed obstruction to extending it to derivatives from strict pointwise phase
negativity alone.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **Abe's valid value-level tail principle.** Pointwise damping plus a single
parameter-independent summable majorant makes the whole complement `tsum` vanish; no uniform
negative phase gap is needed. -/
theorem tendsto_tsum_zero_of_pointwise_damping_of_summable_majorant
    {T ι : Type*} {l : Filter T} {f : T → ι → ℂ} {bound : ι → ℝ}
    (hbound : Summable bound)
    (hpoint : ∀ z : ι, Tendsto (fun t => f t z) l (nhds 0))
    (hdom : ∀ᶠ t in l, ∀ z : ι, ‖f t z‖ ≤ bound z) :
    Tendsto (fun t => ∑' z : ι, f t z) l (nhds 0) := by
  simpa using tendsto_tsum_of_dominated_convergence hbound hpoint hdom

/-- **No common dominator for the first damping derivative.**  Strict pointwise decay
`exp (-a B)` with arbitrary `a > 0` does not uniformly absorb its derivative factor `B`.
Consequently, a derivative-stable summable dominator needs additional quantitative structure;
strict phase negativity by itself is insufficient. -/
theorem not_exists_uniform_linear_exponential_damping_bound :
    ¬ ∃ C : ℝ, ∀ B a : ℝ, 0 ≤ B → 0 < a →
      B * Real.exp (-a * B) ≤ C := by
  rintro ⟨C, hC⟩
  have hC0 : 0 ≤ C := by
    have h := hC 1 1 zero_le_one zero_lt_one
    norm_num at h ⊢
    exact (Real.exp_pos (-1)).le.trans h
  let B : ℝ := (C + 1) * Real.exp 1
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have ha : 0 < B⁻¹ := inv_pos.mpr hBpos
  have h := hC B B⁻¹ hBpos.le ha
  have hunit : B⁻¹ * B = 1 := inv_mul_cancel₀ hBpos.ne'
  have hvalue : B * Real.exp (-(B⁻¹) * B) = C + 1 := by
    rw [show -B⁻¹ * B = -(B⁻¹ * B) by ring]
    rw [hunit]
    dsimp [B]
    rw [Real.exp_neg]
    field_simp
  rw [hvalue] at h
  linarith

end GaloisForLFunctions.HTGeometry
