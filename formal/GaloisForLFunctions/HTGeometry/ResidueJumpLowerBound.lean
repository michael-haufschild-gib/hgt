import Mathlib

/-!
# A residue forces a uniform jump on the surrounding circle

If a function has a non-zero residue on a circle, then it cannot be uniformly close on that circle
to any function whose integral over the circle vanishes: the sup-distance is at least
`‖residue‖ / radius`.

This is the mechanism by which a family of functions parametrised by a point `α` can be
*discontinuous in `α`* purely because the residue of the family at a fixed pole is non-zero at one
parameter value and zero at all others: the residue is a contour integral, so a uniform limit of
residue-free members cannot have a non-zero residue. Only the two contour facts are used —
linearity of the circle integral and the standard length estimate — so the statement is elementary
and unconditional.
-/

open Complex Metric

namespace HTGeometry

/-- **Residue jump bound.**  If the circle integral of `h` over `∂B(c,r)` equals `2πi·ρ` and `h` is
bounded by `C` on that circle, then `C ≥ ‖ρ‖ / r`. -/
theorem residue_jump_bound {h : ℂ → ℂ} {c ρ : ℂ} {r C : ℝ} (hr : 0 < r)
    (hres : (∮ z in C(c, r), h z) = 2 * Real.pi * Complex.I * ρ)
    (hC : ∀ z ∈ Metric.sphere c r, ‖h z‖ ≤ C) :
    ‖ρ‖ / r ≤ C := by
  have hlen : ‖∮ z in C(c, r), h z‖ ≤ 2 * Real.pi * r * C :=
    circleIntegral.norm_integral_le_of_norm_le_const hr.le hC
  rw [hres] at hlen
  have hnorm : ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I * ρ‖ = 2 * Real.pi * ‖ρ‖ := by
    simp [abs_of_nonneg Real.pi_pos.le]
  rw [hnorm] at hlen
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2 : (2 * Real.pi) * ‖ρ‖ ≤ (2 * Real.pi) * (r * C) :=
    calc (2 * Real.pi) * ‖ρ‖ ≤ 2 * Real.pi * r * C := hlen
      _ = (2 * Real.pi) * (r * C) := by ring
  have h1 : ‖ρ‖ ≤ r * C := le_of_mul_le_mul_left h2 hpi
  exact (div_le_iff₀ hr).2 (by linarith [h1])

/-- **The jump form.**  A function `f` whose circle integral vanishes cannot approximate, uniformly
on that circle, a function `g` with non-zero residue `ρ`: the sup-distance is at least `‖ρ‖ / r`.
Applied to the standard twist of an `L`-function — where `g` is the twist at a spectral parameter
(non-zero residue) and `f` a twist at a non-spectral parameter (entire, so vanishing integral) —
this is the exact obstruction to continuity of the twist family at its spectrum. -/
theorem residue_jump_of_integral_eq_zero {f g : ℂ → ℂ} {c ρ : ℂ} {r C : ℝ} (hr : 0 < r)
    (hfi : CircleIntegrable f c r) (hgi : CircleIntegrable g c r)
    (hf : (∮ z in C(c, r), f z) = 0)
    (hg : (∮ z in C(c, r), g z) = 2 * Real.pi * Complex.I * ρ)
    (hC : ∀ z ∈ Metric.sphere c r, ‖g z - f z‖ ≤ C) :
    ‖ρ‖ / r ≤ C := by
  refine residue_jump_bound (h := fun z => g z - f z) hr ?_ hC
  rw [circleIntegral.integral_sub hgi hfi, hf, hg, sub_zero]

end HTGeometry
