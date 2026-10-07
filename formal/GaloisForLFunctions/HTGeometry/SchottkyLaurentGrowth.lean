import GaloisForLFunctions.HTGeometry.SchottkyHalfPlaneGrowth

/-!
# Laurent compositions on a half-plane

Two omitted nonzero-separated values bound both a map and its reciprocal.
Consequently every finite Laurent expression has an exponential ray bound.
-/

open Complex Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- A Laurent expression in a half-plane map omitting zero and another value
has at most exponential growth along the horizontal ray. -/
theorem exists_exp_ray_bound_laurent (R : ℝ) (p q : Polynomial ℂ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z : ℂ | R < z.re}) {b : ℂ} (hb : b ≠ 0)
    (homit : ∀ z : ℂ, R < z.re → f z ≠ 0 ∧ f z ≠ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖p.eval (f ((R + t : ℝ) : ℂ)) + q.eval ((f ((R + t : ℝ) : ℂ))⁻¹)‖ ≤
        Real.exp (C * t) := by
  let g : ℂ → ℂ := fun z => (f z)⁻¹
  have hg : DifferentiableOn ℂ g {z : ℂ | R < z.re} :=
    hf.inv (fun z hz => (homit z hz).1)
  have hgomit : ∀ z : ℂ, R < z.re → g z ≠ 0 ∧ g z ≠ b⁻¹ := by
    intro z hz
    exact ⟨inv_ne_zero (homit z hz).1, fun he => (homit z hz).2 (inv_inj.mp he)⟩
  obtain ⟨A, hA, hp⟩ := exists_exp_ray_bound_polynomial R p
    (exists_exp_ray_bound_of_omitting_two_halfPlane R hf hb.symm homit)
  obtain ⟨B, hB, hq⟩ := exists_exp_ray_bound_polynomial R q
    (exists_exp_ray_bound_of_omitting_two_halfPlane R hg (inv_ne_zero hb).symm hgomit)
  refine ⟨A + B + 1, by positivity, fun t ht => ?_⟩
  have ht0 : 0 ≤ t := by linarith
  have he2 : 2 ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  calc
    _ ≤ ‖p.eval (f ((R + t : ℝ) : ℂ))‖ + ‖q.eval (g ((R + t : ℝ) : ℂ))‖ :=
      norm_add_le _ _
    _ ≤ Real.exp (A * t) + Real.exp (B * t) := add_le_add (hp t ht) (hq t ht)
    _ ≤ Real.exp ((A + B) * t) + Real.exp ((A + B) * t) := by
      apply add_le_add <;> apply Real.exp_le_exp.mpr <;> nlinarith
    _ = 2 * Real.exp ((A + B) * t) := by ring
    _ ≤ Real.exp t * Real.exp ((A + B) * t) :=
      mul_le_mul_of_nonneg_right he2 (Real.exp_nonneg _)
    _ = Real.exp ((A + B + 1) * t) := by rw [← Real.exp_add]; congr 1; ring

end GaloisForLFunctions.HTGeometry
