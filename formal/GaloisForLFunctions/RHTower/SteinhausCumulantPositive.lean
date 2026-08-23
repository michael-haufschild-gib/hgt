import GaloisForLFunctions.RHTower.SteinhausSubcriticalRate

/-!
# Strict positivity of the cumulants

The circle cumulant is strictly convex and even with `log I₀(0) = 0`, so `log I₀(x) > 0` for every
`x ≠ 0`; integrating, `Λ_α(λ) > 0` for every `λ > 0`.  This is what pins the Legendre supremum to
the small-tilt range.
-/

open MeasureTheory Set

namespace HTGeometry

noncomputable section

/-- **The circle cumulant is strictly positive off the origin.** -/
theorem steinhausLogLaplace_pos {x : ℝ} (hx : x ≠ 0) : 0 < steinhausLogLaplace x := by
  have hstrict := strictConvexOn_steinhausLogLaplace
  have hne : x ≠ -x := by
    intro h
    apply hx
    linarith
  have hmid := hstrict.2 (Set.mem_univ x) (Set.mem_univ (-x)) hne
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hzero : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (-x) = 0 := by
    simp only [smul_eq_mul]
    ring
  rw [hzero] at hmid
  have heven : steinhausLogLaplace (-x) = steinhausLogLaplace x := steinhausLogLaplace_neg x
  rw [heven] at hmid
  simp only [smul_eq_mul, steinhausLogLaplace_zero] at hmid
  linarith

/-- **The regular-variation cumulant is strictly positive off the origin.** -/
theorem rvCumulant_pos {α : ℝ} (hα : α < 1) {lam : ℝ} (hlam : 0 < lam) :
    0 < rvCumulant α lam := by
  rw [rvCumulant]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (intervalIntegrable_rvCumulant_integrand hα lam) ?_ (by norm_num)
  intro v hv
  have hw : 0 < weightProfile α v := weightProfile_pos hα hv.1
  exact steinhausLogLaplace_pos (by positivity)

end

end HTGeometry
