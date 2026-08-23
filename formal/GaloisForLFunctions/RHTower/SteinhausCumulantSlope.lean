import GaloisForLFunctions.RHTower.SteinhausCumulantPositive

/-!
# The cumulant's slope is nondecreasing

Convexity with `log I₀(0) = 0` gives `log I₀(t x) ≤ t·log I₀(x)` for `0 ≤ t ≤ 1`, hence
`Λ_α(δ)/δ ≤ Λ_α(λ)/λ` for `0 < δ ≤ λ`.  Since `Λ_α(δ) > 0`, every tilt beyond `δ` contributes a
NEGATIVE value to the Legendre supremum once `q < Λ_α(δ)/δ`, which confines the supremum to the
small-tilt range where the quadratic asymptotic holds.
-/

open MeasureTheory Set

namespace HTGeometry

noncomputable section

/-- Convexity through the origin. -/
theorem steinhausLogLaplace_scale_le {t x : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    steinhausLogLaplace (t * x) ≤ t * steinhausLogLaplace x := by
  rcases eq_or_lt_of_le ht0 with h | ht0'
  · rw [← h]
    simp
  rcases eq_or_lt_of_le ht1 with h | ht1'
  · rw [h]
    simp
  have hconv := strictConvexOn_steinhausLogLaplace.convexOn
  have h := hconv.2 (Set.mem_univ x) (Set.mem_univ (0 : ℝ)) ht0
    (by linarith : (0:ℝ) ≤ 1 - t) (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, steinhausLogLaplace_zero, mul_zero] at h
  exact h

/-- **The cumulant's slope is nondecreasing.** -/
theorem rvCumulant_slope_mono {α : ℝ} (hα : α < 1) {δ lam : ℝ} (hδ : 0 < δ) (hle : δ ≤ lam) :
    lam / δ * rvCumulant α δ ≤ rvCumulant α lam := by
  have hlam : 0 < lam := lt_of_lt_of_le hδ hle
  have ht0 : (0 : ℝ) ≤ δ / lam := by positivity
  have ht1 : δ / lam ≤ 1 := by
    rw [div_le_one hlam]
    exact hle
  have hpt : ∀ v ∈ Set.Icc (0 : ℝ) 1,
      steinhausLogLaplace (δ * weightProfile α v)
        ≤ (δ / lam) * steinhausLogLaplace (lam * weightProfile α v) := by
    intro v _
    have hid : δ * weightProfile α v = (δ / lam) * (lam * weightProfile α v) := by
      field_simp
    rw [hid]
    exact steinhausLogLaplace_scale_le ht0 ht1
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
    (intervalIntegrable_rvCumulant_integrand hα δ)
    ((intervalIntegrable_rvCumulant_integrand hα lam).const_mul (δ / lam)) hpt
  rw [intervalIntegral.integral_const_mul] at hmono
  have hcum : rvCumulant α δ ≤ (δ / lam) * rvCumulant α lam := hmono
  rw [div_mul_eq_mul_div, div_le_iff₀ hδ]
  have hstep : lam * rvCumulant α δ ≤ lam * (δ / lam * rvCumulant α lam) :=
    mul_le_mul_of_nonneg_left hcum hlam.le
  have hid : lam * (δ / lam * rvCumulant α lam) = rvCumulant α lam * δ := by
    field_simp
  rw [hid] at hstep
  exact hstep

end

end HTGeometry
