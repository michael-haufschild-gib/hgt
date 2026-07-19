import GaloisForLFunctions.HTGeometry.MomentDeterminacyStep

/-!
# Uniform convergence on a carrying set passes through the integral

If a finite measure gives full mass to `S` and `F n → f` uniformly on `S`, then the integrals
converge.  The estimate is the elementary one: the integrand is uniformly small almost
everywhere, so
`norm_integral_le_of_norm_le_const` bounds the difference of the integrals by that smallness
times the
total mass.

This is the analytic step a density argument needs, isolated from the density itself.
-/

open scoped BigOperators
open MeasureTheory Filter

namespace HTGeometry

/-- **Uniform convergence on a full-measure set gives convergence of integrals.** -/
theorem tendsto_integral_of_tendstoUniformlyOn {mu : Measure ℝ} [IsFiniteMeasure mu]
    {S : Set ℝ} (hS : mu Sᶜ = 0) {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hF : ∀ n, Integrable (F n) mu) (hf : Integrable f mu)
    (hunif : TendstoUniformlyOn F f atTop S) :
    Tendsto (fun n => ∫ x, F n x ∂mu) atTop (nhds (∫ x, f x ∂mu)) := by
  refine Metric.tendsto_atTop.mpr fun eps heps => ?_
  set c : ℝ := (mu Set.univ).toReal with hc
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  set e : ℝ := eps / (2 * (c + 1)) with he
  have he0 : 0 < e := by
    rw [he]
    have : 0 < 2 * (c + 1) := by linarith
    positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp hunif e he0)
  refine ⟨N, fun n hn => ?_⟩
  have hae : ∀ᵐ x ∂mu, x ∈ S := by
    rw [ae_iff]
    simpa using hS
  have hbound : ∀ᵐ x ∂mu, ‖F n x - f x‖ ≤ e := by
    filter_upwards [hae] with x hx
    have hd := hN n hn x hx
    rw [Real.dist_eq] at hd
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact hd.le
  have hsub : ∫ x, F n x ∂mu - ∫ x, f x ∂mu = ∫ x, (F n x - f x) ∂mu :=
    (integral_sub (hF n) hf).symm
  rw [Real.dist_eq, hsub]
  have hle : ‖∫ x, (F n x - f x) ∂mu‖ ≤ e * c :=
    norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs] at hle
  refine lt_of_le_of_lt hle ?_
  rw [he]
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith : (0:ℝ) < 2 * (c + 1))]
  nlinarith [heps, hc0]

end HTGeometry
