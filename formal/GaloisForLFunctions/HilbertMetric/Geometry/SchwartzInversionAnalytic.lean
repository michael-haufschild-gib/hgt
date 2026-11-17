import GaloisForLFunctions.HilbertMetric.Geometry.SchwartzInversion
import GaloisForLFunctions.HTGeometry.KleinbockMargulis.AnalyticNondegeneracy

/-!
# The analytic boundary of flat Schwartz compactification

The inversion extension is identically zero near the pole exactly when
the original Schwartz function has compact support. Since every jet at
the pole vanishes, real analyticity is equivalent to that same support
condition. The stereographic scalar correction has the identical boundary.
-/

open Filter Topology Metric
namespace GaloisForLFunctions.HilbertMetric.Geometry.SchwartzInversionAnalytic
open SchwartzInversion
open GaloisForLFunctions.HTGeometry.KleinbockMargulis
noncomputable section

/-- Local vanishing after inversion is exactly compact support before inversion. -/
theorem kelvin_eventually_zero_iff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : SchwartzMap ℂ F) :
    (kelvin f =ᶠ[𝓝 0] fun _ => 0) ↔ HasCompactSupport (f : ℂ → F) := by
  constructor
  · intro h
    obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp h
    apply HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (1 / ε))
    intro w hw
    have hnorm : 1 / ε < ‖w‖ := by
      simpa only [mem_closedBall, dist_zero_right, not_le] using hw
    have hp : 0 < ‖w‖ := lt_trans (one_div_pos.mpr hε) hnorm
    have hw0 : w ≠ 0 := norm_ne_zero_iff.mp hp.ne'
    have hi : ‖w⁻¹‖ < ε := by
      rw [norm_inv, ← one_div]
      apply (div_lt_iff₀ hp).mpr
      have hmul := (div_lt_iff₀ hε).mp hnorm
      nlinarith only [hmul]
    have hz := hb (show w⁻¹ ∈ ball (0 : ℂ) ε by simpa only [mem_ball, dist_zero_right] using hi)
    change kelvin f w⁻¹ = 0 at hz
    simpa only [kelvin_of_ne_zero f (inv_ne_zero hw0), inv_inv] using hz
  · intro hf
    obtain ⟨R, hR⟩ := hf.isCompact.isBounded.subset_closedBall (0 : ℂ)
    have hC : 0 < |R| + 1 := by positivity
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (one_div_pos.mpr hC)] with z hz
    by_cases hz0 : z = 0
    · simp only [hz0, kelvin_zero]
    · rw [kelvin_of_ne_zero f hz0]
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have hb : ‖z⁻¹‖ ≤ R := by
        simpa only [mem_closedBall, dist_zero_right] using hR hmem
      have hsmall : ‖z‖ < 1 / (|R| + 1) := by
        simpa only [mem_ball, dist_zero_right] using hz
      have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      have hi : |R| + 1 < ‖z⁻¹‖ := by
        rw [norm_inv, ← one_div]
        apply (lt_div_iff₀ hp).mpr
        have hmul := (lt_div_iff₀ hC).mp hsmall
        nlinarith only [hmul]
      linarith only [hi, hb, le_abs_self R]

/-- A real-valued Schwartz inversion extension is analytic at the pole exactly for compact support. -/
theorem kelvin_analyticAt_iff (f : SchwartzMap ℂ ℝ) :
    AnalyticAt ℝ (kelvin f) 0 ↔ HasCompactSupport (f : ℂ → ℝ) := by
  constructor
  · intro hf
    have hz := eventuallyEq_const_of_iteratedFDeriv_eq_zero hf
      (fun n _ => kelvin_iteratedFDeriv_zero n f)
    simp only [kelvin_zero] at hz
    exact (kelvin_eventually_zero_iff f).mp hz
  · intro hf
    have hz := (kelvin_eventually_zero_iff f).mpr hf
    exact (analyticAt_const : AnalyticAt ℝ (fun _ : ℂ => (0 : ℝ)) 0).congr hz.symm

private theorem northCorrection_eventually_zero_iff (f : SchwartzMap ℂ ℝ) :
    (northCorrection f =ᶠ[𝓝 0] fun _ => 0) ↔ (kelvin f =ᶠ[𝓝 0] fun _ => 0) := by
  constructor
  · intro h
    filter_upwards [h] with z hz
    by_cases hz0 : z = 0
    · simp only [hz0, kelvin_zero]
    · have hq : ‖z‖ ^ 2 / (1 + ‖z‖ ^ 2) ≠ 0 :=
        div_ne_zero (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz0)) (by positivity)
      change (‖z‖ ^ 2 / (1 + ‖z‖ ^ 2)) * kelvin f z = 0 at hz
      exact (mul_eq_zero.mp hz).resolve_left hq
  · intro h
    filter_upwards [h] with z hz
    change (‖z‖ ^ 2 / (1 + ‖z‖ ^ 2)) * kelvin f z = 0
    rw [hz, mul_zero]

/-- The round-coordinate weight does not conceal a nonanalytic flat tail. -/
theorem northCorrection_analyticAt_iff (f : SchwartzMap ℂ ℝ) :
    AnalyticAt ℝ (northCorrection f) 0 ↔ HasCompactSupport (f : ℂ → ℝ) := by
  have hzero : northCorrection f 0 = 0 := by simp [northCorrection, kelvin_zero]
  constructor
  · intro hf
    have hz := eventuallyEq_const_of_iteratedFDeriv_eq_zero hf
      (fun n _ => northCorrection_iteratedFDeriv_zero f n)
    rw [hzero] at hz
    exact (kelvin_eventually_zero_iff f).mp ((northCorrection_eventually_zero_iff f).mp hz)
  · intro hf
    have hz := (northCorrection_eventually_zero_iff f).mpr ((kelvin_eventually_zero_iff f).mpr hf)
    exact (analyticAt_const : AnalyticAt ℝ (fun _ : ℂ => (0 : ℝ)) 0).congr hz.symm

#print axioms kelvin_eventually_zero_iff
#print axioms kelvin_analyticAt_iff
#print axioms northCorrection_analyticAt_iff
end
end GaloisForLFunctions.HilbertMetric.Geometry.SchwartzInversionAnalytic
