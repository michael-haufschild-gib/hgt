import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.SpecificLimits.Basic

open Complex Set Filter Metric
open scoped Topology
noncomputable section
namespace RHTower

/-- The exterior of a closed complex disc is path connected, with an explicit radial
surjection from the punctured plane. -/
theorem isPathConnected_complex_disc_exterior (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    IsPathConnected (closedBall c r)ᶜ := by
  let f : ℂ → ℂ := fun z => c + (1 + r / ‖z‖) • z
  have hcont : ContinuousOn f ({0}ᶜ : Set ℂ) := by
    intro z hz
    have hz0 : z ≠ 0 := by simpa using hz
    exact (continuousAt_const.add
      ((continuousAt_const.add (continuousAt_const.div continuousAt_id.norm
        (norm_ne_zero_iff.mpr hz0))).smul continuousAt_id)).continuousWithinAt
  have himage : f '' ({0}ᶜ : Set ℂ) = (closedBall c r)ᶜ := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr (by simpa using hz)
      have ha : 0 < 1 + r / ‖z‖ := by positivity
      have heq : ‖f z - c‖ = ‖z‖ + r := by
        dsimp only [f]
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
        field_simp
      rw [mem_compl_iff, mem_closedBall, dist_eq_norm, heq]
      linarith
    · intro w hw
      have hwr : r < ‖w - c‖ := by
        simpa only [mem_compl_iff, mem_closedBall, dist_eq_norm, not_le] using hw
      have hd : 0 < ‖w - c‖ := hr.trans_lt hwr
      let a : ℝ := 1 - r / ‖w - c‖
      have ha : 0 < a := by
        dsimp only [a]
        exact sub_pos.mpr ((div_lt_one hd).mpr hwr)
      let z : ℂ := a • (w - c)
      have hzNorm : ‖z‖ = ‖w - c‖ - r := by
        dsimp only [z]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
        dsimp only [a]
        field_simp
      have hz0 : z ≠ 0 := norm_pos_iff.mp (by rw [hzNorm]; linarith)
      refine ⟨z, by simpa using hz0, ?_⟩
      have hscalar : (1 + r / ‖z‖) * a = 1 := by
        rw [hzNorm]
        dsimp only [a]
        field_simp [hd.ne', (sub_pos.mpr hwr).ne']
        ring
      change c + (1 + r / ‖z‖) • (a • (w - c)) = w
      rw [smul_smul, hscalar, one_smul]
      ring
  have hpunct : IsPathConnected ({0}ᶜ : Set ℂ) :=
    isPathConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num) 0
  rw [← himage]
  exact hpunct.image' hcont

/-- An analytic transform on a connected domain containing zero is determined by its
values on the imaginary axis. -/
theorem eqOn_zero_of_analyticOnNhd_of_eq_imaginary
    {U : Set ℂ} {F : ℂ → ℂ} (hU : IsPreconnected U) (h0 : (0 : ℂ) ∈ U)
    (hF : AnalyticOnNhd ℂ F U) (haxis : ∀ t : ℝ, F ((t : ℂ) * I) = 0) :
    ∀ w ∈ U, F w = 0 := by
  have hbase : Tendsto (fun n : ℕ => ((1 / (n + 1 : ℝ) : ℝ) : ℂ) * I)
      atTop (𝓝 (0 : ℂ)) := by
    have hr : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hc := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hr
    simpa only [Function.comp_def, Complex.ofReal_zero, zero_mul] using hc.mul_const I
  have hpunc : Tendsto (fun n : ℕ => ((1 / (n + 1 : ℝ) : ℝ) : ℂ) * I)
      atTop (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hbase ?_
    filter_upwards with n
    simp only [mem_compl_iff, mem_singleton_iff, mul_eq_zero, Complex.ofReal_eq_zero]
    exact not_or.mpr ⟨by positivity, I_ne_zero⟩
  have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), F w = 0 :=
    hpunc.frequently (Filter.Frequently.of_forall fun n => haxis _)
  exact hF.eqOn_zero_of_preconnected_of_frequently_eq_zero hU h0 hfreq

end RHTower
