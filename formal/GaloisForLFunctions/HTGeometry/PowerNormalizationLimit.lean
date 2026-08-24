import GaloisForLFunctions.HTGeometry.EndpointIntegralAsymptotics

open Complex Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def positivePowerRescale (α : ℝ) (G : ℝ → E) (ω : ℝ) : E :=
  (((ω ^ (1 - α) : ℝ) : ℂ)) • G ω

theorem tendsto_positivePowerRescale_zero_of_lt {α : ℝ} (hα : α < 1)
    {G : ℝ → E} {T : E} (hG : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 T)) :
    Tendsto (positivePowerRescale α G) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hpR := HTGeometry.tendsto_rpow_nhdsGT_zero (sub_pos.mpr hα)
  have hpC : Tendsto (fun ω : ℝ => ((ω ^ (1 - α) : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto 0).comp hpR
  change Tendsto (fun ω : ℝ => ((ω ^ (1 - α) : ℝ) : ℂ) • G ω)
    (𝓝[>] (0 : ℝ)) (𝓝 0)
  simpa only [zero_smul] using hpC.smul hG

theorem positivePowerRescale_one (G : ℝ → E) :
    positivePowerRescale 1 G = G := by
  funext ω
  simp [positivePowerRescale]

theorem tendsto_positivePowerRescale_one {G : ℝ → E} {T : E}
    (hG : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 T)) :
    Tendsto (positivePowerRescale 1 G) (𝓝[>] (0 : ℝ)) (𝓝 T) := by
  simpa [positivePowerRescale_one] using hG

theorem tendsto_rpow_nhdsGT_zero_atTop_of_neg {β : ℝ} (hβ : β < 0) :
    Tendsto (fun ω : ℝ => ω ^ β) (𝓝[>] (0 : ℝ)) atTop := by
  have hmul := Real.tendsto_log_nhdsGT_zero.const_mul_atBot_of_neg hβ
  have hexp := Real.tendsto_exp_atTop.comp hmul
  apply hexp.congr'
  filter_upwards [self_mem_nhdsWithin] with ω hω
  simp only [Function.comp_apply, Real.rpow_def_of_pos hω, mul_comm]

theorem tendsto_norm_positivePowerRescale_atTop_of_gt {α : ℝ} (hα : 1 < α)
    {G : ℝ → E} {T : E} (hG : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 T))
    (hT : T ≠ 0) :
    Tendsto (fun ω => ‖positivePowerRescale α G ω‖)
      (𝓝[>] (0 : ℝ)) atTop := by
  have hnormT : 0 < ‖T‖ := norm_pos_iff.mpr hT
  have hnormG := hG.norm
  have hhalf : ∀ᶠ ω in 𝓝[>] (0 : ℝ), ‖T‖ / 2 ≤ ‖G ω‖ := by
    have hopen : Set.Ioi (‖T‖ / 2) ∈ 𝓝 ‖T‖ := by
      exact Ioi_mem_nhds (by linarith)
    filter_upwards [hnormG.eventually hopen] with ω hω
    exact hω.le
  have hpow := tendsto_rpow_nhdsGT_zero_atTop_of_neg (sub_neg.mpr hα)
  have hscaled := hpow.const_mul_atTop (by linarith : 0 < ‖T‖ / 2)
  refine tendsto_atTop_mono' (𝓝[>] (0 : ℝ)) ?_ hscaled
  filter_upwards [self_mem_nhdsWithin, hhalf] with ω hω hlower
  rw [positivePowerRescale, norm_smul]
  have hp : 0 < ω ^ (1 - α) := Real.rpow_pos_of_pos hω _
  simpa [Real.norm_eq_abs, abs_of_pos hp, mul_comm] using
    (mul_le_mul_of_nonneg_left hlower hp.le)

end GaloisForLFunctions.HTGeometry

