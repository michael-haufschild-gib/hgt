import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLaplaceGaussFactors

/-! Low-dependency nonreal-frequency parameter control for the literal Gauss factor. -/

namespace RHTower.D4BMLaplaceRadial
open Complex Filter Topology Set Metric
noncomputable section
set_option autoImplicit false

theorem horizonGauss_parameter_neighborhood_core (w chi : ℂ) (hw : w.im ≠ 0) :
    ∃ R B δ : ℝ, 0 < R ∧ R ≤ 1 ∧ 0 < B ∧ 0 < δ ∧
      ∀ u ∈ ball w R, ‖gaussA u chi‖ ≤ B ∧ ‖gaussB u chi‖ ≤ B ∧ ‖gaussC u‖ ≤ B ∧
        δ ≤ |u.im| := by
  let B := ‖gaussA w chi‖ + ‖gaussB w chi‖ + ‖gaussC w‖ + 1
  let δ := |w.im| / 2
  have hδ : 0 < δ := div_pos (abs_pos.mpr hw) (by norm_num)
  have hA : ∀ᶠ u in 𝓝 w, ‖gaussA u chi‖ < B :=
    (show ContinuousAt (fun u => ‖gaussA u chi‖) w by unfold gaussA; fun_prop).eventually_lt
      continuousAt_const (by
        dsimp [B]
        linarith [norm_nonneg (gaussB w chi), norm_nonneg (gaussC w)])
  have hB : ∀ᶠ u in 𝓝 w, ‖gaussB u chi‖ < B :=
    (show ContinuousAt (fun u => ‖gaussB u chi‖) w by unfold gaussB; fun_prop).eventually_lt
      continuousAt_const (by
        dsimp [B]
        linarith [norm_nonneg (gaussA w chi), norm_nonneg (gaussC w)])
  have hC : ∀ᶠ u in 𝓝 w, ‖gaussC u‖ < B :=
    (show ContinuousAt (fun u => ‖gaussC u‖) w by unfold gaussC; fun_prop).eventually_lt
      continuousAt_const (by
        dsimp [B]
        linarith [norm_nonneg (gaussA w chi), norm_nonneg (gaussB w chi)])
  have hi : ∀ᶠ u : ℂ in 𝓝 w, δ < |u.im| := continuousAt_const.eventually_lt
    (by fun_prop) (by
      dsimp [δ]
      linarith [abs_pos.mpr hw])
  obtain ⟨R, hR, hall⟩ := Metric.eventually_nhds_iff.mp (hA.and (hB.and (hC.and hi)))
  refine ⟨min R 1, B, δ, lt_min hR (by norm_num), min_le_right _ _, by dsimp [B]; positivity,
    hδ, ?_⟩
  intro u hu
  obtain ⟨ha, hb, hc, hd⟩ := hall ((mem_ball.mp hu).trans_le (min_le_left _ _))
  exact ⟨ha.le, hb.le, hc.le, hd.le⟩

end
end RHTower.D4BMLaplaceRadial
