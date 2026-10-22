import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalHorizonFinitePart
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLaplaceContinuedForcedODE

/-! The source-determined horizon finite part is the original continued radial boundary current. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Filter Topology Set GaloisForLFunctions.HTGeometry D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The finite part equals the bracket of the original response and its actual derivative. -/
theorem continuedResponse_horizon_current_eq (s chi a J K w : ℂ) (hw : w.im ≠ 0)
    (hwre : -2 < w.re) (hc : connection w chi ≠ 0) {b : ℝ} (hb : b ∈ Ioo 0 1) :
    radialBracket (horizon w chi) (horizonFirst w chi)
      (fun t => continuedResponse s chi a J K t w)
      (deriv (fun t => continuedResponse s chi a J K t w)) b =
      continuedHorizonSourcePhase s chi a J K b w := by
  unfold radialBracket
  rw [(continuedResponse_deriv_eq s chi a J K w hw hwre hb).1]
  calc
    _ = wronskian w chi b*continuedHorizonMoment s chi a J K b w := by
      dsimp [radialBracket,continuedResponse,continuedResponseFirst,wronskian]
      ring
    _ = _ := by
      rw [wronskian_eq_continued w chi hw hb]
      dsimp [continuedHorizonMoment,continuedHorizonSourcePhase]
      field_simp [hc]

/-- The original boundary-current identification continues through each connection zero as a germ. -/
theorem continuedResponse_horizon_current_germ (s chi a J K w : ℂ) (hw : w.im ≠ 0)
    (hwre : -2 < w.re) {b : ℝ} (hb : b ∈ Ioo 0 1) :
    ∀ᶠ u in 𝓝[≠] w, radialBracket (horizon u chi) (horizonFirst u chi)
      (fun t => continuedResponse s chi a J K t u)
      (deriv (fun t => continuedResponse s chi a J K t u)) b =
      continuedHorizonSourcePhase s chi a J K b u := by
  have hi := (Complex.continuous_im.continuousAt.eventually_ne hw).filter_mono
    (show 𝓝[≠] w ≤ 𝓝 w from inf_le_left)
  have hr := (Complex.continuous_re.continuousAt.eventually_const_lt hwre).filter_mono
    (show 𝓝[≠] w ≤ 𝓝 w from inf_le_left)
  filter_upwards [hi,hr,connection_eventually_ne_zero w chi hw] with u hui hur huc
  exact continuedResponse_horizon_current_eq s chi a J K u hui hur huc hb

/-- The source-determined endpoint subtraction leaves zero horizon boundary current. -/
theorem continuedResponse_horizon_current_finite_part_zero (s chi a J K w : ℂ) (hw : w.im ≠ 0)
    (hwre : -2 < w.re) (hc : connection w chi ≠ 0) :
    Tendsto (fun b : ℝ => radialBracket (horizon w chi) (horizonFirst w chi)
      (fun t => continuedResponse s chi a J K t w)
      (deriv (fun t => continuedResponse s chi a J K t w)) b-
        continuedHorizonSourceCounterterm s chi a J K w b)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨R,C,hR,-,-,hbound⟩ := horizonMellinCore_uniform_first_bound s chi a J K w hw
    (b := 1/2) (by norm_num) (by norm_num)
  have hr := firstEndpointMellinRemainder_tendsto_zero (by norm_num : (0:ℝ)<1/2) hwre
    (fun t ht => hbound w (Metric.mem_ball_self hR) t ⟨ht.1.le,ht.2⟩)
  have h := (hr.mul_const (1/(w-2*s)+onsetCorrection (2*s) w)).div_const 2
  simp only [zero_mul,zero_div] at h
  apply h.congr'
  have he : ∀ᶠ b : ℝ in 𝓝[>] (0:ℝ), b < 1 :=
    (show ∀ᶠ b : ℝ in 𝓝 (0:ℝ), b < 1 from Iio_mem_nhds (by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,he] with b hb0 hb1
  rw [continuedResponse_horizon_current_eq s chi a J K w hw hwre hc ⟨hb0,hb1⟩]
  dsimp [continuedHorizonSourcePhase,continuedHorizonSourceCounterterm,firstEndpointMellin]
  ring

end
end RHTower.D4BMLaplaceRadial
