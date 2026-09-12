import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalHorizonFinitePartCurrent
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalFundamentalFrequencies

/-!
# The horizon source phase through the quasinormal frequency

The horizon Wronskian bracket of the continued response with the horizon mode equals the horizon
source phase wherever the connection coefficient is nonzero.  The phase itself carries no
connection denominator: the Wronskian cancels the horizon-mode component of the response, so the
phase is analytic in the frequency through every connection zero, and its endpoint-subtracted
finite part vanishes at every nonreal frequency with real part above `-2`, the fundamental
quasinormal frequencies included.  This is the analytic germ of the horizon bracket at the QNM.
-/

namespace RHTower.D4BMJointSource
open Complex Set Filter Topology Metric RHTower.D4BMLaplaceRadial RHTower.D4BMModularCore
  GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

/-- The horizon source phase is analytic in the frequency at every nonreal point off the source
rate, in particular through the connection zeros. -/
theorem continuedHorizonSourcePhase_frequency_analyticAt (s chi a J K w : ℂ) (hw : w.im ≠ 0)
    (hwre : -2 < w.re) (hs : w - 2 * s ≠ 0) {b : ℝ} (hb : b ∈ Ioo (0:ℝ) 1) :
    AnalyticAt ℂ (fun u => continuedHorizonSourcePhase s chi a J K b u) w := by
  have hM := horizonFirstMellin_analyticAt s chi a J K w hw hwre hb.1 hb.2
  have honset : AnalyticAt ℂ (fun u => onsetCorrection (2 * s) u) w :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr (onsetCorrection_entire (2 * s))) w
      (mem_univ _)
  have hinv : AnalyticAt ℂ (fun u => 1 / (u - 2 * s)) w :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) hs
  unfold continuedHorizonSourcePhase
  exact (hM.mul (hinv.add honset)).div analyticAt_const (by norm_num)

/-- The endpoint-subtracted horizon source phase vanishes in the horizon limit at every nonreal
frequency with real part above `-2`; no connection hypothesis is needed. -/
theorem continuedHorizonSourcePhase_finite_part_zero (s chi a J K w : ℂ) (hw : w.im ≠ 0)
    (hwre : -2 < w.re) :
    Tendsto (fun b : ℝ => continuedHorizonSourcePhase s chi a J K b w -
      continuedHorizonSourceCounterterm s chi a J K w b) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨R, C, hR, -, -, hbound⟩ := horizonMellinCore_uniform_first_bound s chi a J K w hw
    (b := 1 / 2) (by norm_num) (by norm_num)
  have hr := firstEndpointMellinRemainder_tendsto_zero (by norm_num : (0:ℝ) < 1 / 2) hwre
    (fun t ht => hbound w (mem_ball_self hR) t ⟨ht.1.le, ht.2⟩)
  have h := (hr.mul_const (1 / (w - 2 * s) + onsetCorrection (2 * s) w)).div_const 2
  simp only [zero_mul, zero_div] at h
  refine h.congr' (Filter.Eventually.of_forall (fun b => ?_))
  unfold continuedHorizonSourcePhase continuedHorizonSourceCounterterm firstEndpointMellin
  ring

/-- **Horizon bracket germ at a connection zero.** Near any nonreal frequency `w` off the source
rate, the horizon bracket of the continued response agrees on the punctured neighbourhood with a
function analytic at `w`, whose own endpoint-subtracted horizon limit at `w` is zero. -/
theorem continuedResponse_horizon_current_analytic_germ (s chi a J K w : ℂ) (hw : w.im ≠ 0)
    (hwre : -2 < w.re) (hs : w - 2 * s ≠ 0) {b : ℝ} (hb : b ∈ Ioo (0:ℝ) 1) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g w ∧
      (∀ᶠ u in 𝓝[≠] w, radialBracket (horizon u chi) (horizonFirst u chi)
        (fun t => continuedResponse s chi a J K t u)
        (deriv (fun t => continuedResponse s chi a J K t u)) b = g u) ∧
      g w = continuedHorizonSourcePhase s chi a J K b w :=
  ⟨fun u => continuedHorizonSourcePhase s chi a J K b u,
    continuedHorizonSourcePhase_frequency_analyticAt s chi a J K w hw hwre hs hb,
    continuedResponse_horizon_current_germ s chi a J K w hw hwre hb, rfl⟩

/-- The physical instance at both fundamental Xi quasinormal frequencies. -/
theorem physicalResponse_horizon_current_qnm_germ (q : XiZeroCopy) (branch side : Bool)
    (a J K : ℂ) {b : ℝ} (hb : b ∈ Ioo (0:ℝ) 1) :
    (∃ g : ℂ → ℂ, AnalyticAt ℂ g (physicalFundamentalFrequency q side) ∧
      (∀ᶠ u in 𝓝[≠] physicalFundamentalFrequency q side,
        radialBracket (horizon u (physicalRadialFrequency q)) (horizonFirst u (physicalRadialFrequency q))
          (fun t => continuedResponse (physicalRate q branch) (physicalRadialFrequency q) a J K t u)
          (deriv (fun t => continuedResponse (physicalRate q branch) (physicalRadialFrequency q) a J K t u))
          b = g u) ∧
      g (physicalFundamentalFrequency q side) =
        continuedHorizonSourcePhase (physicalRate q branch) (physicalRadialFrequency q) a J K b
          (physicalFundamentalFrequency q side)) ∧
    Tendsto (fun e : ℝ => continuedHorizonSourcePhase (physicalRate q branch) (physicalRadialFrequency q)
        a J K e (physicalFundamentalFrequency q side) -
      continuedHorizonSourceCounterterm (physicalRate q branch) (physicalRadialFrequency q) a J K
        (physicalFundamentalFrequency q side) e) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hw := physicalFundamentalFrequency_strip q side
  have hwr : -2 < (physicalFundamentalFrequency q side).re := (abs_lt.mp hw.2).1
  exact ⟨continuedResponse_horizon_current_analytic_germ _ _ a J K _ hw.1 hwr
    (physicalFundamentalFrequency_sub_sourceRate_ne_zero q branch side) hb,
    continuedHorizonSourcePhase_finite_part_zero _ _ a J K _ hw.1 hwr⟩

end
end RHTower.D4BMJointSource
