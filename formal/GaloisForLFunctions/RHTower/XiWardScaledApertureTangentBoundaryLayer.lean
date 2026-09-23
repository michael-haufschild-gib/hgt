import GaloisForLFunctions.RHTower.XiWardInfinitesimalDefectIndexQuantization
import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardEulerEdgeCompleteness

open Complex Filter Topology Set

namespace RHTower

noncomputable section

private theorem hasDerivAt_realAperture_of_complex_zero'
    {f : ℂ → ℂ} {f' : ℂ} (h : HasDerivAt f f' 0) :
    HasDerivAt (fun x : ℝ => f x) f' 0 := by
  have houter : HasFDerivAt f
      ((ContinuousLinearMap.toSpanSingleton ℂ f').restrictScalars ℝ)
      (Complex.ofRealCLM 0) := by
    simpa using h.hasFDerivAt.restrictScalars ℝ
  have hcomp := houter.comp (0 : ℝ) Complex.ofRealCLM.hasFDerivAt
  show HasFDerivAt (fun x : ℝ => f x)
    (ContinuousLinearMap.toSpanSingleton ℝ f') 0
  simpa using! hcomp

/-- The exact source-row homogeneity required before singular aperture division. -/
def XiWardScaledApertureFourUnitLaw : Prop :=
  ∀ (t a : ℝ), 0 < a →
    Complex.normSq
        (mobiusGammaXiAntiCausalWardTransportV
          ((1 / 2 : ℂ) + I * (t : ℂ)) (a : ℂ)) ≤
      4 * a ^ (2 : ℕ)

private theorem tendsto_scaled_transport_normSq
    {w : ℂ} (hw : 0 < w.re) :
    Tendsto
      (fun a : ℝ =>
        Complex.normSq
          (mobiusGammaXiAntiCausalWardTransportV w (a : ℂ) / (a : ℂ)))
      (𝓝[>] 0)
      (𝓝 (Complex.normSq (continuedXiAntiCausalWardResponse w))) := by
  have hderiv : HasDerivAt
      (fun a : ℝ =>
        mobiusGammaXiAntiCausalWardTransportV w (a : ℂ))
      (continuedXiAntiCausalWardResponse w) 0 :=
    hasDerivAt_realAperture_of_complex_zero'
      (hasDerivAt_mobiusGammaXiAntiCausalWardTransportV_zero hw)
  have hzero : mobiusGammaXiAntiCausalWardTransportV w 0 = 0 :=
    mobiusGammaXiAntiCausalWardTransportV_zero hw
  have hslope : Tendsto
      (fun a : ℝ =>
        mobiusGammaXiAntiCausalWardTransportV w (a : ℂ) / (a : ℂ))
      (𝓝[>] 0) (𝓝 (continuedXiAntiCausalWardResponse w)) := by
    convert hderiv.tendsto_slope_zero_right using 1
    ext a
    simp [hzero, div_eq_inv_mul]
  exact Complex.continuous_normSq.continuousAt.tendsto.comp hslope

/-- Scaled aperture control implies the closed four-unit Ward bound on the
Euler edge. -/
theorem continuedXiWardEulerEdgeScalarLaw_of_scaledApertureFourUnitLaw
    (hscaled : XiWardScaledApertureFourUnitLaw) :
    ContinuedXiWardEulerEdgeScalarLaw := by
  intro t
  let w : ℂ := (1 / 2 : ℂ) + I * (t : ℂ)
  have hw : 0 < w.re := by
    norm_num [w, Complex.add_re, Complex.mul_re]
  have hlim := tendsto_scaled_transport_normSq hw
  apply le_of_tendsto hlim
  have hpos : ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a := self_mem_nhdsWithin
  filter_upwards [hpos] with a ha
  have hsource := hscaled t a ha
  rw [Complex.normSq_div, Complex.normSq_ofReal]
  rw [div_le_iff₀ (by positivity : 0 < a * a)]
  simpa only [w, pow_two] using hsource

/-- The scaled aperture source-row law is exactly equivalent to RH. -/
theorem riemannHypothesis_iff_xiWardScaledApertureFourUnitLaw :
    RiemannHypothesis ↔ XiWardScaledApertureFourUnitLaw := by
  constructor
  · intro hRH t a ha
    have hw : 0 < ((1 / 2 : ℂ) + I * (t : ℂ)).re := by
      norm_num [Complex.add_re, Complex.mul_re]
    rw [(riemannHypothesis_iff_mobiusGammaXiAntiCausalWardTransportV_eq_zero
      hw ha).mp hRH]
    norm_num
    positivity
  · intro hscaled
    exact riemannHypothesis_of_continuedXiWardEulerEdgeScalarLaw
      (continuedXiWardEulerEdgeScalarLaw_of_scaledApertureFourUnitLaw hscaled)

/-- Every strict-right zero forces failure of scaled source-row control at all
sufficiently small positive apertures around its adapted Euler-edge node. -/
theorem eventually_normSq_mobiusGammaXiAntiCausalWardTransportV_gt_scaled_four
    (q : XiRightUpperZeroCopy) :
    ∀ᶠ a : ℝ in 𝓝[>] 0,
      4 * a ^ (2 : ℕ) <
        Complex.normSq
          (mobiusGammaXiAntiCausalWardTransportV
            (xiWardEulerEdgeAdaptedNode q) (a : ℂ)) := by
  have hw : 0 < (xiWardEulerEdgeAdaptedNode q).re := by
    rw [xiWardEulerEdgeAdaptedNode_re]
    norm_num
  have hlim := tendsto_scaled_transport_normSq hw
  have hgt : 4 < Complex.normSq
      (continuedXiAntiCausalWardResponse
        (xiWardEulerEdgeAdaptedNode q)) :=
    normSq_continuedXiAntiCausalWardResponse_at_eulerEdge_gt_four q
  have hquot : ∀ᶠ a : ℝ in 𝓝[>] 0,
      4 < Complex.normSq
        (mobiusGammaXiAntiCausalWardTransportV
          (xiWardEulerEdgeAdaptedNode q) (a : ℂ) / (a : ℂ)) :=
    hlim.eventually (Ioi_mem_nhds hgt)
  have hpos : ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a := self_mem_nhdsWithin
  filter_upwards [hquot, hpos] with a hqa ha
  rw [Complex.normSq_div, Complex.normSq_ofReal] at hqa
  have hqa' := (lt_div_iff₀ (by positivity : 0 < a * a)).mp hqa
  simpa only [pow_two] using hqa'

/-- If RH fails, a concrete adapted Euler-edge node has a whole punctured
right neighborhood of scaled source-row violations. -/
theorem exists_eventually_scaledApertureFourUnit_violation_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    ∃ q : XiRightUpperZeroCopy,
      ∀ᶠ a : ℝ in 𝓝[>] 0,
        4 * a ^ (2 : ℕ) <
          Complex.normSq
            (mobiusGammaXiAntiCausalWardTransportV
              (xiWardEulerEdgeAdaptedNode q) (a : ℂ)) := by
  obtain ⟨q⟩ := nonempty_xiRightUpperZeroCopy_for_boundaryLift hRH
  exact ⟨q,
    eventually_normSq_mobiusGammaXiAntiCausalWardTransportV_gt_scaled_four q⟩

end

end RHTower
