import GaloisForLFunctions.RHTower.XiWardScaledApertureTangentBoundaryLayer

open Complex Filter Topology Set

namespace RHTower

noncomputable section

theorem xiRightWardBoundarySourcePhaseCrossRatio_mul_neg_eq_one
    {w : ℂ} {a : ℝ} (hw : 0 < w.re) (ha : 0 ≤ a)
    (haw : a < w.re) :
    xiRightWardBoundarySourcePhaseCrossRatio (I * w) (a : ℂ) *
        xiRightWardBoundarySourcePhaseCrossRatio (I * w) ((-a : ℝ) : ℂ) = 1 := by
  have hplus : xiRightCanonicalProduct
      (I * w + (a : ℂ) * I) ≠ 0 :=
    xiRightCanonicalProduct_boundary_shift_ne_zero hw ha
  have hwminus : 0 < (w - (a : ℂ)).re := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  have hminus' : xiRightCanonicalProduct
      (I * (w - (a : ℂ)) + (0 : ℂ) * I) ≠ 0 :=
    xiRightCanonicalProduct_boundary_shift_ne_zero hwminus (le_refl 0)
  have hminus : xiRightCanonicalProduct
      (I * w - (a : ℂ) * I) ≠ 0 := by
    simpa [mul_sub, mul_comm] using hminus'
  have hminusI : xiRightCanonicalProduct (I * (w - (a : ℂ))) ≠ 0 := by
    simpa [mul_sub, mul_comm] using hminus
  have hplusI : xiRightCanonicalProduct (I * (w + (a : ℂ))) ≠ 0 := by
    simpa [mul_add, mul_comm] using hplus
  simp only [xiRightWardBoundarySourcePhaseCrossRatio,
    xiRightWardSourcePhase, xiAntiCausalWardBoundarySourcePhase,
    Complex.ofReal_neg]
  rw [show I * w - -(a : ℂ) * I = I * w + (a : ℂ) * I by ring,
    show I * w + -(a : ℂ) * I = I * w - (a : ℂ) * I by ring,
    show -(a : ℂ) * xiAntiCausalWardBoundarySelfSymbol =
      -((a : ℂ) * xiAntiCausalWardBoundarySelfSymbol) by ring,
    Complex.exp_neg]
  field_simp [hminus, hplus, hminusI, hplusI, Complex.exp_ne_zero]

theorem mobiusGammaXiAntiCausalWardTransportV_aperture_conservation
    {w : ℂ} {a : ℝ} (hw : 0 < w.re) (ha : 0 ≤ a)
    (haw : a < w.re) :
    (1 - mobiusGammaXiAntiCausalWardTransportV w (a : ℂ)) *
        (1 - mobiusGammaXiAntiCausalWardTransportV w ((-a : ℝ) : ℂ)) = 1 := by
  rw [mobiusGammaXiAntiCausalWardTransportV_eq_one_sub_phase hw,
    mobiusGammaXiAntiCausalWardTransportV_eq_one_sub_phase hw]
  simp only [sub_sub_cancel]
  exact xiRightWardBoundarySourcePhaseCrossRatio_mul_neg_eq_one hw ha haw

theorem mobiusGammaXiAntiCausalWardTransportV_add_neg_eq_mul
    {w : ℂ} {a : ℝ} (hw : 0 < w.re) (ha : 0 ≤ a)
    (haw : a < w.re) :
    mobiusGammaXiAntiCausalWardTransportV w (a : ℂ) +
        mobiusGammaXiAntiCausalWardTransportV w ((-a : ℝ) : ℂ) =
      mobiusGammaXiAntiCausalWardTransportV w (a : ℂ) *
        mobiusGammaXiAntiCausalWardTransportV w ((-a : ℝ) : ℂ) := by
  have h := mobiusGammaXiAntiCausalWardTransportV_aperture_conservation hw ha haw
  linear_combination -h

private theorem hasDerivAt_realAperture_of_complex_zero''
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

/-- Symmetric aperture folding, normalized at its first surviving order. -/
def xiWardSymmetricApertureCurvature (w : ℂ) (a : ℝ) : ℂ :=
  (mobiusGammaXiAntiCausalWardTransportV w (a : ℂ) +
      mobiusGammaXiAntiCausalWardTransportV w ((-a : ℝ) : ℂ)) /
    (a : ℂ) ^ 2

/-- Aperture reversal erases the linear Ward row. Its normalized two-sided
curvature is forced to be the negative complex square of that row, so it
contains no independent positive energy. -/
theorem tendsto_xiWardSymmetricApertureCurvature_zero_right
    {w : ℂ} (hw : 0 < w.re) :
    Tendsto (xiWardSymmetricApertureCurvature w) (𝓝[>] 0)
      (𝓝 (-(continuedXiAntiCausalWardResponse w) ^ 2)) := by
  let V : ℝ → ℂ := fun a =>
    mobiusGammaXiAntiCausalWardTransportV w (a : ℂ)
  let r : ℂ := continuedXiAntiCausalWardResponse w
  have hV : HasDerivAt V r 0 :=
    hasDerivAt_realAperture_of_complex_zero''
      (hasDerivAt_mobiusGammaXiAntiCausalWardTransportV_zero hw)
  have hV0 : V 0 = 0 := by
    exact mobiusGammaXiAntiCausalWardTransportV_zero hw
  have hplus : Tendsto (fun a : ℝ => V a / (a : ℂ))
      (𝓝[>] 0) (𝓝 r) := by
    convert hV.tendsto_slope_zero_right using 1
    ext a
    simp [hV0, div_eq_inv_mul]
  have hVneg : HasDerivAt (fun a : ℝ => V (-a)) (-r) 0 := by
    have hV' : HasDerivAt V r (-0) := by simpa using hV
    simpa [Function.comp_def] using
      hV'.scomp 0 (hasDerivAt_neg 0)
  have hminus : Tendsto (fun a : ℝ => V (-a) / (a : ℂ))
      (𝓝[>] 0) (𝓝 (-r)) := by
    convert hVneg.tendsto_slope_zero_right using 1
    ext a
    simp [hV0, div_eq_inv_mul]
  have hproduct : Tendsto
      (fun a : ℝ => (V a / (a : ℂ)) * (V (-a) / (a : ℂ)))
      (𝓝[>] 0) (𝓝 (-(r ^ 2))) := by
    simpa [pow_two] using hplus.mul hminus
  apply hproduct.congr'
  have hpos : ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a := self_mem_nhdsWithin
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0, a < w.re :=
    (eventually_lt_nhds hw).filter_mono inf_le_left
  filter_upwards [hpos, hsmall] with a ha haw
  have hfold := mobiusGammaXiAntiCausalWardTransportV_add_neg_eq_mul
    hw ha.le haw
  change (V a / (a : ℂ)) * (V (-a) / (a : ℂ)) =
    xiWardSymmetricApertureCurvature w a
  dsimp only [V]
  rw [xiWardSymmetricApertureCurvature, hfold]
  field_simp [ha.ne']

/-- At an off-line adapted node, symmetric folding does not dilute the
four-unit violation: its quadratic survivor eventually crosses sixteen. -/
theorem eventually_sixteen_lt_normSq_xiWardSymmetricApertureCurvature
    (q : XiRightUpperZeroCopy) :
    ∀ᶠ a : ℝ in 𝓝[>] 0,
      16 < Complex.normSq
        (xiWardSymmetricApertureCurvature
          (xiWardEulerEdgeAdaptedNode q) a) := by
  let w := xiWardEulerEdgeAdaptedNode q
  let r := continuedXiAntiCausalWardResponse w
  have hw : 0 < w.re := by
    rw [xiWardEulerEdgeAdaptedNode_re]
    norm_num
  have hlim := Complex.continuous_normSq.continuousAt.tendsto.comp
    (tendsto_xiWardSymmetricApertureCurvature_zero_right hw)
  have hlimit : Complex.normSq (-(r ^ 2)) =
      (Complex.normSq r) ^ 2 := by
    simp only [Complex.normSq_neg, map_pow]
  rw [hlimit] at hlim
  have hr : 4 < Complex.normSq r := by
    exact normSq_continuedXiAntiCausalWardResponse_at_eulerEdge_gt_four q
  have hsixteen : 16 < (Complex.normSq r) ^ 2 := by
    nlinarith [Complex.normSq_nonneg r]
  exact hlim.eventually (Ioi_mem_nhds hsixteen)

end

end RHTower
