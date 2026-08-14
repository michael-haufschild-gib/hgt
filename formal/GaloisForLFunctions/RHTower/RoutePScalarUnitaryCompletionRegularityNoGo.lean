import GaloisForLFunctions.RHTower.RoutePFirstOrderSlackNoGo

/-!
# Route-P scalar unitary-completion regularity no-go

The fixed-node Xi phase is an unconditional scalar contraction.  Any exact
Hilbert defect completion has energy equal to its Julia defect.  P-G162
shows that this energy opens linearly when RH fails.  Consequently the
defect vector is intrinsically square-root scale and cannot have a finite
aperture derivative at zero.

Thus a differentiable block-unitary completion of the already scalarized Xi
phase is itself an RH receiver, not an unconditional producer.  A viable
Route-P unitary incidence must retain a vector-valued causal source before
scalar compression, cancelling first-order norm loss there.
-/

open Complex Filter

namespace RHTower

noncomputable section

/-- Every exact Hilbert defect completion of the fixed-node scalar phase has
the same first-order energy density, namely twice the real Ward response. -/
theorem tendsto_norm_sq_div_aperture_scalarXiPhase_unitaryDefect
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (c : ℝ → F)
    (hunit : ∀ a : ℝ,
      Complex.normSq
          (xiRightWardBoundarySourcePhaseCrossRatio
            (I * (1 / 2 : ℂ)) (a : ℂ)) +
        ‖c a‖ ^ 2 = 1) :
    Tendsto (fun a : ℝ => ‖c a‖ ^ 2 / a)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (2 *
        (continuedXiAntiCausalWardResponse (1 / 2 : ℂ)).re)) := by
  have hhalf : 0 < ((1 / 2 : ℂ)).re := by norm_num
  have hzero : xiWardBoundaryPhaseDefect (1 / 2 : ℂ) 0 = 0 := by
    rw [xiWardBoundaryPhaseDefect_eq_transport hhalf]
    norm_num [mobiusGammaXiAntiCausalWardTransportV_zero hhalf]
  have hdefect : ∀ a : ℝ,
      xiWardBoundaryPhaseDefect (1 / 2 : ℂ) a = ‖c a‖ ^ 2 := by
    intro a
    rw [xiWardBoundaryPhaseDefect]
    linarith [hunit a]
  have hslope :=
    (hasDerivAt_xiWardBoundaryPhaseDefect_zero hhalf).tendsto_slope_zero_right
  convert hslope using 1
  ext a
  rw [zero_add, hdefect a, hzero, sub_zero]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

/-- A differentiable Hilbert defect vector completing the fixed-node scalar
Xi phase to exact unit norm would force RH. -/
theorem riemannHypothesis_of_differentiable_scalarXiPhase_unitaryCompletion
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (c : ℝ → F) (c' : F)
    (hc0 : c 0 = 0) (hc : HasDerivAt c c' 0)
    (hunit : ∀ a : ℝ,
      Complex.normSq
          (xiRightWardBoundarySourcePhaseCrossRatio
            (I * (1 / 2 : ℂ)) (a : ℂ)) +
        ‖c a‖ ^ 2 = 1) :
    RiemannHypothesis := by
  have hdefect : xiWardBoundaryPhaseDefect (1 / 2 : ℂ) =
      fun a : ℝ => ‖c a‖ ^ 2 := by
    funext a
    rw [xiWardBoundaryPhaseDefect]
    linarith [hunit a]
  have hcNorm : HasDerivAt (fun a : ℝ => ‖c a‖ ^ 2) 0 0 := by
    have h := hc.norm_sq
    rw [hc0, inner_zero_left, mul_zero] at h
    exact h
  have hdefectZero : HasDerivAt
      (xiWardBoundaryPhaseDefect (1 / 2 : ℂ)) 0 0 := by
    rw [hdefect]
    exact hcNorm
  have hhalf : 0 < ((1 / 2 : ℂ)).re := by norm_num
  have hward := hasDerivAt_xiWardBoundaryPhaseDefect_zero hhalf
  have hreZero : 2 *
      (continuedXiAntiCausalWardResponse (1 / 2 : ℂ)).re = 0 :=
    hward.unique hdefectZero
  by_contra hRH
  have hpos := re_continuedXiAntiCausalWardResponse_half_pos_of_not_rh hRH
  linarith

/-- Under false RH, no Hilbert-valued exact unitary defect completion of the
fixed-node scalar phase can have a finite derivative at aperture zero. -/
theorem no_hasDerivAt_scalarXiPhase_unitaryDefect_of_not_rh
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (hRH : ¬ RiemannHypothesis) (c : ℝ → F) (hc0 : c 0 = 0)
    (hunit : ∀ a : ℝ,
      Complex.normSq
          (xiRightWardBoundarySourcePhaseCrossRatio
            (I * (1 / 2 : ℂ)) (a : ℂ)) +
        ‖c a‖ ^ 2 = 1) :
    ∀ c' : F, ¬ HasDerivAt c c' 0 := by
  intro c' hc
  exact hRH
    (riemannHypothesis_of_differentiable_scalarXiPhase_unitaryCompletion
      c c' hc0 hc hunit)

end

end RHTower
