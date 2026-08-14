import GaloisForLFunctions.RHTower.RoutePScalarUnitaryCompletionRegularityNoGo
import GaloisForLFunctions.HTGeometry.SkewFrequencyCurrent

/-!
# Route-P differentiable unit-frame overlap no-go

P-G163 excludes differentiable Hilbert defect completions after the Xi phase
has been scalarized.  A possible escape would be to realize that phase before
scalarization as the overlap of two moving unit source frames.

This module excludes that larger class.  If two differentiable unit vectors
meet at aperture zero, the real part of their overlap derivative vanishes:
both tangent vectors lie in the real tangent hyperplane of the unit sphere.
The fixed-node Xi phase instead has radial derivative

`-Re (continuedXiAntiCausalWardResponse (1 / 2))`,

which is strictly negative when RH fails.  Hence a differentiable unit-frame
overlap realization is already an RH receiver.  A viable pre-divisor
incidence cannot realize the scalar Xi phase as a coefficient of two unit
paths; it must retain the division-free graph-normal channel and cancel its
linear loss before this scalar observation.
-/

open Complex
open scoped InnerProductSpace

namespace RHTower

noncomputable section

private theorem hasDerivAt_realAperture_of_complex_zero
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

private theorem hasDerivAt_real_scalarXiPhase_at_zero :
    HasDerivAt
      (fun a : ℝ =>
        xiRightWardBoundarySourcePhaseCrossRatio
          (I * (1 / 2 : ℂ)) (a : ℂ))
      (-(continuedXiAntiCausalWardResponse (1 / 2 : ℂ))) 0 := by
  have hhalf : 0 < ((1 / 2 : ℂ)).re := by norm_num
  have hVcomplex : HasDerivAt
      (mobiusGammaXiAntiCausalWardTransportV (1 / 2 : ℂ))
      (continuedXiAntiCausalWardResponse (1 / 2 : ℂ)) 0 :=
    hasDerivAt_mobiusGammaXiAntiCausalWardTransportV_zero hhalf
  have hVreal : HasDerivAt
      (fun a : ℝ => mobiusGammaXiAntiCausalWardTransportV
        (1 / 2 : ℂ) (a : ℂ))
      (continuedXiAntiCausalWardResponse (1 / 2 : ℂ)) 0 := by
    exact hasDerivAt_realAperture_of_complex_zero hVcomplex
  have hphase : (fun a : ℝ =>
        xiRightWardBoundarySourcePhaseCrossRatio
          (I * (1 / 2 : ℂ)) (a : ℂ)) =
      fun a : ℝ => 1 - mobiusGammaXiAntiCausalWardTransportV
        (1 / 2 : ℂ) (a : ℂ) := by
    funext a
    rw [mobiusGammaXiAntiCausalWardTransportV_eq_one_sub_phase hhalf]
    ring
  rw [hphase]
  exact hVreal.const_sub (1 : ℂ)

/-- Two differentiable unit source frames that meet at aperture zero have a
phase-only first-order overlap: its radial derivative vanishes. -/
theorem re_overlap_deriv_eq_zero_of_unit_paths
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [NormedSpace ℝ F]
    {x y : ℝ → F} {x' y' e : F}
    (hx : HasDerivAt x x' 0) (hy : HasDerivAt y y' 0)
    (hx0 : x 0 = e) (hy0 : y 0 = e)
    (hunitx : ∀ a : ℝ, ‖x a‖ ^ 2 = 1)
    (hunity : ∀ a : ℝ, ‖y a‖ ^ 2 = 1) :
    ((inner ℂ (x 0) y' + inner ℂ x' (y 0) : ℂ)).re = 0 := by
  have hnx := GaloisForLFunctions.HTGeometry.hasDerivAt_normSq_path hx
  have hny := GaloisForLFunctions.HTGeometry.hasDerivAt_normSq_path hy
  have hdx : 2 * (inner ℂ x' (x 0) : ℂ).re = 0 := by
    rw [funext hunitx] at hnx
    exact hnx.unique (hasDerivAt_const (0 : ℝ) (1 : ℝ))
  have hdy : 2 * (inner ℂ y' (y 0) : ℂ).re = 0 := by
    rw [funext hunity] at hny
    exact hny.unique (hasDerivAt_const (0 : ℝ) (1 : ℝ))
  rw [hx0, hy0, Complex.add_re, ← inner_conj_symm e y',
    Complex.conj_re]
  rw [hx0] at hdx
  rw [hy0] at hdy
  linarith

/-- A differentiable realization of the fixed-node Xi phase as the overlap
of two unit source paths meeting at the base point forces RH. -/
theorem riemannHypothesis_of_differentiable_unitFrame_scalarXiPhase
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [NormedSpace ℝ F]
    (x y : ℝ → F) (x' y' e : F)
    (hx : HasDerivAt x x' 0) (hy : HasDerivAt y y' 0)
    (hx0 : x 0 = e) (hy0 : y 0 = e)
    (hunitx : ∀ a : ℝ, ‖x a‖ ^ 2 = 1)
    (hunity : ∀ a : ℝ, ‖y a‖ ^ 2 = 1)
    (hoverlap : ∀ a : ℝ,
      inner ℂ (x a) (y a) =
        xiRightWardBoundarySourcePhaseCrossRatio
          (I * (1 / 2 : ℂ)) (a : ℂ)) :
    RiemannHypothesis := by
  have hxy := hx.inner ℂ hy
  have hxyPhase : HasDerivAt
      (fun a : ℝ => inner ℂ (x a) (y a))
      (-(continuedXiAntiCausalWardResponse (1 / 2 : ℂ))) 0 := by
    rw [funext hoverlap]
    exact hasDerivAt_real_scalarXiPhase_at_zero
  have hderiv := hxy.unique hxyPhase
  have hre := re_overlap_deriv_eq_zero_of_unit_paths
    hx hy hx0 hy0 hunitx hunity
  rw [hderiv] at hre
  simp only [neg_re] at hre
  by_contra hRH
  have hpos := re_continuedXiAntiCausalWardResponse_half_pos_of_not_rh hRH
  linarith

/-- Under false RH, no pair of differentiable unit source frames meeting at
zero can have the fixed-node Xi phase as its overlap coefficient. -/
theorem no_differentiable_unitFrame_scalarXiPhase_of_not_rh
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [NormedSpace ℝ F]
    (hRH : ¬ RiemannHypothesis)
    (x y : ℝ → F) (e : F)
    (hx0 : x 0 = e) (hy0 : y 0 = e)
    (hunitx : ∀ a : ℝ, ‖x a‖ ^ 2 = 1)
    (hunity : ∀ a : ℝ, ‖y a‖ ^ 2 = 1)
    (hoverlap : ∀ a : ℝ,
      inner ℂ (x a) (y a) =
        xiRightWardBoundarySourcePhaseCrossRatio
          (I * (1 / 2 : ℂ)) (a : ℂ)) :
    ∀ x' y' : F, ¬ (HasDerivAt x x' 0 ∧ HasDerivAt y y' 0) := by
  intro x' y' hderiv
  exact hRH
    (riemannHypothesis_of_differentiable_unitFrame_scalarXiPhase
      x y x' y' e hderiv.1 hderiv.2 hx0 hy0 hunitx hunity hoverlap)

end

end RHTower
