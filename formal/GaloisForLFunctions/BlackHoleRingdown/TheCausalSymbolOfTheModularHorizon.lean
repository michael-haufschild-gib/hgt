import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingTopologicalBlackHoleQNMIncidence
import GaloisForLFunctions.RHTower.LiClockThetaSingleDampingStrip

/-!
# The causal symbol of the modular horizon

On the massless topological black hole with modular horizon, a radial overtone of decay `D` multiplies
the horizon response by `e^{-Dt}`, so its retarded transform in the cusp channel evaluates the
scattering coefficient `φ` at `s = D + 1/2 - iω`. This module studies that composite symbol in the
frequency plane.

At a Xi divisor `z` the two continued QNM branches `ω_± = ±ξ - iD`, `ξ = z/2 + i/4`, behave oppositely.
The branch `ω_-` lands on `z` and is a pole. The branch `ω_+` lands on the functional-equation shadow
and is a regular zero. So the symbol selects `ω_-`, and its damping rate at `ρ = β + iγ` is
`D + (1-β)/2`, with oscillation `γ/2`.

Damping is universal, equal to `D + 1/4` at every zero, exactly when RH holds; this is a restatement of
RH, not a route to it. The residue of the scattering coefficient at a simple zero is the excitation
factor of the mode.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open RHTower

/-- The resonance coordinate `z` of the point `s = D + 1/2 - iω`. -/
def causalCoordinate (D : ℝ) (ω : ℂ) : ℂ := -2 * ω - 2 * I * D - I / 2

theorem resonanceParameter_causalCoordinate (D : ℝ) (ω : ℂ) :
    thetaCuspHawkingOpticalCuspResonanceParameter (causalCoordinate D ω) = D + 1 / 2 - I * ω := by
  unfold thetaCuspHawkingOpticalCuspResonanceParameter causalCoordinate
  linear_combination (-(D : ℂ) - 1 / 4) * I_sq

/-- The minus branch lands on the divisor coordinate. -/
theorem causalCoordinate_qnmMinus (n : ℕ) (z : ℂ) :
    causalCoordinate (thetaCuspHawkingTopologicalBlackHoleConformalDecay n)
        (thetaCuspHawkingTopologicalBlackHoleQNMMinus n z) = z := by
  unfold causalCoordinate thetaCuspHawkingTopologicalBlackHoleQNMMinus
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum
  ring

/-- The plus branch lands on the functional-equation shadow. -/
theorem causalCoordinate_qnmPlus (n : ℕ) (z : ℂ) :
    causalCoordinate (thetaCuspHawkingTopologicalBlackHoleConformalDecay n)
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus n z) =
      thetaCuspHawkingOpticalCuspShadow z := by
  unfold causalCoordinate thetaCuspHawkingTopologicalBlackHoleQNMPlus
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum thetaCuspHawkingOpticalCuspShadow
  ring

/-- The scattering coefficient as a function of frequency, at radial decay `D`. -/
def causalSymbol (D : ℝ) (ω : ℂ) : ℂ :=
  thetaCuspHawkingOpticalCuspScattering (causalCoordinate D ω)

theorem differentiable_causalCoordinate (D : ℝ) : Differentiable ℂ (causalCoordinate D) := by
  unfold causalCoordinate
  fun_prop

/-- **The excited branch.**  Every Xi divisor makes the minus branch a pole of the causal symbol. -/
theorem causalSymbol_qnmMinus_isPole (n : ℕ) (q : XiZeroCopy) :
    meromorphicOrderAt (causalSymbol (thetaCuspHawkingTopologicalBlackHoleConformalDecay n))
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q)) < 0 := by
  set D := thetaCuspHawkingTopologicalBlackHoleConformalDecay n with hD
  set w := thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q) with hw
  have hcoord : causalCoordinate D w = xiSpectralPoint q := causalCoordinate_qnmMinus n _
  have hcd := differentiable_causalCoordinate D
  have hnumD : Differentiable ℂ
      (fun ω => thetaCuspHawkingOpticalCuspNumerator (causalCoordinate D ω)) := by
    unfold thetaCuspHawkingOpticalCuspNumerator
    exact XiC_differentiable.comp (hcd.add_const _)
  have hdenD : Differentiable ℂ
      (fun ω => thetaCuspHawkingOpticalCuspDenominator (causalCoordinate D ω)) := by
    unfold thetaCuspHawkingOpticalCuspDenominator
    exact XiC_differentiable.comp hcd
  have hfun : causalSymbol D =
      (fun ω => thetaCuspHawkingOpticalCuspNumerator (causalCoordinate D ω)) /
        (fun ω => thetaCuspHawkingOpticalCuspDenominator (causalCoordinate D ω)) := by
    funext ω
    rfl
  rw [hfun]
  refine meromorphicOrderAt_div_neg_of_analyticAt_num_ne_den_zero (hnumD.analyticAt w)
    (hdenD.analyticAt w) ?_ ?_ ?_
  · simp only
    rw [hcoord]
    exact thetaCuspHawkingOpticalCuspNumerator_xiSpectralPoint_ne_zero q
  · simp only
    rw [hcoord]
    exact thetaCuspHawkingOpticalCuspDenominator_xiSpectralPoint_eq_zero q
  · intro htop
    have hevent := analyticOrderAt_eq_top.mp htop
    have hglobal : AnalyticOnNhd ℂ
        (fun ω => thetaCuspHawkingOpticalCuspDenominator (causalCoordinate D ω)) Set.univ :=
      fun z _ => hdenD.analyticAt z
    have hzero := hglobal.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ w) hevent
    have hshift : causalCoordinate D (w - I / 2) = xiSpectralPoint q + I := by
      rw [← hcoord]
      unfold causalCoordinate
      ring
    have h0 := hzero (Set.mem_univ (w - I / 2))
    simp only [Pi.zero_apply] at h0
    rw [hshift] at h0
    exact thetaCuspHawkingOpticalCuspNumerator_xiSpectralPoint_ne_zero q h0

/-- **The silent branch.**  At every Xi divisor the plus branch is a regular zero of the causal
symbol. -/
theorem causalSymbol_qnmPlus_isZero (n : ℕ) (q : XiZeroCopy) :
    AnalyticAt ℂ (causalSymbol (thetaCuspHawkingTopologicalBlackHoleConformalDecay n))
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)) ∧
      causalSymbol (thetaCuspHawkingTopologicalBlackHoleConformalDecay n)
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)) = 0 := by
  obtain ⟨han, hzero⟩ := thetaCuspHawkingOpticalCuspShadow_xiSpectralPoint_isZero q
  have hcoord := causalCoordinate_qnmPlus n (xiSpectralPoint q)
  constructor
  · rw [← hcoord] at han
    exact han.comp ((differentiable_causalCoordinate _).analyticAt _)
  · rw [causalSymbol, hcoord]
    exact hzero

/-! ### The ringdown rate -/

/-- The damping rate of the minus branch at radial decay `D` and divisor coordinate `z`. -/
def ringdownRate (D : ℝ) (z : ℂ) : ℝ := D + 1 / 4 + z.im / 2

theorem qnmMinus_im_eq_neg_ringdownRate (n : ℕ) (z : ℂ) :
    (thetaCuspHawkingTopologicalBlackHoleQNMMinus n z).im =
      -ringdownRate (thetaCuspHawkingTopologicalBlackHoleConformalDecay n) z := by
  rw [thetaCuspHawkingTopologicalBlackHoleQNMMinus_im, ringdownRate]
  ring

/-- **The rate at a zero.**  A zero `ρ = β + iγ` rings with damping `D + (1-β)/2`. -/
theorem ringdownRate_xiSpectralPoint (D : ℝ) (q : XiZeroCopy) :
    ringdownRate D (xiSpectralPoint q) = D + (1 - (q.1 : ℂ).re) / 2 := by
  have him : (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
    simp [xiSpectralPoint, Complex.mul_im]
  rw [ringdownRate, him]
  ring

/-- **The frequency at a zero.**  A zero `ρ = β + iγ` rings at frequency `-γ/2`; its conjugate zero
gives `+γ/2` at the same damping. -/
theorem qnmMinus_re_xiSpectralPoint (n : ℕ) (q : XiZeroCopy) :
    (thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q)).re =
      -(q.1 : ℂ).im / 2 := by
  have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by
    simp [xiSpectralPoint, Complex.mul_re]
  simp [thetaCuspHawkingTopologicalBlackHoleQNMMinus,
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum, hre]
  ring

/-- **Universal damping is RH.**  This restates RH; it is not an input towards it. -/
theorem riemannHypothesis_iff_universal_damping (D : ℝ) :
    RiemannHypothesis ↔ ∀ q : XiZeroCopy, ringdownRate D (xiSpectralPoint q) = D + 1 / 4 := by
  rw [riemannHypothesis_iff_forall_xiSpectralPoint_im_eq_zero]
  refine forall_congr' fun q => ?_
  rw [ringdownRate]
  constructor <;> intro h <;> linarith

/-! ### The excitation factor -/

/-- **The excitation factor.**  At a simple zero of `XiC` the scattering coefficient has residue
`XiC (z₀ + i) / XiC' z₀`. -/
theorem tendsto_sub_mul_opticalCuspScattering {z₀ : ℂ} (h0 : XiC z₀ = 0) (hd : deriv XiC z₀ ≠ 0) :
    Tendsto (fun z => (z - z₀) * thetaCuspHawkingOpticalCuspScattering z) (𝓝[≠] z₀)
      (𝓝 (XiC (z₀ + I) / deriv XiC z₀)) := by
  have hder : HasDerivAt XiC (deriv XiC z₀) z₀ := XiC_differentiable.differentiableAt.hasDerivAt
  have hslope := hasDerivAt_iff_tendsto_slope.mp hder
  have hinv := hslope.inv₀ hd
  have hnum : Tendsto (fun z => XiC (z + I)) (𝓝[≠] z₀) (𝓝 (XiC (z₀ + I))) := by
    have hc : Continuous (fun z => XiC (z + I)) :=
      XiC_differentiable.continuous.comp (continuous_id.add continuous_const)
    exact (hc.tendsto z₀).mono_left nhdsWithin_le_nhds
  have hmul := hnum.mul hinv
  rw [← div_eq_mul_inv] at hmul
  refine hmul.congr fun z => ?_
  rw [slope_def_field, h0, sub_zero, thetaCuspHawkingOpticalCuspScattering,
    thetaCuspHawkingOpticalCuspNumerator, thetaCuspHawkingOpticalCuspDenominator]
  rw [inv_div]
  ring

/-- The excitation factor is nonzero at every simple Xi divisor. -/
theorem excitationFactor_ne_zero (q : XiZeroCopy) (hd : deriv XiC (xiSpectralPoint q) ≠ 0) :
    XiC (xiSpectralPoint q + I) / deriv XiC (xiSpectralPoint q) ≠ 0 :=
  div_ne_zero (thetaCuspHawkingOpticalCuspNumerator_xiSpectralPoint_ne_zero q) hd

end GaloisForLFunctions.BlackHoleRingdown

end
