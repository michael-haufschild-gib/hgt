import GaloisForLFunctions.HyperbolicArakelovTheory.TheFinitePartOfTheCoupledAdelicOrbit
import GaloisForLFunctions.HyperbolicArakelovTheory.TheWeilPacketsFromRenormalizedGeometricDiagonals
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadCoherentQuantileGammaNoGo
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteWeilSourceTransfer

/-!
# The coupled orbit density matches the archimedean constants and tower packet functional

This file establishes the exact scalar and continuum bridges between the three objects appearing
in the glued-carrier question:

1. **Exact archimedean constant decomposition (`four_mul_regularMean_eq`,
   `gammaHardyPhaseRate_zero_eq_regularMean_add_robin`).** The regular remainder mean
   `CoupledOrbit.regularMean = log 2 / 4 + π / 8` of the coupled rational torus orbit, the
   modular cusp counterterm `(ScatteringTower.robinCounterterm (1 / 2)).re = -log(4π) / 2`
   (with `(robinCounterterm 2).re = -log π / 2`), and the harmonic Euler–Mascheroni constant `γ`
   sum to Weil's central archimedean digamma scalar `gammaHardyPhaseRate 0`:
   `gammaHardyPhaseRate 0 = -2 * regularMean + (robinCounterterm (1 / 2)).re - γ / 2`,
   equivalently `4 * regularMean = -2 * gammaHardyPhaseRate 0 - (log(4π) + γ)`.
   Thus the obstruction to gluing on the adelic carrier is not an archimedean scalar mismatch at
   degree `1`, but a degree-dependent diagonal variation across `n ≥ 1`.
2. **Real packet limit and exact log-scale shift invariance of the scattering tower
   (`geometricWeilEnergy_shift`, `tendsto_geometricWeilEnergy_re_weilQuad`,
   `tendsto_geometricWeilEnergy_shift_re_weilQuad`).** On every real `C_c²` profile `F : ℝ → ℝ`,
   the Robin-normalized geometric scattering tower `(geometricWeilEnergy (fun u => (F u : ℂ)) N).re`
   converges as `N → ∞` to `weilQuad F`, and is strictly invariant under all log-scale shifts
   `u ↦ u - c`.
-/

set_option autoImplicit false
noncomputable section

open Complex Filter Topology MeasureTheory
open scoped ComplexConjugate

namespace GaloisForLFunctions.HyperbolicArakelovTheory.ArchimedeanConstantBridge

open CoupledOrbit ScatteringTower SpacingScaleHarmonicAnalysis

/-! ## 1. Exact decomposition of `gammaHardyPhaseRate 0` into `regularMean`, `robinCounterterm`, and `γ` -/

private theorem log_four_mul_pi :
    Real.log (4 * Real.pi) = 2 * Real.log 2 + Real.log Real.pi := by
  have h4 : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
  rw [h4, Real.log_mul (by norm_num) Real.pi_pos.ne', Real.log_pow]
  push_cast
  ring

/-- The cusp Robin counterterm at `x = 2` has real part `-log π / 2`. -/
theorem robinCounterterm_two_re :
    (robinCounterterm 2).re = -Real.log Real.pi / 2 := by
  rw [robinCounterterm_eq (by norm_num : (0 : ℝ) < 2)]
  simp only [Complex.ofReal_re, div_self (by norm_num : (2 : ℝ) ≠ 0), Real.log_one, zero_div,
    zero_sub]
  ring

/-- The cusp Robin counterterm at the critical parameter `x = 1 / 2` has real part
`-log(4π) / 2`. -/
theorem robinCounterterm_half_re :
    (robinCounterterm (1 / 2)).re = -Real.log (4 * Real.pi) / 2 := by
  rw [robinCounterterm_eq (by norm_num : (0 : ℝ) < 1 / 2)]
  simp only [Complex.ofReal_re]
  have hdiv : (1 / 2 : ℝ) / 2 = ((2 : ℝ) ^ 2)⁻¹ := by norm_num
  rw [hdiv, Real.log_inv, Real.log_pow, log_four_mul_pi]
  push_cast
  ring

/-- Four times the smooth torus-orbit density `regularMean` equals `-2 * gammaHardyPhaseRate 0`
minus `log(4π) + γ`. -/
theorem four_mul_regularMean_eq :
    4 * regularMean =
      -2 * _root_.RHTower.gammaHardyPhaseRate 0 -
        (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant) := by
  rw [regularMean_eq, _root_.RHTower.gammaHardyPhaseRate_zero_closed, log_four_mul_pi]
  ring

/-- Exact three-part archimedean identity linking Weil's central digamma constant, the smooth
coupled-orbit remainder mean, the critical Robin counterterm, and Euler's constant `γ`. -/
theorem gammaHardyPhaseRate_zero_eq_regularMean_add_robin :
    _root_.RHTower.gammaHardyPhaseRate 0 =
      -2 * regularMean + (robinCounterterm (1 / 2)).re -
        Real.eulerMascheroniConstant / 2 := by
  rw [regularMean_eq, robinCounterterm_half_re,
    _root_.RHTower.gammaHardyPhaseRate_zero_closed, log_four_mul_pi]
  ring

/-- Equivalent form for the locking parameter `2 * gammaHardyPhaseRate 0`. -/
theorem two_mul_gammaHardyPhaseRate_zero_eq :
    2 * _root_.RHTower.gammaHardyPhaseRate 0 =
      -4 * regularMean - (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant) := by
  linarith [four_mul_regularMean_eq]

/-! ## 2. Translation invariance and `weilQuad` convergence of the scattering tower -/

/-- Simultaneous translation `u ↦ u - c` leaves the Weil autocorrelation `EF.weilTest` unchanged. -/
theorem weilTest_shift_same (f g : ℝ → ℂ) (c : ℝ) :
    Zeta23.EF.weilTest (fun u => f (u - c)) (fun u => g (u - c)) =
      Zeta23.EF.weilTest f g := by
  funext x
  unfold Zeta23.EF.weilTest
  rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
  simp only [ContinuousLinearMap.mul_apply', Zeta23.EF.tilde, neg_sub]
  have heq : (fun u : ℝ => f (u - c) * conj (g (u - x - c))) =
      fun u : ℝ => f (u - c) * conj (g ((u - c) - x)) := by
    funext u
    congr 3
    ring
  rw [heq]
  exact MeasureTheory.integral_sub_right_eq_self
    (fun v : ℝ => f v * conj (g (v - x))) c

/-- The finite Robin-normalized geometric tower energy `geometricWeilEnergy` is strictly invariant
under log-scale shifts `u ↦ u - c` for every truncation `N`. -/
theorem geometricWeilEnergy_shift (f : ℝ → ℂ) (c : ℝ) (N : ℕ) :
    geometricWeilEnergy (fun u => f (u - c)) N = geometricWeilEnergy f N := by
  unfold geometricWeilEnergy
  rw [weilTest_shift_same]

/-- On every real `C_c²` profile `F : ℝ → ℝ`, the real part of the Robin-normalized scattering-tower
energy converges as `N → ∞` to `weilQuad F`. -/
theorem tendsto_geometricWeilEnergy_re_weilQuad {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) :
    Tendsto (fun N : ℕ => (geometricWeilEnergy (fun u => (F u : ℂ)) N).re) atTop
      (𝓝 (weilQuad F)) := by
  have hcF : ContDiff ℝ 2 (fun u => (F u : ℂ)) := Complex.ofRealCLM.contDiff.comp hF
  have hcFc : HasCompactSupport (fun u => (F u : ℂ)) := hFc.comp_left Complex.ofReal_zero
  have ht := (Complex.continuous_re.tendsto _).comp (tendsto_geometricWeilEnergy hcF hcFc)
  have hlim : (_root_.RHTower.weilFullFunctional
      (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (Zeta23.EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)))).re = weilQuad F := by
    rw [ArithmeticCastelnuovoSeveri.LogCells.weilQuad_eq_zetaW hF hFc]
    exact congrArg Complex.re (_root_.RHTower.zeta_W_eq_weilFullFunctional hcF hcFc).symm
  simpa only [Function.comp_def, hlim] using ht

/-- Shifted profiles `u ↦ F(u - c)` have the exact same `N → ∞` scattering-tower limit `weilQuad F`,
independent of the log-scale center `c`. -/
theorem tendsto_geometricWeilEnergy_shift_re_weilQuad {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (c : ℝ) :
    Tendsto (fun N : ℕ => (geometricWeilEnergy (fun u => (F (u - c) : ℂ)) N).re) atTop
      (𝓝 (weilQuad F)) :=
  (tendsto_geometricWeilEnergy_re_weilQuad hF hFc).congr fun N =>
    congrArg Complex.re (geometricWeilEnergy_shift (fun v => (F v : ℂ)) c N).symm

#print axioms four_mul_regularMean_eq
#print axioms gammaHardyPhaseRate_zero_eq_regularMean_add_robin
#print axioms geometricWeilEnergy_shift
#print axioms tendsto_geometricWeilEnergy_re_weilQuad
#print axioms tendsto_geometricWeilEnergy_shift_re_weilQuad

end GaloisForLFunctions.HyperbolicArakelovTheory.ArchimedeanConstantBridge
