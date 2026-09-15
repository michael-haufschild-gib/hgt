import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMConnectionSimpleZero
import GaloisForLFunctions.HTGeometry.ReciprocalGammaPoleBranchTaylor

/-! Exact second jet of the original Birmingham--Mokhtari connection at a fundamental zero. -/
open Complex Set Filter Topology
namespace RHTower.D4BMLaplaceRadial
open GaloisForLFunctions
noncomputable section
set_option autoImplicit false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

private theorem Gamma_hasDerivAt_digamma {z : ℂ}
    (hz : ∀ n : ℕ, z ≠ -(n : ℂ)) :
    HasDerivAt Complex.Gamma (Complex.digamma z * Complex.Gamma z) z := by
  have h := (Complex.differentiableAt_Gamma z hz).hasDerivAt
  apply h.congr_deriv
  rw [Complex.digamma_def, logDeriv_apply]
  field_simp [Complex.Gamma_ne_zero hz]

private theorem reciprocalGammaEntire_hasDerivAt_digamma {z : ℂ}
    (hz : ∀ n : ℕ, z ≠ -(n : ℂ)) :
    HasDerivAt reciprocalGammaEntire
      (-Complex.digamma z * reciprocalGammaEntire z) z := by
  unfold reciprocalGammaEntire
  have h : HasDerivAt (fun s : ℂ => (Complex.Gamma s)⁻¹)
      (deriv (fun s : ℂ => (Complex.Gamma s)⁻¹) z) z :=
    Complex.differentiable_one_div_Gamma.differentiableAt.hasDerivAt
  apply h.congr_deriv
  rw [oneDivGamma_deriv_eq z hz, Complex.digamma_def, logDeriv_apply]
  field_simp [Complex.Gamma_ne_zero hz]

theorem connectionOtherArgument_hasDerivAt (w chi : ℂ) (side : Bool) :
    HasDerivAt (fun v => connectionOtherArgument v chi side) (1 / 2 : ℂ) w := by
  have hC : HasDerivAt gaussC 1 w := (hasDerivAt_id w).const_add 1
  have hA : HasDerivAt (fun v => gaussA v chi) (1 / 2 : ℂ) w :=
    (((hasDerivAt_id w).div_const 2).const_add (1 / 4 : ℂ)).add_const (I * chi / 2)
  have hB : HasDerivAt (fun v => gaussB v chi) (1 / 2 : ℂ) w :=
    (((hasDerivAt_id w).div_const 2).const_add (1 / 4 : ℂ)).sub_const (I * chi / 2)
  cases side
  · exact (hC.sub hB).congr_deriv (by ring)
  · exact (hC.sub hA).congr_deriv (by ring)

/-- At a fundamental reciprocal-Gamma zero, the original connection second derivative is its
nonzero first derivative times one explicit digamma combination. No regular Gamma-jet remainder
survives. -/
theorem connection_fundamental_secondDerivative (w chi : ℂ) (side : Bool)
    (hw : w.im ≠ 0) (hz : connectionZeroArgument w chi side = 0) :
    deriv (deriv (fun v => connection v chi)) w =
      connectionSimpleSlope w chi side *
        (2 * Complex.digamma (gaussC w) -
          Complex.digamma (connectionOtherArgument w chi side) -
          Complex.digamma 1) := by
  let Z : ℂ → ℂ := fun v => connectionZeroArgument v chi side
  let O : ℂ → ℂ := fun v => connectionOtherArgument v chi side
  let H : ℂ → ℂ := reciprocalGammaEntire
  let A : ℂ → ℂ := fun v =>
    Complex.Gamma (gaussC v) * Complex.Gamma (1 / 2 : ℂ) * H (O v)
  let B : ℂ → ℂ := fun v => H (Z v)
  have hZw : Z w = 0 := hz
  have hOeq : O w = 3 / 2 + w := by
    have hsum := connection_argument_sum w chi side
    change Z w + O w = 3 / 2 + w at hsum
    rw [hZw, zero_add] at hsum
    exact hsum
  have hcim : (gaussC w).im ≠ 0 := by
    simpa only [gaussC, Complex.add_im, Complex.one_im, zero_add] using hw
  have hOim : (O w).im ≠ 0 := by
    rw [hOeq]
    norm_num [Complex.add_im]
    exact hw
  have hcoff : ∀ n : ℕ, gaussC w ≠ -(n : ℂ) := by
    intro n hn
    apply hcim
    rw [hn]
    simp
  have hOoff : ∀ n : ℕ, O w ≠ -(n : ℂ) := by
    intro n hn
    apply hOim
    rw [hn]
    simp
  have hZ : HasDerivAt Z (1 / 2 : ℂ) w := by
    simpa only [Z] using connectionZeroArgument_hasDerivAt w chi side
  have hO : HasDerivAt O (1 / 2 : ℂ) w := by
    simpa only [O] using connectionOtherArgument_hasDerivAt w chi side
  have hC : HasDerivAt gaussC 1 w := (hasDerivAt_id w).const_add 1
  have hGammaC := (Gamma_hasDerivAt_digamma hcoff).comp w hC
  have hInvO := (reciprocalGammaEntire_hasDerivAt_digamma hOoff).comp w hO
  have hAder :=
    (hGammaC.mul_const (Complex.Gamma (1 / 2 : ℂ))).mul hInvO
  change HasDerivAt A _ w at hAder
  simp only [Function.comp_apply] at hAder
  have hAprime : deriv A w =
      A w * (Complex.digamma (gaussC w) - Complex.digamma (O w) / 2) := by
    rw [hAder.deriv]
    dsimp only [A]
    ring
  have hAanalytic : AnalyticAt ℂ A w := by
    have hGc := (_root_.HTGeometry.analyticAt_Gamma_off_poles hcoff).comp
      (show AnalyticAt ℂ gaussC w by unfold gaussC; fun_prop)
    have hOanalytic : AnalyticAt ℂ O w := by
      dsimp only [O, connectionOtherArgument]
      split <;> dsimp only [gaussA, gaussB, gaussC] <;> fun_prop
    exact (hGc.mul analyticAt_const).mul
      ((Complex.differentiable_one_div_Gamma.analyticAt _).comp hOanalytic)
  have hBanalytic : AnalyticAt ℂ B w := by
    have hZanalytic : AnalyticAt ℂ Z w := by
      dsimp only [Z, connectionZeroArgument]
      split <;> dsimp only [gaussA, gaussB, gaussC] <;> fun_prop
    exact (Complex.differentiable_one_div_Gamma.analyticAt _).comp hZanalytic
  have hBzero : B w = 0 := by
    dsimp only [B, H]
    rw [hZw]
    simp [reciprocalGammaEntire]
  have hBder : HasDerivAt B (1 / 2 : ℂ) w := by
    have hraw : HasDerivAt H 1 0 := by
      dsimp only [H]
      unfold reciprocalGammaEntire
      convert hasDerivAt_oneDivGamma_neg_nat 0 using 1 <;> norm_num
    have hraw' : HasDerivAt H 1 (Z w) := by simpa only [hZw] using hraw
    change HasDerivAt (H ∘ Z) (1 / 2 : ℂ) w
    simpa only [one_mul] using hraw'.comp w hZ
  have hHsecond : deriv (deriv H) 0 = -2 * Complex.digamma 1 := by
    have htwo := iteratedDeriv_two_reciprocalGammaEntire_neg_nat 0
    norm_num at htwo
    have htwo' : deriv (deriv reciprocalGammaEntire) 0 =
        -(2 * Complex.digamma 1) := by
      rw [← show iteratedDeriv 2 reciprocalGammaEntire 0 =
        deriv (deriv reciprocalGammaEntire) 0 by
          rw [show 2 = 0 + 1 + 1 by omega, iteratedDeriv_succ', iteratedDeriv_succ']
          simp]
      exact htwo
    change deriv (deriv reciprocalGammaEntire) 0 = _
    rw [htwo']
    ring
  have hHdd : HasDerivAt (deriv H) (-2 * Complex.digamma 1) 0 := by
    have hHan : AnalyticAt ℂ H 0 := by
      dsimp only [H]
      unfold reciprocalGammaEntire
      exact Complex.differentiable_one_div_Gamma.analyticAt 0
    rw [← hHsecond]
    exact hHan.deriv.differentiableAt.hasDerivAt
  have hBderiv_fun : deriv B = fun v => deriv H (Z v) * (1 / 2 : ℂ) := by
    funext v
    have hZv : HasDerivAt Z (1 / 2 : ℂ) v := by
      simpa only [Z] using connectionZeroArgument_hasDerivAt v chi side
    have hHv : HasDerivAt H (deriv H (Z v)) (Z v) := by
      dsimp only [H, reciprocalGammaEntire]
      exact Complex.differentiable_one_div_Gamma.differentiableAt.hasDerivAt
    exact (hHv.comp v hZv).deriv
  have hBdd : HasDerivAt (deriv B) (-Complex.digamma 1 / 2) w := by
    rw [hBderiv_fun]
    have hHdd' : HasDerivAt (deriv H) (-2 * Complex.digamma 1) (Z w) := by
      simpa only [hZw] using hHdd
    have hcomp := hHdd'.comp w hZ
    have hmul := hcomp.mul_const (1 / 2 : ℂ)
    change HasDerivAt (fun v => deriv H (Z v) * (1 / 2 : ℂ)) _ w
    exact hmul.congr_deriv (by ring)
  have hprod_deriv : deriv (fun v => A v * B v) =ᶠ[𝓝 w]
      fun v => deriv A v * B v + A v * deriv B v := by
    filter_upwards [hAanalytic.eventually_analyticAt,
      hBanalytic.eventually_analyticAt] with v hAv hBv
    exact (hAv.differentiableAt.hasDerivAt.mul
      hBv.differentiableAt.hasDerivAt).deriv
  have hAdd : HasDerivAt (deriv A) (deriv (deriv A) w) w :=
    hAanalytic.deriv.differentiableAt.hasDerivAt
  have hAder' : HasDerivAt A (deriv A w) w :=
    hAanalytic.differentiableAt.hasDerivAt
  have hRhs := (hAdd.mul hBder).add (hAder'.mul hBdd)
  have hProdSecond := hRhs.congr_of_eventuallyEq hprod_deriv
  have hProdValue : deriv (deriv (fun v => A v * B v)) w =
      A w * (Complex.digamma (gaussC w) - Complex.digamma (O w) / 2) -
        A w * Complex.digamma 1 / 2 := by
    rw [hProdSecond.deriv, hBzero, hBder.deriv, hAprime]
    ring
  have hAB : (fun v => connection v chi) = fun v => A v * B v := by
    funext v
    rw [connection_selected_factorization v chi side]
    dsimp only [A, B, H, O, Z, reciprocalGammaEntire]
  have hAvalue : A w = 2 * connectionSimpleSlope w chi side := by
    dsimp only [A, H, O, reciprocalGammaEntire, connectionSimpleSlope]
    rw [div_eq_mul_inv]
    ring
  rw [hAB, hProdValue, hAvalue]
  change _ = _ * (2 * Complex.digamma (gaussC w) -
    Complex.digamma (O w) - Complex.digamma 1)
  ring

end
end RHTower.D4BMLaplaceRadial
