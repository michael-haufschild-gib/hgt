import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspGammaSourceAction
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspPolarSourceAction
import GaloisForLFunctions.RHTower.XiExplicitFormulaLogDeriv
import GaloisForLFunctions.RHTower.ReflectionCocycleArchimedean
import GaloisForLFunctions.RHTower.XiShiftLoewnerEulerSplit
import Mathlib.Analysis.Fourier.Inversion

/-!
# The exact prime–Gamma–pole equation for the complete theta source

The completed-Xi logarithmic derivative, absolute Laplace exchanges, and
weighted Fourier uniqueness prove the literal physical source equation.
This is source annihilation; it supplies no signed-energy positivity theorem.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped FourierTransform
noncomputable section
namespace RHTower.ThetaSourceWard

def archSymbol (w : ℂ) : ℂ :=
  (1/2+w)⁻¹ + (1/2+w-1)⁻¹ +
    Complex.digamma ((1/2+w)/2)/2 - (Real.log Real.pi : ℂ)/2

def primeSymbol (w : ℂ) : ℂ :=
  LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1/2+w)

lemma source_symbol_identity {w : ℂ} (hw : 1/2 < w.re) :
    bilateralLaplaceDeriv thetaCuspTiltSource w =
      (archSymbol w - primeSymbol w) * bilateralLaplace thetaCuspTiltSource w := by
  have hs : 1 < (1/2+w).re := by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
    linarith
  have hsp : 0 < (1/2+w).re := lt_trans zero_lt_one hs
  have hn : xiCent w ≠ 0 := xi_ne_zero_of_one_le_re hs.le
  have hz : logDeriv riemannZeta (1/2+w) = -primeSymbol w := by
    rw [primeSymbol, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
      logDeriv_apply]
    ring
  have h : logDeriv xiCent w = archSymbol w - primeSymbol w := by
    rw [logDeriv_xiCent, logDeriv_xi_split hs, logDeriv_Gammaℝ_of_re_pos hsp, hz]
    unfold archSymbol
    ring
  rw [logDeriv_apply] at h
  have hd := (div_eq_iff hn).mp h
  have hf : bilateralLaplace thetaCuspTiltSource = xiCent :=
    funext bilateralLaplace_thetaCuspTiltSource_eq_xiCent
  rw [← deriv_bilateralLaplace, hf]
  exact hd

lemma arch_symbol_gauss_integral {w : ℂ} (hw : -1/2 < w.re) :
    archSymbol w = (1/2+w)⁻¹ + (1/2+w-1)⁻¹ -
      ((Real.eulerMascheroniConstant + Real.log Real.pi : ℝ) : ℂ)/2 +
      (∫ t in Ioi (0 : ℝ), gaussLaplaceKernel ((1/2+w)/2) t)/2 := by
  have hs : 0 < ((1/2+w)/2).re := by
    simp only [Complex.div_ofNat_re, Complex.add_re, Complex.one_re]
    linarith
  rw [archSymbol, integral_gaussLaplaceKernel_eq_tsum hs,
    digamma_eq_neg_euler_add_tsum_gauss hs]
  push_cast
  ring

def archConstant : ℂ := ((Real.eulerMascheroniConstant+Real.log Real.pi:ℝ):ℂ)/2

def sourceResidual (x : ℝ) : ℂ :=
  -archConstant*(thetaCuspFullSource x:ℂ) + gammaSource x +
    polarSource (1/2) x + polarSource (-1/2) x -
    fullPrimeSource thetaCuspTiltSource x - (x:ℂ)*(thetaCuspFullSource x:ℂ)

lemma momentIntegrand_integrable (w : ℂ) :
    Integrable (fun x : ℝ => (x:ℂ)*(thetaCuspFullSource x:ℂ)*Complex.exp (w*x)) := by
  simpa only [pow_one,thetaCuspTiltSource_k] using
    ThetaSource.integrable_mul_exp thetaCuspTiltSource w 1

lemma sourceResidual_continuous : Continuous sourceResidual := by
  have hc := contDiff_thetaCuspFullSource.continuous
  have hg := gammaSource_continuous
  have hp := polarSource_continuous (a := 1/2) (by norm_num)
  have hm := polarSource_continuous (a := -1/2) (by norm_num)
  have hn := fullPrimeSource_continuous thetaCuspTiltSource
  unfold sourceResidual
  fun_prop

lemma sourceResidual_laplace_integrable {w : ℂ}
    (hw : 1/2 < w.re) (hw1 : |w.re| < 1) :
    Integrable (fun x : ℝ => sourceResidual x*Complex.exp (w*x)) := by
  have ha := (integrable_laplaceIntegrand thetaCuspTiltSource w).const_mul (-archConstant)
  have hg := gammaSource_laplace_integrable (w := w) (by linarith) hw1
  have hp := polarSource_laplace_integrable (1/2) hw
  have hm := polarSource_laplace_integrable (-1/2) (w := w) (by linarith)
  have hn := fullPrimeSource_laplace_integrable thetaCuspTiltSource hw
  have hd := momentIntegrand_integrable w
  apply (((((ha.fun_add hg).fun_add hp).fun_add hm).sub hn).sub hd).congr
  filter_upwards with x
  dsimp [sourceResidual,laplaceIntegrand,thetaCuspTiltSource]
  ring

lemma sourceResidual_laplace_zero {w : ℂ}
    (hw : 1/2 < w.re) (hw1 : |w.re| < 1) :
    (∫ x : ℝ, sourceResidual x*Complex.exp (w*x)) = 0 := by
  let A := fun x : ℝ => -archConstant*laplaceIntegrand thetaCuspTiltSource w x
  let G := fun x : ℝ => gammaSource x*Complex.exp (w*x)
  let P := fun x : ℝ => polarSource (1/2) x*Complex.exp (w*x)
  let M := fun x : ℝ => polarSource (-1/2) x*Complex.exp (w*x)
  let N := fun x : ℝ => fullPrimeSource thetaCuspTiltSource x*Complex.exp (w*x)
  let D := fun x : ℝ => (x:ℂ)*(thetaCuspFullSource x:ℂ)*Complex.exp (w*x)
  have ha : Integrable A := (integrable_laplaceIntegrand thetaCuspTiltSource w).const_mul _
  have hg : Integrable G := gammaSource_laplace_integrable (by linarith) hw1
  have hp : Integrable P := polarSource_laplace_integrable (1/2) hw
  have hm : Integrable M := polarSource_laplace_integrable (-1/2) (by linarith)
  have hn : Integrable N := fullPrimeSource_laplace_integrable thetaCuspTiltSource hw
  have hd : Integrable D := momentIntegrand_integrable w
  have heq : (fun x : ℝ => sourceResidual x*Complex.exp (w*x)) =
      fun x : ℝ => A x+G x+P x+M x-N x-D x := by
    funext x
    dsimp [sourceResidual,A,G,P,M,N,D,laplaceIntegrand,thetaCuspTiltSource]
    ring
  have hsum : Integrable (fun x : ℝ => A x+G x+P x+M x) :=
    ((ha.fun_add hg).fun_add hp).fun_add hm
  have hsub : Integrable (fun x : ℝ => A x+G x+P x+M x-N x) := hsum.sub hn
  rw [heq,integral_sub hsub hd,
    integral_sub hsum hn,
    integral_add ((ha.fun_add hg).fun_add hp) hm,
    integral_add (ha.fun_add hg) hp,integral_add ha hg]
  dsimp [A,G,P,M,N,D]
  rw [integral_const_mul,integral_gammaSource_laplace (by linarith) hw1,
    integral_polarSource_laplace _ hw,
    integral_polarSource_laplace _ (show (-1/2:ℝ)<w.re by linarith)]
  change -archConstant*bilateralLaplace thetaCuspTiltSource w +
    ((∫ t in Ioi (0:ℝ), gaussLaplaceKernel ((1/2+w)/2) t)/2)*bilateralLaplace thetaCuspTiltSource w +
    (w-((1/2:ℝ):ℂ))⁻¹*bilateralLaplace thetaCuspTiltSource w +
    (w-((-1/2:ℝ):ℂ))⁻¹*bilateralLaplace thetaCuspTiltSource w -
    (∫ x : ℝ, (∑' n : ℕ, primeSourceTerm thetaCuspTiltSource n x)*Complex.exp (w*x)) -
    bilateralLaplaceDeriv thetaCuspTiltSource w = 0
  rw [integral_full_prime_source_laplace thetaCuspTiltSource hw,
    source_symbol_identity hw,arch_symbol_gauss_integral (by linarith)]
  have hp : w-((1/2:ℝ):ℂ) = 1/2+w-1 := by push_cast; ring
  have hm : w-((-1/2:ℝ):ℂ) = 1/2+w := by push_cast; ring
  rw [hp,hm]
  unfold archConstant primeSymbol
  ring

lemma sourceResidual_eq_zero (x : ℝ) : sourceResidual x = 0 := by
  let f := fun y : ℝ => sourceResidual y*Complex.exp ((3/4:ℂ)*y)
  have hc : Continuous f := sourceResidual_continuous.mul (by fun_prop)
  have hi : Integrable f := sourceResidual_laplace_integrable (by norm_num) (by norm_num)
  have hz : 𝓕 f = 0 := by
    funext t
    let w : ℂ := (3/4:ℂ)+((-2*Real.pi*t:ℝ):ℂ)*Complex.I
    have hw : 1/2 < w.re := by dsimp [w]; norm_num
    have hw1 : |w.re| < 1 := by dsimp [w]; norm_num
    have hf : 𝓕 f t = ∫ y : ℝ, sourceResidual y*Complex.exp (w*y) := by
      rw [Real.fourier_real_eq_integral_exp_smul]
      apply integral_congr_ae
      filter_upwards with y
      dsimp [f]
      calc
        _ = sourceResidual y*(Complex.exp (↑(-2*Real.pi*t*y)*Complex.I)*
          Complex.exp ((3/4:ℂ)*y)) := by ring
        _ = _ := by
          rw [← Complex.exp_add]
          congr 2
          dsimp [w]
          push_cast
          ring
    exact hf.trans (sourceResidual_laplace_zero hw hw1)
  have hfi : Integrable (𝓕 f) := by rw [hz]; exact integrable_zero _ _ _
  have hinv := hc.fourierInv_fourier_eq hi hfi
  have hx : f x = 0 := by
    rw [hz] at hinv
    exact (congrFun hinv.symm x).trans (by simp [Real.fourierInv_eq])
  exact (mul_eq_zero.mp hx).resolve_right (Complex.exp_ne_zero _)

/-- The exact one-sided complete-theta source equation. -/
theorem complete_theta_source_equation (x : ℝ) :
    -archConstant*(thetaCuspFullSource x:ℂ) + gammaSource x +
      polarSource (1/2) x + polarSource (-1/2) x -
      fullPrimeSource thetaCuspTiltSource x = (x:ℂ)*(thetaCuspFullSource x:ℂ) :=
  sub_eq_zero.mp (sourceResidual_eq_zero x)

lemma primeCoefficient_eq (n : ℕ) : primeCoefficient n =
    ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ):ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [primeCoefficient]
  have hnR : 0 < (n:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hs : (Real.sqrt (n:ℝ):ℂ) = Complex.exp ((Real.log n:ℂ)/2) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hnR,Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [primeCoefficient,Complex.ofReal_div,hs]
  simp only [div_eq_mul_inv,← Complex.exp_neg]
  congr 2
  ring

lemma fullPrimeSource_eq (x : ℝ) : fullPrimeSource thetaCuspTiltSource x =
    ∑' n : ℕ, (((ArithmeticFunction.vonMangoldt n / Real.sqrt n)*
      thetaCuspFullSource (x+Real.log n):ℝ):ℂ) := by
  apply tsum_congr
  intro n
  rw [primeSourceTerm,primeCoefficient_eq,thetaCuspTiltSource_k,Complex.ofReal_mul]

/-- Frozen S1, with literal Gamma, pole, and infinite prime terms. -/
theorem literal_complete_theta_source_equation (x : ℝ) :
    -(((Real.eulerMascheroniConstant+Real.log Real.pi:ℝ):ℂ)/2)*(thetaCuspFullSource x:ℂ) +
      (∫ u in Ioi (0:ℝ),
        (((Real.exp (-2*u)*thetaCuspFullSource x-
          Real.exp (-u/2)*thetaCuspFullSource (x+u))/(1-Real.exp (-2*u)):ℝ):ℂ)) +
      (∫ u in Ioi (0:ℝ), ((2*Real.cosh (u/2)*thetaCuspFullSource (x+u):ℝ):ℂ)) -
      (∑' n : ℕ, (((ArithmeticFunction.vonMangoldt n / Real.sqrt n)*
        thetaCuspFullSource (x+Real.log n):ℝ):ℂ)) =
      (x:ℂ)*(thetaCuspFullSource x:ℂ) := by
  have h := complete_theta_source_equation x
  rw [fullPrimeSource_eq,add_assoc (_+_) _ _,polarSource_half_add] at h
  exact h

end RHTower.ThetaSourceWard
