import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolWardResolvedGeneratorGraph
import GaloisForLFunctions.RHTower.DeningerPrimeGammaReflectedDiagonal

/-!
# Route P primitive Burnol / Deninger squared-Cauchy graph incidence

The primitive Burnol mode admits a canonical quarter-turn into Deninger's strict absolute-Euler
source sector.  Its conjugate upper point evaluates every strict-right Xi zero by the ordinary
Cauchy resolvent of the sum of the target and primitive centered modes.  Squaring that source
evaluation, with its forced minus sign, is exactly the P-G199 generator Laplace reporter of the
coefficient-weighted primitive Burnol window.
-/

open Complex Set MeasureTheory

namespace RHTower

noncomputable section

/-- Centered complex rate of a primitive Euler/Burnol cell. -/
def routePPrimitiveBurnolCenteredMode
    (pe : Nat.Primes × ℕ) (kappa : ℝ) : ℂ :=
  (xiGammaEulerPrimitiveLogFrequency pe : ℂ) + I * (kappa : ℂ)

theorem routePPrimitiveBurnolCenteredMode_re
    (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    (routePPrimitiveBurnolCenteredMode pe kappa).re =
      xiGammaEulerPrimitiveLogFrequency pe := by
  simp [routePPrimitiveBurnolCenteredMode]

theorem half_lt_xiGammaEulerPrimitiveLogFrequency
    (pe : Nat.Primes × ℕ) :
    (1 / 2 : ℝ) < xiGammaEulerPrimitiveLogFrequency pe := by
  have hval : 2 ≤ xiGammaEulerValuationNat pe := by
    rw [xiGammaEulerValuationNat]
    exact pe.1.property.two_le.trans (Nat.le_pow (by omega))
  have hlog : Real.log 2 ≤
      Real.log (xiGammaEulerValuationNat pe : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hval)
  rw [xiGammaEulerPrimitiveLogFrequency]
  exact (lt_trans (by norm_num) Real.log_two_gt_d9).trans_le hlog

/-- Primitive node quarter-turned into Deninger's lower absolute-Euler sector.  The ordinate is
reversed so that its canonical upper mate reports the original Burnol mode. -/
def routePPrimitiveDeningerLowerPoint
    (pe : Nat.Primes × ℕ) (kappa : ℝ) : DeningerPrimeGammaLowerPoint :=
  ⟨routePPrimitiveBurnolCenteredMode pe (-kappa) * (-I), by
    have hfreq := half_lt_xiGammaEulerPrimitiveLogFrequency pe
    rw [show (1 / 2 +
        routePPrimitiveBurnolCenteredMode pe (-kappa) * (-I) * I).re =
        1 / 2 + xiGammaEulerPrimitiveLogFrequency pe by
      simp [routePPrimitiveBurnolCenteredMode, Complex.mul_re]]
    linarith⟩

/-- Canonical reflected upper Deninger point associated to a primitive Burnol mode. -/
def routePPrimitiveDeningerUpperPoint
    (pe : Nat.Primes × ℕ) (kappa : ℝ) : DeningerPrimeGammaUpperPoint :=
  deningerPrimeGammaPointConjEquiv
    (routePPrimitiveDeningerLowerPoint pe kappa)

theorem routePPrimitiveDeningerUpperPoint_coe
    (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    (routePPrimitiveDeningerUpperPoint pe kappa : ℂ) =
      routePPrimitiveBurnolCenteredMode pe kappa * I := by
  apply Complex.ext
  · simp [routePPrimitiveDeningerUpperPoint, deningerPrimeGammaPointConjEquiv,
      routePPrimitiveDeningerLowerPoint, routePPrimitiveBurnolCenteredMode,
      Complex.mul_re]
  · simp [routePPrimitiveDeningerUpperPoint, deningerPrimeGammaPointConjEquiv,
      routePPrimitiveDeningerLowerPoint, routePPrimitiveBurnolCenteredMode,
      Complex.mul_im]

/-- Deninger's upper source Cauchy evaluation is the rotated Hardy resolvent joining the actual
strict-right zero mode to the primitive Burnol mode. -/
theorem xiWeilCauchyTest_routePPrimitiveDeningerUpperPoint
    (pe : Nat.Primes × ℕ) (kappa : ℝ) (q : XiRightZeroCopy) :
    xiWeilCauchyTest (routePPrimitiveDeningerUpperPoint pe kappa : ℂ)
        (xiSpectralPoint q.1) =
      I * (xiRightCenteredZero q +
        routePPrimitiveBurnolCenteredMode pe kappa)⁻¹ := by
  have hspectral : xiSpectralPoint q.1 = -I * xiRightCenteredZero q := by
    rw [xiRightCenteredZero]
    ring_nf
    norm_num [I_mul_I]
  have hsum : xiRightCenteredZero q +
      routePPrimitiveBurnolCenteredMode pe kappa ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp only [Complex.add_re, routePPrimitiveBurnolCenteredMode_re,
      Complex.zero_re] at hre
    have hq := xiRightCenteredZero_re_pos q
    have hp := xiGammaEulerPrimitiveLogFrequency_pos pe
    linarith
  rw [xiWeilCauchyTest, hspectral,
    routePPrimitiveDeningerUpperPoint_coe]
  rw [show -I * xiRightCenteredZero q -
      routePPrimitiveBurnolCenteredMode pe kappa * I =
      -I * (xiRightCenteredZero q +
        routePPrimitiveBurnolCenteredMode pe kappa) by ring]
  rw [mul_inv]
  simp only [inv_neg, Complex.inv_I]
  ring

/-- The forced minus square of the Deninger source evaluation is exactly the squared resolvent
created by P-G199's common radial generator. -/
theorem neg_sq_xiWeilCauchyTest_routePPrimitiveDeningerUpperPoint
    (pe : Nat.Primes × ℕ) (kappa : ℝ) (q : XiRightZeroCopy) :
    -(xiWeilCauchyTest (routePPrimitiveDeningerUpperPoint pe kappa : ℂ)
        (xiSpectralPoint q.1)) ^ (2 : ℕ) =
      (xiRightCenteredZero q +
        routePPrimitiveBurnolCenteredMode pe kappa)⁻¹ ^ (2 : ℕ) := by
  rw [xiWeilCauchyTest_routePPrimitiveDeningerUpperPoint]
  rw [mul_pow]
  norm_num [I_mul_I]

/-- **Coefficient-faithful graph incidence.**  The Laplace report of an actual primitive Burnol
window at a strict-right Xi mode is its resolved von Mangoldt amplitude times the forced negative
square of the canonical Deninger upper-sector Cauchy evaluation. -/
theorem integral_routePPrimitiveBurnolWindowFeature_eq_deningerSquaredEvaluation
    (pe : Nat.Primes × ℕ) (kappa : ℝ) (q : XiRightZeroCopy) :
    (∫ L : ℝ in Ioi 0,
      Complex.exp (-(xiRightCenteredZero q * (L : ℂ))) *
        routePPrimitiveBurnolWindowFeature pe kappa L) =
      finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) *
        (-(xiWeilCauchyTest
          (routePPrimitiveDeningerUpperPoint pe kappa : ℂ)
          (xiSpectralPoint q.1)) ^ (2 : ℕ)) := by
  let lam := routePPrimitiveBurnolCenteredMode pe kappa
  have hrate : 0 < (xiRightCenteredZero q + lam).re := by
    rw [Complex.add_re, routePPrimitiveBurnolCenteredMode_re]
    exact add_pos (xiRightCenteredZero_re_pos q)
      (xiGammaEulerPrimitiveLogFrequency_pos pe)
  rw [show (fun L : ℝ =>
      Complex.exp (-(xiRightCenteredZero q * (L : ℂ))) *
        routePPrimitiveBurnolWindowFeature pe kappa L) =
      fun L : ℝ =>
        finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) *
          (Complex.exp (-(xiRightCenteredZero q * (L : ℂ))) *
            xiWardResolvedRadialGeneratorMode lam L) by
    funext L
    rw [routePPrimitiveBurnolWindowFeature_eq_resolvedRadialGeneratorMode]
    dsimp [lam, routePPrimitiveBurnolCenteredMode]
    ring]
  rw [MeasureTheory.integral_const_mul,
    integral_xiWardResolvedRadialGeneratorMode_laplace hrate]
  rw [neg_sq_xiWeilCauchyTest_routePPrimitiveDeningerUpperPoint]

end

end RHTower
