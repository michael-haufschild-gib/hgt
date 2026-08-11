import GaloisForLFunctions.HTGeometry.PoleUnitGammaBase
import GaloisForLFunctions.RHTower.HighExponentShellSourcePole

/-!
# Euler-shell specialization of the pole-unit formation cocycle

The high-exponent shell source has a simple pole at `s = 1`.  In the pole coordinate `z = s - 1`
its regular unit is `U_m(z) = G(1+z)·H_m(1+z)` with `G = (s-1)ζ(s)`, so the shell source is an
instance of the pole-unit formation mechanics with pole order `1`.

Two shell-specific facts are certified: the relative shell-source response is exactly the
pole-retaining response of `U_m`, and the first constitutive correction coefficient of `U_m` is
the Euler–Mascheroni constant plus the logarithmic derivative of the literal shell multiplier.
Through the cumulant laws these give the exact mean and variance of the shell clock.
-/

open Complex Filter Topology RHTower

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The regular unit of the shell source read in the pole coordinate `z = s - 1`. -/
def shellUnit (m : ℕ) (z : ℂ) : ℂ := shellResidueUnit m (1 + z)

@[simp] theorem shellUnit_zero (m : ℕ) : shellUnit m 0 = shellMultiplier m 1 := by
  simp [shellUnit]

theorem shellUnit_zero_ne_zero {m : ℕ} (hm : 2 ≤ m) : shellUnit m 0 ≠ 0 := by
  simpa using shellResidueUnit_one_ne_zero hm

theorem analyticAt_shellUnit {m : ℕ} (hm : 12 ≤ m) {z : ℂ} (hz : 1 / 2 < (1 + z).re) :
    AnalyticAt ℂ (shellUnit m) z := by
  have hshift : AnalyticAt ℂ (fun y : ℂ => 1 + y) z := analyticAt_const.add analyticAt_id
  exact (analyticAt_shellResidueUnit hm hz).comp hshift

/-- **Shell relative response.**  The normalized shell source ratio is the pole-retaining response
of the shell unit at pole order one. -/
theorem shellSource_relative_response (m : ℕ) {ε w : ℂ} (hε : ε ≠ 0) (hw : w ≠ 0) :
    shellSource m (1 + ε * w) / shellSource m (1 + ε) =
      polarScaleResponse 1 (shellUnit m) ε w := by
  have hne1 : (1 : ℂ) + ε * w ≠ 1 := by
    intro h
    exact (mul_ne_zero hε hw) (by linear_combination h)
  have hne2 : (1 : ℂ) + ε ≠ 1 := by
    intro h
    exact hε (by linear_combination h)
  rw [shellSource_eq_of_ne_one hne1, shellSource_eq_of_ne_one hne2]
  have h1 : (1 : ℂ) + ε * w - 1 = ε * w := by ring
  have h2 : (1 : ℂ) + ε - 1 = ε := by ring
  rw [h1, h2, polarScaleResponse, correctedScaleResponse, shellUnit, shellUnit, pow_one]
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_inv, inv_inv]
  rw [show shellResidueUnit m (1 + ε * w) * (ε⁻¹ * w⁻¹) *
        ((shellResidueUnit m (1 + ε))⁻¹ * ε)
      = (ε⁻¹ * ε) * (w⁻¹ * (shellResidueUnit m (1 + ε * w) *
        (shellResidueUnit m (1 + ε))⁻¹)) from by ring,
    inv_mul_cancel₀ hε, one_mul]

/-- **First constitutive coefficient of a high-exponent shell.**  The linear logarithmic
correction of the shell unit is the Euler–Mascheroni constant plus the logarithmic derivative of
the shell multiplier at the pole. -/
theorem logDeriv_shellUnit_zero {m : ℕ} (hm : 12 ≤ m) :
    logDeriv (shellUnit m) 0 =
      (Real.eulerMascheroniConstant : ℂ) + logDeriv (shellMultiplier m) 1 := by
  have hhalf : (1 : ℝ) / 2 < (1 : ℂ).re := by norm_num
  have hHne : shellMultiplier m 1 ≠ 0 := shellMultiplier_ne_zero hm hhalf
  have hGne : zetaResidueUnit 1 ≠ 0 := by rw [zetaResidueUnit_one]; norm_num
  have hGdiff : DifferentiableAt ℂ zetaResidueUnit 1 :=
    (analyticAt_zetaResidueUnit 1).differentiableAt
  have hHdiff : DifferentiableAt ℂ (shellMultiplier m) 1 :=
    (analyticAt_shellMultiplier hm hhalf).differentiableAt
  have hprod : logDeriv (shellResidueUnit m) 1 =
      logDeriv zetaResidueUnit 1 + logDeriv (shellMultiplier m) 1 := by
    have hfun : shellResidueUnit m = fun s => zetaResidueUnit s * shellMultiplier m s := rfl
    rw [hfun, logDeriv_mul 1 hGne hHne hGdiff hHdiff]
  have hd : deriv (shellUnit m) 0 = deriv (shellResidueUnit m) 1 := by
    have h1 : HasDerivAt (fun y : ℂ => 1 + y) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_add 1
    have h2 : HasDerivAt (shellResidueUnit m) (deriv (shellResidueUnit m) 1) (1 + 0) := by
      rw [add_zero]
      exact (analyticAt_shellResidueUnit hm hhalf).differentiableAt.hasDerivAt
    have h3 : HasDerivAt (shellUnit m) (deriv (shellResidueUnit m) 1 * 1) 0 := h2.comp 0 h1
    simpa using h3.deriv
  have hz : shellUnit m 0 = shellResidueUnit m 1 := by simp [shellUnit]
  rw [logDeriv_apply, hd, hz, ← logDeriv_apply, hprod, logDeriv_zetaResidueUnit_one]

/-- The shell correction coefficient is continuous at the pole. -/
theorem tendsto_logDeriv_shellUnit {m : ℕ} (hm : 12 ≤ m) :
    Tendsto (logDeriv (shellUnit m)) (𝓝 0)
      (𝓝 ((Real.eulerMascheroniConstant : ℂ) + logDeriv (shellMultiplier m) 1)) := by
  have hhalf : (1 : ℝ) / 2 < (1 + (0 : ℂ)).re := by norm_num
  have hana : AnalyticAt ℂ (shellUnit m) 0 := analyticAt_shellUnit hm hhalf
  have hne : shellUnit m 0 ≠ 0 := shellUnit_zero_ne_zero (by omega)
  have hcont : ContinuousAt (logDeriv (shellUnit m)) 0 :=
    (hana.deriv.continuousAt).div hana.continuousAt hne
  have := hcont.tendsto
  rwa [logDeriv_shellUnit_zero hm] at this

/-- **Shell clock mean.**  The first cumulant of the shell response at the base scale is one minus
the transported first correction coefficient. -/
theorem shellClock_mean {m : ℕ} (hm : 12 ≤ m) {ε : ℂ} (hre : 1 / 2 < (1 + ε).re)
    (hne : shellUnit m ε ≠ 0) :
    -logDeriv (fun z => polarScaleResponse 1 (shellUnit m) ε z) 1 =
      1 - ε * logDeriv (shellUnit m) ε := by
  have h := polarScaleResponse_first_cumulant 1 (U := shellUnit m) (ε := ε)
    (analyticAt_shellUnit hm hre).differentiableAt hne
  simpa using h

/-- **Shell clock variance.**  The second cumulant of the shell response at the base scale is one
plus the transported curvature of the shell unit logarithm. -/
theorem shellClock_variance {m : ℕ} (hm : 12 ≤ m) {ε : ℂ} (hre : 1 / 2 < (1 + ε).re)
    (hne : ∀ᶠ z in 𝓝 ε, shellUnit m z ≠ 0) (hε : shellUnit m ε ≠ 0) :
    deriv (fun z => logDeriv (fun y => polarScaleResponse 1 (shellUnit m) ε y) z) 1 =
      1 + ε ^ 2 * deriv (logDeriv (shellUnit m)) ε := by
  have h := polarScaleResponse_second_cumulant 1 (U := shellUnit m) (ε := ε)
    (analyticAt_shellUnit hm hre) hne hε
  simpa using h

end

end GaloisForLFunctions.HTGeometry
