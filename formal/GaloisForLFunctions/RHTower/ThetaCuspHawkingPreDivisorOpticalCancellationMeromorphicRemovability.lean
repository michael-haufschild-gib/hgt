import GaloisForLFunctions.RHTower.ThetaCuspHawkingPreDivisorOpticalCancellationHolomorphyObstruction

/-!
# Pre-divisor optical cancellation: meromorphic removability obstruction

The HC74 cancellation profile is finite and continuous at every point of the open critical strip.
Consequently, a meromorphic scalar function agreeing with that profile throughout the strip has
only removable singularities: `MeromorphicAt.analyticAt` upgrades it pointwise to analytic. HC74's
holomorphic obstruction then excludes this apparent meromorphic relaxation as well.

This does not exclude partially defined meromorphic response functions with genuine poles, branch
cuts, support-domain discontinuities, antiholomorphic dependence, or operator-valued completions.
-/

open Complex Set Filter Topology

namespace RHTower

noncomputable section

/-- The exact pre-divisor optical-cancellation profile, pulled back along `Complex.re`, is
continuous at every point of the open critical strip. -/
theorem continuousAt_d4PreDivisorOpticalCancellationSusceptibility_re
    (z : ℂ) (hz : z ∈ {w : ℂ | 0 < w.re ∧ w.re < 1}) :
    ContinuousAt
      (fun w : ℂ =>
        (d4PreDivisorOpticalCancellationSusceptibility w.re : ℂ)) z := by
  change 0 < z.re ∧ z.re < 1 at hz
  have hA : d4PreDivisorHorizonAngularShift z.re ≠ 0 := by
    unfold d4PreDivisorHorizonAngularShift
    exact ne_of_gt (mul_pos hz.1 (by linarith))
  have hB : d4PreDivisorReflectedHorizonAngularShift z.re ≠ 0 := by
    unfold d4PreDivisorReflectedHorizonAngularShift
    exact ne_of_gt (mul_pos (by linarith) (by linarith))
  have hAcont : ContinuousAt
      (fun w : ℂ => d4PreDivisorHorizonAngularShift w.re) z := by
    unfold d4PreDivisorHorizonAngularShift
    fun_prop
  have hBcont : ContinuousAt
      (fun w : ℂ => d4PreDivisorReflectedHorizonAngularShift w.re) z := by
    unfold d4PreDivisorReflectedHorizonAngularShift
    fun_prop
  have hcross : ContinuousAt
      (fun w : ℂ => d4EventHorizonThirdMassParityCrossNumerator
        (d4PreDivisorHorizonAngularShift w.re)
        (d4PreDivisorReflectedHorizonAngularShift w.re)) z := by
    unfold d4EventHorizonThirdMassParityCrossNumerator
    fun_prop
  have hthird : ContinuousAt
      (fun w : ℂ =>
        d4PreDivisorEventHorizonThirdMassReflectionSusceptibility w.re) z := by
    unfold d4PreDivisorEventHorizonThirdMassReflectionSusceptibility
    dsimp only
    exact (continuousAt_const.mul hcross).div
      ((hAcont.pow 3).mul (hBcont.pow 3))
      (mul_ne_zero (pow_ne_zero _ hA) (pow_ne_zero _ hB))
  have hden : ContinuousAt
      (fun w : ℂ => d4PreDivisorThetaMirrorAIMEDenominator w.re) z := by
    unfold d4PreDivisorThetaMirrorAIMEDenominator
    fun_prop
  apply Complex.continuous_ofReal.continuousAt.comp
  unfold d4PreDivisorOpticalCancellationSusceptibility
  exact (hthird.mul hden).div_const 12

/-- A meromorphic scalar response agreeing everywhere on the open critical strip with the exact
finite optical-cancellation profile is analytic there: every alleged pole is removable. -/
theorem analyticOnNhd_of_meromorphicOn_eq_d4PreDivisorOpticalCancellationSusceptibility_re
    (f : ℂ → ℂ)
    (hmeromorphic : MeromorphicOn f {z : ℂ | 0 < z.re ∧ z.re < 1})
    (hprofile : ∀ z : ℂ, z ∈ {z : ℂ | 0 < z.re ∧ z.re < 1} →
      f z = (d4PreDivisorOpticalCancellationSusceptibility z.re : ℂ)) :
    AnalyticOnNhd ℂ f {z : ℂ | 0 < z.re ∧ z.re < 1} := by
  intro z hz
  apply (hmeromorphic z hz).analyticAt
  have heq : f =ᶠ[𝓝 z]
      (fun w : ℂ =>
        (d4PreDivisorOpticalCancellationSusceptibility w.re : ℂ)) := by
    filter_upwards [isOpen_criticalOpenStrip.mem_nhds hz] with w hw
    exact hprofile w hw
  rw [continuousAt_congr heq]
  exact continuousAt_d4PreDivisorOpticalCancellationSusceptibility_re z hz

/-- No everywhere-finite meromorphic scalar response on the open critical strip can track the
unique pre-divisor optical-cancellation susceptibility. A meromorphic candidate would be analytic
by removability and therefore contradict the HC74 holomorphic obstruction. -/
theorem not_exists_meromorphic_preDivisorOpticalCancellationSusceptibility :
    ¬ ∃ f : ℂ → ℂ,
      MeromorphicOn f {z : ℂ | 0 < z.re ∧ z.re < 1} ∧
        ∀ z : ℂ, z ∈ {z : ℂ | 0 < z.re ∧ z.re < 1} →
          f z = (d4PreDivisorOpticalCancellationSusceptibility z.re : ℂ) := by
  rintro ⟨f, hmeromorphic, hprofile⟩
  apply not_exists_holomorphic_preDivisorOpticalCancellationSusceptibility
  exact ⟨f,
    analyticOnNhd_of_meromorphicOn_eq_d4PreDivisorOpticalCancellationSusceptibility_re
      f hmeromorphic hprofile,
    hprofile⟩

end

end RHTower
