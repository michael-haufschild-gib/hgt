import GaloisForLFunctions.RHTower.XiMassPrimeSquareAsymptoticCarrier
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaXiMassConnectionGreenCompensation

/-!
# Two-residue asymptotic carrier of the compensated Route T current

Radial Riemann--Lebesgue extinction removes every integrable centered mass-shell packet.  The
higher prime powers also vanish by a common summable envelope.  What survives in the exact
theta-Green / adjacent-prime compensation law is therefore a finite two-mode carrier:

* the crossed archimedean zero at frequency `sqrt(a^(2 : ℕ)-1/4)`, coefficient `2*pi`;
* the prime-square pole at frequency `a`, coefficient `-pi/2`.

This classifies the complete future vertical asymptotic modulo a term tending to zero.  No RH
hypothesis, positivity assumption, or asymptotic expansion is used.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- Explicit two-residue carrier of the compensated theta/prime current. -/
def xiMassThetaPrimeConnectionAsymptoticCarrier
    (a : ℝ) (tau : ℂ) : ℂ :=
  Complex.I * pinnedFirstMoment thetaQuantileCoordinate *
    (2 * Real.pi * xiMassAnalyticTest a tau xiMassArchPole -
      (Real.pi / 2 : ℂ) * xiMassAnalyticTest a tau 0)

/-- Absolutely summable high prime powers become extinct in future vertical time. -/
theorem tendsto_xiMassHighPrimePowerTail_vertical_atTop_zero
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) :
    Tendsto (fun u : ℝ =>
      xiMassHighPrimePowerTail a ((sigma : ℂ) + u * I)) atTop (𝓝 0) := by
  unfold xiMassHighPrimePowerTail
  have hpoint : ∀ pk : Nat.Primes × ℕ,
      Tendsto (fun u : ℝ =>
        xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I)
          ((pk.1 : ℕ) ^ (pk.2 + 3))) atTop (𝓝 (0 : ℂ)) := by
    intro pk
    exact tendsto_xiMassCenteredPrimeAtom_vertical_atTop_zero
      ha hsigma ((pk.1 : ℕ) ^ (pk.2 + 3))
  have hdom : ∀ᶠ u : ℝ in atTop, ∀ pk : Nat.Primes × ℕ,
      ‖xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I)
        ((pk.1 : ℕ) ^ (pk.2 + 3))‖ ≤
      xiMassPrimePowerCriticalWeight pk.1 (pk.2 + 2) *
        (∫ x : ℝ, Real.exp (-(sigma * |x|))) :=
    Filter.Eventually.of_forall fun u pk => by
      simpa only [add_assoc] using
        norm_xiMassCenteredPrimeAtom_primePower_le
          ha hsigma u pk.1 (pk.2 + 2)
  simpa using tendsto_tsum_of_dominated_convergence
    (summable_xiMassPrimePowerCriticalWeight_high.mul_right
      (∫ x : ℝ, Real.exp (-(sigma * |x|)))) hpoint hdom

/-- Centered archimedean packet has no persistent vertical component. -/
theorem tendsto_integral_xiMassCenteredArchIntegrand_vertical_atTop_zero
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) :
    Tendsto (fun u : ℝ =>
      ∫ x : ℝ, xiMassCenteredArchIntegrand a ((sigma : ℂ) + u * I) x)
      atTop (𝓝 0) := by
  let f : ℝ → ℂ := xiMassCenteredArchIntegrand a (sigma : ℂ)
  have hf : Integrable f := by
    simpa only [f, ofReal_zero, zero_mul, add_zero] using
      (integrable_xiMassCenteredArchIntegrand
        (a := a) (σ := sigma) (u := 0) ha hsigma)
  have hradial := tendsto_integral_exp_radialFrequency_mul_atTop_zero ha hf
  refine hradial.congr fun u => ?_
  apply integral_congr_ae
  filter_upwards with x
  dsimp only [f, xiMassCenteredArchIntegrand]
  have hzero := xiMassAnalyticTest_ofReal_eq_radial_time ha sigma 0 x
  have hu := xiMassAnalyticTest_ofReal_eq_radial_time ha sigma u x
  have hzero' : xiMassAnalyticTest a (sigma : ℂ) (x : ℂ) =
      Complex.exp (-(sigma * xiMassRadialFrequency a x : ℝ)) := by
    simpa only [ofReal_zero, zero_mul, mul_zero, neg_zero, exp_zero, mul_one,
      add_zero] using hzero
  rw [hzero', hu]
  ring

/-- Bottom archimedean source modulo its crossed pole tends to zero. -/
theorem tendsto_xiMassBottomArchIntegral_sub_poleCarrier_atTop_zero
    {a c sigma : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hsigma : 0 < sigma) :
    Tendsto (fun u : ℝ =>
      xiMassBottomArchIntegral a c ((sigma : ℂ) + u * I) -
        2 * Real.pi *
          xiMassAnalyticTest a ((sigma : ℂ) + u * I) xiMassArchPole)
      atTop (𝓝 0) := by
  have ha : 0 < a := by linarith
  have hcenter :=
    tendsto_integral_xiMassCenteredArchIntegrand_vertical_atTop_zero ha hsigma
  refine hcenter.congr' (Filter.Eventually.of_forall fun u => ?_)
  change (∫ x : ℝ,
      xiMassCenteredArchIntegrand a ((sigma : ℂ) + u * I) x) =
    xiMassBottomArchIntegral a c ((sigma : ℂ) + u * I) -
      2 * Real.pi *
        xiMassAnalyticTest a ((sigma : ℂ) + u * I) xiMassArchPole
  rw [xiMassBottomArchIntegral,
    integral_xiMassBottomArch_eq_centered_add_residue hhalf hca
      (show 0 < (((sigma : ℂ) + u * I)).re by simpa using hsigma)]
  ring

/-- **Complete future asymptotic classification of the compensated Route T current.** -/
theorem tendsto_xiMassThetaPrimeConnectionCompensatedPacket_sub_carrier_atTop_zero
    {a c sigma : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hsigma : 0 < sigma) :
    Tendsto (fun u : ℝ =>
      xiMassThetaPrimeConnectionCompensatedPacket a c
          ((sigma : ℂ) + u * I) -
        xiMassThetaPrimeConnectionAsymptoticCarrier a
          ((sigma : ℂ) + u * I)) atTop (𝓝 0) := by
  have ha : 0 < a := by linarith
  have harch :=
    tendsto_xiMassBottomArchIntegral_sub_poleCarrier_atTop_zero
      hhalf hca hsigma
  have hsquare :=
    tendsto_xiMassPrimeSquareLayer_sub_poleCarrier_atTop_zero ha hsigma
  have hhigh := tendsto_xiMassHighPrimePowerTail_vertical_atTop_zero ha hsigma
  have hsource : Tendsto (fun u : ℝ =>
      (xiMassBottomArchIntegral a c ((sigma : ℂ) + u * I) -
        2 * Real.pi *
          xiMassAnalyticTest a ((sigma : ℂ) + u * I) xiMassArchPole) -
      ((xiMassPrimeSquareLayer a ((sigma : ℂ) + u * I) -
        (Real.pi / 2 : ℂ) *
          xiMassAnalyticTest a ((sigma : ℂ) + u * I) 0) +
        xiMassHighPrimePowerTail a ((sigma : ℂ) + u * I)))
      atTop (𝓝 0) := by
    simpa using harch.sub (hsquare.add hhigh)
  have hscaled := hsource.const_mul
    (Complex.I * pinnedFirstMoment thetaQuantileCoordinate)
  have hscaled' : Tendsto (fun u : ℝ =>
      (Complex.I * pinnedFirstMoment thetaQuantileCoordinate) *
        ((xiMassBottomArchIntegral a c ((sigma : ℂ) + u * I) -
          2 * Real.pi *
            xiMassAnalyticTest a ((sigma : ℂ) + u * I) xiMassArchPole) -
        ((xiMassPrimeSquareLayer a ((sigma : ℂ) + u * I) -
          (Real.pi / 2 : ℂ) *
            xiMassAnalyticTest a ((sigma : ℂ) + u * I) 0) +
          xiMassHighPrimePowerTail a ((sigma : ℂ) + u * I))))
      atTop (𝓝 0) := by
    simpa using hscaled
  refine hscaled'.congr' (Filter.Eventually.of_forall fun u => ?_)
  have htau : 0 < (((sigma : ℂ) + u * I)).re := by simpa using hsigma
  change (Complex.I * pinnedFirstMoment thetaQuantileCoordinate) *
      ((xiMassBottomArchIntegral a c ((sigma : ℂ) + u * I) -
        2 * Real.pi *
          xiMassAnalyticTest a ((sigma : ℂ) + u * I) xiMassArchPole) -
      ((xiMassPrimeSquareLayer a ((sigma : ℂ) + u * I) -
        (Real.pi / 2 : ℂ) *
          xiMassAnalyticTest a ((sigma : ℂ) + u * I) 0) +
        xiMassHighPrimePowerTail a ((sigma : ℂ) + u * I))) =
    xiMassThetaPrimeConnectionCompensatedPacket a c
        ((sigma : ℂ) + u * I) -
      xiMassThetaPrimeConnectionAsymptoticCarrier a
        ((sigma : ℂ) + u * I)
  rw [xiMassThetaPrimeConnectionCompensatedPacket_eq_arch_sub_nonPrime
    hhalf hca htau]
  unfold xiMassThetaPrimeConnectionAsymptoticCarrier
  ring

end

end RHTower
