import GaloisForLFunctions.RHTower.Suzuki.SuzukiWardContinuousCoDivergence

/-!
# Completed-light residual cannot be paid by the regular Suzuki continuum

The literal unit-Riesz source has an exact positive/negative Suzuki wall-light
split.  At spectral center the negative light is precisely half of its finite
prime mass.  It is tempting to pay that light directly with the positive
regular-screw continuum.  This module excludes that exact payment: the
remaining continuum residual has forced scale `sqrt N / 6`, and hence escapes
to infinity unconditionally.

Thus a source-faithful Ward assembly must retain a further signed relative
term; identifying the continuum with the negative light alone loses a
macroscopic part of the completed source.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- At spectral center, regular-screw mass left after exact negative-light payment has the
forced normalized limit `1 / 6`. -/
theorem tendsto_suzukiUnitRieszLightCompletedRegularResidual_zero_div_sqrt_atTop_one_sixth :
    Tendsto (fun N : ℕ =>
      suzukiUnitRieszLightCompletedRegularResidual (N + 2) 0 /
        Real.sqrt ((N + 2 : ℕ) : ℝ)) atTop (nhds (1 / 6 : ℝ)) := by
  have hprime : Tendsto (fun N : ℕ =>
      unitRieszCoherentPrimeOutgoingCharge (N + 2) /
        Real.sqrt ((N + 2 : ℕ) : ℝ)) atTop (nhds (1 / 3 : ℝ)) :=
    tendsto_unitRieszCoherentPrimeOutgoingCharge_div_sqrt_atTop_one_third.comp
      (Filter.tendsto_add_atTop_nat 2)
  have hneg : Tendsto (fun N : ℕ =>
      suzukiUnitRieszReporterWeightedNegativeLightMass (N + 2) 0 /
        Real.sqrt ((N + 2 : ℕ) : ℝ)) atTop (nhds (1 / 6 : ℝ)) := by
    have hscale := hprime.const_mul (1 / 2 : ℝ)
    have hval : (1 / 2 : ℝ) * (1 / 3 : ℝ) = 1 / 6 := by norm_num
    rw [hval] at hscale
    refine hscale.congr' ?_
    filter_upwards with N
    rw [suzukiUnitRieszReporterWeightedNegativeLightMass_zero_eq_prime_half
      (by omega : 2 ≤ N + 2)]
    ring
  have hregular :=
    tendsto_suzukiUnitRieszRegularWardMass_logNat_div_sqrt_atTop_one_third
  have hsub := hregular.sub hneg
  have hval2 : (1 / 3 : ℝ) - 1 / 6 = 1 / 6 := by norm_num
  rw [hval2] at hsub
  refine hsub.congr' ?_
  filter_upwards with N
  rw [suzukiUnitRieszLightCompletedRegularResidual]
  ring

/-- The center residual after direct negative-light payment is unbounded; no finite continuum
completion can identify regular mass with negative light. -/
theorem tendsto_suzukiUnitRieszLightCompletedRegularResidual_zero_atTop :
    Tendsto (fun N : ℕ =>
      suzukiUnitRieszLightCompletedRegularResidual (N + 2) 0) atTop atTop := by
  have hratio :=
    tendsto_suzukiUnitRieszLightCompletedRegularResidual_zero_div_sqrt_atTop_one_sixth
  have hsqrt : Tendsto (fun N : ℕ => Real.sqrt ((N + 2 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 2))
  rw [tendsto_atTop] at hsqrt ⊢
  intro b
  filter_upwards [hsqrt (12 * b),
    hratio.eventually (Ioi_mem_nhds (by norm_num : (1 / 12 : ℝ) < 1 / 6))]
      with N hroot hratioN
  have hsqrtpos : 0 < Real.sqrt ((N + 2 : ℕ) : ℝ) := by positivity
  have hres : (1 / 12 : ℝ) * Real.sqrt ((N + 2 : ℕ) : ℝ) <
      suzukiUnitRieszLightCompletedRegularResidual (N + 2) 0 :=
    (lt_div_iff₀ hsqrtpos).mp hratioN
  linarith

end GaloisForLFunctions.RHTower
