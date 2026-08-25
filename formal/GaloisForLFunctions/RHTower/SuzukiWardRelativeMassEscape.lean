import GaloisForLFunctions.RHTower.CCMUnitRieszSharpPoleClassification
import GaloisForLFunctions.RHTower.SuzukiWardAtomicContinuousLightWeld

/-!
# RH forces relative, not absolute, Suzuki Ward completion

The literal Suzuki wall-light mass and regular-screw mass are both positive.  This module proves
a falsifiable consequence of treating their Ward weld as a relative object: under RH, both
unrenormalized masses escape to `+∞`, at every fixed wall height, while their difference remains
uniformly bounded.  Consequently neither mass can have a finite real cofinal limit even when RH
is true.  Any viable infinite Suzuki completion must therefore retain the common divergent sector
and control its relative displacement; absolute Hilbert-energy convergence is the wrong endpoint.
-/

open Set MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

private theorem tendsto_sqrtNat_div_three_sub_two_atTop :
    Tendsto (fun N : ℕ => Real.sqrt (N : ℝ) / 3 - 2) atTop atTop := by
  have hsqrt : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  rw [tendsto_atTop] at hsqrt ⊢
  intro b
  filter_upwards [hsqrt (3 * (b + 2))] with N hN
  linarith

private theorem tendsto_nat_add_two_atTop :
    Tendsto (fun N : ℕ => N + 2) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop b] with N hN
  omega

private theorem no_finite_limit_of_tendsto_atTop
    {f : ℕ → ℝ} (hf : Tendsto f atTop atTop) (L : ℝ) :
    ¬ Tendsto f atTop (𝓝 L) := by
  intro hL
  have hlarge : ∀ᶠ N in atTop, L + 1 ≤ f N :=
    (tendsto_atTop.1 hf) (L + 1)
  have hsmall : ∀ᶠ N in atTop, f N < L + 1 / 2 :=
    hL (Iio_mem_nhds (by norm_num : L < L + 1 / 2))
  rcases (hlarge.and hsmall).exists with ⟨N, hlargeN, hsmallN⟩
  exact (not_lt_of_ge (by linarith : L + 1 / 2 ≤ f N)) hsmallN

/-- Under RH the positive finite-prime Ward mass escapes to `+∞`.  The proof uses the exact
polar reference `sqrt N / 3` and the corpus sharp RH bound on completed outgoing charge. -/
theorem tendsto_unitRieszCoherentPrimeOutgoingCharge_atTop_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    Tendsto unitRieszCoherentPrimeOutgoingCharge atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_
    tendsto_sqrtNat_div_three_sub_two_atTop
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hcompleted :=
    _root_.RHTower.abs_unitRieszCoherentCompletedOutgoingCharge_lt_two_of_riemannHypothesis
      hRH hN
  rw [unitRieszCoherentCompletedOutgoingCharge,
    unitRieszCoherentPolarOutgoingCharge_eq] at hcompleted
  exact le_of_lt (by linarith [abs_lt.mp hcompleted |>.1])

/-- Under RH the positive regular-screw continuum co-diverges with finite-prime Ward mass. -/
theorem tendsto_suzukiUnitRieszRegularWardMass_logNat_atTop_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    Tendsto (fun N : ℕ =>
      suzukiUnitRieszRegularWardMass (Real.log ((N + 2 : ℕ) : ℝ))) atTop atTop := by
  have hprimeShift : Tendsto (fun N : ℕ =>
      unitRieszCoherentPrimeOutgoingCharge (N + 2)) atTop atTop :=
    (tendsto_unitRieszCoherentPrimeOutgoingCharge_atTop_of_riemannHypothesis hRH).comp
      tendsto_nat_add_two_atTop
  obtain ⟨B, _hB, hbound⟩ :=
    riemannHypothesis_iff_suzukiWardAtomicContinuousImbalanceBounded.mp hRH
  have hprimeSub : Tendsto (fun N : ℕ =>
      unitRieszCoherentPrimeOutgoingCharge (N + 2) - B) atTop atTop := by
    rw [tendsto_atTop] at hprimeShift ⊢
    intro b
    filter_upwards [hprimeShift (b + B)] with N hN
    linarith
  refine tendsto_atTop_mono' atTop ?_ hprimeSub
  filter_upwards with N
  have h := hbound N
  rw [abs_le] at h
  linarith

/-- At every fixed wall height, total literal wall-light energy escapes under RH. -/
theorem tendsto_suzukiUnitRieszReporterWeightedWallLightMass_atTop_of_riemannHypothesis
    (hRH : RiemannHypothesis) (t : ℝ) :
    Tendsto (fun N : ℕ =>
      suzukiUnitRieszReporterWeightedWallLightMass (N + 2) t) atTop atTop := by
  have hprimeShift : Tendsto (fun N : ℕ =>
      unitRieszCoherentPrimeOutgoingCharge (N + 2)) atTop atTop :=
    (tendsto_unitRieszCoherentPrimeOutgoingCharge_atTop_of_riemannHypothesis hRH).comp
      tendsto_nat_add_two_atTop
  apply hprimeShift.congr'
  filter_upwards with N
  exact (suzukiUnitRieszReporterWeightedWallLightMass_eq_primeOutgoingCharge
    (by omega : 2 ≤ N + 2) t).symm

/-- **Relative-mass escape law.**  Under RH, literal wall-light mass and regular-screw mass both
escape to `+∞`, but their Ward displacement remains uniformly bounded. -/
theorem riemannHypothesis_forces_divergent_wallLight_regularPair
    (hRH : RiemannHypothesis) (t : ℝ) :
    Tendsto (fun N : ℕ =>
        suzukiUnitRieszReporterWeightedWallLightMass (N + 2) t) atTop atTop ∧
      Tendsto (fun N : ℕ =>
        suzukiUnitRieszRegularWardMass (Real.log ((N + 2 : ℕ) : ℝ))) atTop atTop ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
        |suzukiUnitRieszReporterWeightedWallLightMass (N + 2) t -
          suzukiUnitRieszRegularWardMass (Real.log ((N + 2 : ℕ) : ℝ))| ≤ B := by
  refine ⟨
    tendsto_suzukiUnitRieszReporterWeightedWallLightMass_atTop_of_riemannHypothesis hRH t,
    tendsto_suzukiUnitRieszRegularWardMass_logNat_atTop_of_riemannHypothesis hRH, ?_⟩
  obtain ⟨B, hB, hbound⟩ :=
    riemannHypothesis_iff_suzukiWardAtomicContinuousImbalanceBounded.mp hRH
  refine ⟨B, hB, fun N => ?_⟩
  rw [suzukiUnitRieszReporterWeightedWallLightMass_eq_primeOutgoingCharge
    (by omega : 2 ≤ N + 2) t]
  exact hbound N

/-- Even under RH, neither unrenormalized side of the Suzuki Ward weld has a finite real cofinal
limit. -/
theorem no_finite_absolute_suzukiWardMassLimits_of_riemannHypothesis
    (hRH : RiemannHypothesis) (t wallLimit regularLimit : ℝ) :
    ¬ Tendsto (fun N : ℕ =>
        suzukiUnitRieszReporterWeightedWallLightMass (N + 2) t)
      atTop (𝓝 wallLimit) ∧
      ¬ Tendsto (fun N : ℕ =>
        suzukiUnitRieszRegularWardMass (Real.log ((N + 2 : ℕ) : ℝ)))
      atTop (𝓝 regularLimit) := by
  exact ⟨
    no_finite_limit_of_tendsto_atTop
      (tendsto_suzukiUnitRieszReporterWeightedWallLightMass_atTop_of_riemannHypothesis
        hRH t) wallLimit,
    no_finite_limit_of_tendsto_atTop
      (tendsto_suzukiUnitRieszRegularWardMass_logNat_atTop_of_riemannHypothesis hRH)
      regularLimit⟩

end GaloisForLFunctions.RHTower
