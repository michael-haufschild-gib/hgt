import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekSingularCarrierRescalingGaugeNoGo

/-!
# The singular PW carrier has no uniformly bounded neutral realization

The source-forced singular Parikh--Wilczek reflection is algebraically conjugate to bare channel
exchange by the positive gauge `g = sqrt a`.  The preceding gauge no-go leaves a possible analytic
escape: perhaps the conjugated blocks still define a uniformly bounded family on one fixed,
source-independent two-channel Hilbert norm.

This module closes that escape.  Reciprocal covariance transports the already-proved blow-up of
`g⁻¹` at the singular Borel edge to blow-up of `g` at infinity.  Hence the exact carrier gain and
the neutral energy amplification of the single channel `(0, 1)` both tend to infinity.  No finite
constant can bound every positive-scale block in the fixed neutral energy.  More strongly, no
fixed source-independent energy coercive against the neutral norm admits such a bound; this
includes every fixed Hilbert norm on the two-channel space.

The obstruction is sharp: every individual block still preserves its positive source-adapted
energy, while the fixed neutral energy is invariant exactly at the self-dual scale.  Thus the
regular fixed-neutral Hilbert/domain branch is killed in

`PW endpoint winding -> unique singular FE carrier -> bounded neutral realization ->
partner balance -> shared Ward -> RH`.

Only an unbounded/domain-sensitive realization or a source-dependent weighted completion survives.

`[NEW] [PW-B ROUTE-CLASS NO-GO] [UNIFORM BOUNDEDNESS] [SHARP SURVIVOR] [LEAN-PROVED]`
-/

open Complex Real Filter Set Topology

namespace RHTower

noncomputable section

/-- Reciprocal inversion sends large positive scales to the punctured positive boundary. -/
theorem tendsto_inv_atTop_nhdsGT_zero_pw :
    Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨tendsto_inv_atTop_zero, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact inv_pos.mpr hx

/-- Reciprocal covariance forces the trivializing gauge to diverge at large scales. -/
theorem tendsto_pwSingularReflectionGauge_atTop :
    Tendsto pwSingularReflectionGauge atTop atTop := by
  have hcomp :=
    tendsto_pwSingularReflectionGauge_inv_atTop.comp
      tendsto_inv_atTop_nhdsGT_zero_pw
  refine hcomp.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [Function.comp_apply]
  rw [pwSingularReflectionGauge_inv hx, inv_inv]

theorem pwSingularReflectionGain_eq_gauge_sq
    {x : ℝ} (hx : 0 < x) :
    pwSingularReflectionGain x = pwSingularReflectionGauge x ^ (2 : ℕ) := by
  rw [pwSingularReflectionGauge,
    Real.sq_sqrt (pwSingularReflectionGain_pos hx).le]

private theorem tendsto_sq_atTop_pw :
    Tendsto (fun y : ℝ => y ^ (2 : ℕ)) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [eventually_ge_atTop (max b 1)] with y hy
  have hb : b ≤ y := le_trans (le_max_left b 1) hy
  have hyone : 1 ≤ y := le_trans (le_max_right b 1) hy
  nlinarith

/-- The exact singular reflection gain diverges cofinally. -/
theorem tendsto_pwSingularReflectionGain_atTop :
    Tendsto pwSingularReflectionGain atTop atTop := by
  have hsq := tendsto_sq_atTop_pw.comp
    tendsto_pwSingularReflectionGauge_atTop
  refine hsq.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simpa only [Function.comp_apply] using
    (pwSingularReflectionGain_eq_gauge_sq hx).symm

/-- One neutral input channel reads off the square of the exact singular gain. -/
theorem pwNeutralChannelEnergy_singularReflectionBlock_zero_one
    (x : ℝ) :
    pwNeutralChannelEnergy (pwSingularReflectionBlock x (0, 1)) =
      pwSingularReflectionGain x ^ (2 : ℕ) := by
  simp [pwNeutralChannelEnergy, pwSingularReflectionBlock]

/-- Neutral energy amplification already diverges on the fixed input `(0, 1)`. -/
theorem tendsto_pwNeutralChannelEnergy_singularReflectionBlock_zero_one_atTop :
    Tendsto
      (fun x : ℝ =>
        pwNeutralChannelEnergy (pwSingularReflectionBlock x (0, 1)))
      atTop atTop := by
  have hsq := tendsto_sq_atTop_pw.comp
    tendsto_pwSingularReflectionGain_atTop
  refine hsq.congr' (Filter.Eventually.of_forall ?_)
  intro x
  simp only [Function.comp_apply]
  exact (pwNeutralChannelEnergy_singularReflectionBlock_zero_one x).symm

/-- Uniform boundedness in one fixed neutral quadratic energy, with the conventional squared
operator bound. -/
def PWSingularNeutralOrbitUniformlyBounded : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → ∀ w : PWReflectionPair,
    pwNeutralChannelEnergy (pwSingularReflectionBlock x w) ≤
      C ^ (2 : ℕ) * pwNeutralChannelEnergy w

/-- No fixed neutral Hilbert norm makes the source-forced singular blocks uniformly bounded. -/
theorem no_pwSingularNeutralOrbitUniformlyBounded :
    ¬ PWSingularNeutralOrbitUniformlyBounded := by
  rintro ⟨C, _hCnonneg, hC⟩
  have hlarge : ∀ᶠ x in atTop,
      C ^ (2 : ℕ) <
        pwNeutralChannelEnergy (pwSingularReflectionBlock x (0, 1)) :=
    tendsto_pwNeutralChannelEnergy_singularReflectionBlock_zero_one_atTop.eventually
      (eventually_gt_atTop (C ^ (2 : ℕ)))
  have hxpos : ∀ᶠ x : ℝ in atTop, 0 < x := eventually_gt_atTop 0
  rcases (hlarge.and hxpos).exists with ⟨x, hCx, hx⟩
  have hbound := hC x hx (0, 1)
  simp [pwNeutralChannelEnergy] at hbound
  exact (not_lt_of_ge hbound) hCx

/-- A source-independent fixed energy is uniformly coercive if it dominates one positive multiple
of neutral energy; uniform boundedness then asks for one operator bound at every positive scale. -/
def PWSingularFixedCoerciveEnergyUniformlyBounded : Prop :=
  ∃ (energy : PWReflectionPair → ℝ) (m C : ℝ),
    0 < m ∧ 0 ≤ C ∧
    (∀ w : PWReflectionPair, m * pwNeutralChannelEnergy w ≤ energy w) ∧
    (∀ x : ℝ, 0 < x → ∀ w : PWReflectionPair,
      energy (pwSingularReflectionBlock x w) ≤ C ^ (2 : ℕ) * energy w)

/-- No fixed source-independent coercive energy can uniformly bound the singular carrier family. -/
theorem no_pwSingularFixedCoerciveEnergyUniformlyBounded :
    ¬ PWSingularFixedCoerciveEnergyUniformlyBounded := by
  rintro ⟨energy, m, C, hm, _hCnonneg, hcoerce, hbound⟩
  let D : ℝ := C ^ (2 : ℕ) * energy (0, 1)
  have hlarge : ∀ᶠ x in atTop,
      D / m <
        pwNeutralChannelEnergy (pwSingularReflectionBlock x (0, 1)) :=
    tendsto_pwNeutralChannelEnergy_singularReflectionBlock_zero_one_atTop.eventually
      (eventually_gt_atTop (D / m))
  have hxpos : ∀ᶠ x : ℝ in atTop, 0 < x := eventually_gt_atTop 0
  rcases (hlarge.and hxpos).exists with ⟨x, hDx, hx⟩
  have hlower := hcoerce (pwSingularReflectionBlock x (0, 1))
  have hupper := hbound x hx (0, 1)
  change energy (pwSingularReflectionBlock x (0, 1)) ≤ D at hupper
  have hcancel : m * (D / m) = D := by
    field_simp [hm.ne']
  nlinarith

/-- Closed certificate killing the regular fixed-neutral Hilbert/domain realization. -/
def PWSingularNeutralOrbitBoundednessNoGo : Prop :=
  Tendsto pwSingularReflectionGauge atTop atTop ∧
  Tendsto pwSingularReflectionGain atTop atTop ∧
  Tendsto
    (fun x : ℝ =>
      pwNeutralChannelEnergy (pwSingularReflectionBlock x (0, 1)))
    atTop atTop ∧
  ¬ PWSingularNeutralOrbitUniformlyBounded ∧
  ¬ PWSingularFixedCoerciveEnergyUniformlyBounded ∧
  (∀ x : ℝ, 0 < x → ∀ w : PWReflectionPair,
    pwSingularReflectionEnergy x (pwSingularReflectionBlock x w) =
      pwSingularReflectionEnergy x w) ∧
  (∀ x : ℝ, 0 < x →
    ((∀ w : PWReflectionPair,
      pwNeutralChannelEnergy (pwSingularReflectionBlock x w) =
        pwNeutralChannelEnergy w) ↔ x = 1))

/-- **[PW-B ROUTE-CLASS NO-GO].** The unique singular carrier cannot be a uniformly bounded
family on the fixed neutral two-channel energy.  Source-adapted conservation remains exact. -/
theorem pwSingularNeutralOrbit_boundedness_noGo :
    PWSingularNeutralOrbitBoundednessNoGo := by
  exact ⟨tendsto_pwSingularReflectionGauge_atTop,
    tendsto_pwSingularReflectionGain_atTop,
    tendsto_pwNeutralChannelEnergy_singularReflectionBlock_zero_one_atTop,
    no_pwSingularNeutralOrbitUniformlyBounded,
    no_pwSingularFixedCoerciveEnergyUniformlyBounded,
    fun _x hx w => pwSingularReflectionEnergy_invariant hx w,
    fun _x hx => pwNeutralChannelEnergy_block_invariant_iff hx⟩

end

end RHTower
