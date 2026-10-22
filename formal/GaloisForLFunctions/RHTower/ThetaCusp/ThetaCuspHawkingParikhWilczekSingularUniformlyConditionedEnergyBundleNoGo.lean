import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekSingularNeutralOrbitBoundednessNoGo

/-!
# No uniformly conditioned invariant energy bundle for the singular PW carrier

The exact singular Parikh--Wilczek reflection admits a positive conserved energy after allowing
the energy to depend on the source scale.  This leaves a serious analytic escape from the fixed
Hilbert-space no-go: use a scale-dependent Hilbert bundle and make every reflection fibrewise
unitary.

This module kills every regular version of that escape.  It allows the fibre energy to be an
arbitrary function—no quadratic, bilinear, diagonal, continuity, or linearity hypothesis is used.
If one pair of positive constants compares every fibre energy with neutral two-channel energy,
exact reflection invariance forces

`m * max (a(x)^(2 : ℕ)) (a(x)⁻¹)^(2 : ℕ) ≤ M`.

Since the source-forced gain is cofinally unbounded, no such global constants exist.  The result is
sharp: the already-constructed source-adapted energy is invariant and lies exactly between the
minimum and maximum reciprocal gain weights.  Hence every surviving invariant energy bundle must
become singularly ill-conditioned.

This kills the regular source-dependent completion class in

`PW endpoint winding -> unique singular FE carrier -> uniformly conditioned source-dependent
conserved energy -> partner balance -> shared Ward -> RH`.

Only singular/degenerating energy bundles or genuine unbounded operator-domain/connection data
survive.

`[NEW] [PW-B ROUTE-CLASS NO-GO] [ENERGY-BUNDLE RIGIDITY] [SHARP] [LEAN-PROVED]`
-/

open Complex Real Filter Set Topology

namespace RHTower

noncomputable section

/-- The opposite neutral input channel reads off reciprocal-gain amplification. -/
theorem pwNeutralChannelEnergy_singularReflectionBlock_one_zero
    (x : ℝ) :
    pwNeutralChannelEnergy (pwSingularReflectionBlock x (1, 0)) =
      (pwSingularReflectionGain x)⁻¹ ^ (2 : ℕ) := by
  simp [pwNeutralChannelEnergy, pwSingularReflectionBlock]

/-- Exact conditioning law forced on any energy invariant under one singular PW block. -/
theorem pwInvariantEnergy_conditioning_forced
    (energy : PWReflectionPair → ℝ) {x m M : ℝ}
    (hlower : ∀ w, m * pwNeutralChannelEnergy w ≤ energy w)
    (hupper : ∀ w, energy w ≤ M * pwNeutralChannelEnergy w)
    (hinvariant : ∀ w,
      energy (pwSingularReflectionBlock x w) = energy w) :
    m * max (pwSingularReflectionGain x ^ (2 : ℕ))
        ((pwSingularReflectionGain x)⁻¹ ^ (2 : ℕ)) ≤ M := by
  have hforward : m * pwSingularReflectionGain x ^ (2 : ℕ) ≤ M := by
    calc
      m * pwSingularReflectionGain x ^ (2 : ℕ) =
          m * pwNeutralChannelEnergy (pwSingularReflectionBlock x (0, 1)) := by
            rw [pwNeutralChannelEnergy_singularReflectionBlock_zero_one]
      _ ≤ energy (pwSingularReflectionBlock x (0, 1)) := hlower _
      _ = energy (0, 1) := hinvariant _
      _ ≤ M * pwNeutralChannelEnergy (0, 1) := hupper _
      _ = M := by norm_num [pwNeutralChannelEnergy]
  have hbackward : m * (pwSingularReflectionGain x)⁻¹ ^ (2 : ℕ) ≤ M := by
    calc
      m * (pwSingularReflectionGain x)⁻¹ ^ (2 : ℕ) =
          m * pwNeutralChannelEnergy (pwSingularReflectionBlock x (1, 0)) := by
            rw [pwNeutralChannelEnergy_singularReflectionBlock_one_zero]
      _ ≤ energy (pwSingularReflectionBlock x (1, 0)) := hlower _
      _ = energy (1, 0) := hinvariant _
      _ ≤ M * pwNeutralChannelEnergy (1, 0) := hupper _
      _ = M := by norm_num [pwNeutralChannelEnergy]
  rcases le_total (pwSingularReflectionGain x ^ (2 : ℕ))
      ((pwSingularReflectionGain x)⁻¹ ^ (2 : ℕ)) with hle | hle
  · rw [max_eq_right hle]
    exact hbackward
  · rw [max_eq_left hle]
    exact hforward

/-- A regular source-dependent completion: every fibre energy is uniformly equivalent to neutral
energy and exactly invariant under its source-forced reflection block. -/
def PWSingularUniformlyConditionedInvariantEnergyBundle : Prop :=
  ∃ (energy : ℝ → PWReflectionPair → ℝ) (m M : ℝ),
    0 < m ∧ 0 ≤ M ∧
    ∀ x : ℝ, 0 < x →
      (∀ w, m * pwNeutralChannelEnergy w ≤ energy x w) ∧
      (∀ w, energy x w ≤ M * pwNeutralChannelEnergy w) ∧
      (∀ w, energy x (pwSingularReflectionBlock x w) = energy x w)

/-- No uniformly conditioned scale-dependent invariant energy bundle exists. -/
theorem no_pwSingularUniformlyConditionedInvariantEnergyBundle :
    ¬ PWSingularUniformlyConditionedInvariantEnergyBundle := by
  rintro ⟨energy, m, M, hm, _hMnonneg, hbundle⟩
  have hlarge : ∀ᶠ x in atTop,
      M / m <
        pwNeutralChannelEnergy (pwSingularReflectionBlock x (0, 1)) :=
    tendsto_pwNeutralChannelEnergy_singularReflectionBlock_zero_one_atTop.eventually
      (eventually_gt_atTop (M / m))
  have hxpos : ∀ᶠ x : ℝ in atTop, 0 < x := eventually_gt_atTop 0
  rcases (hlarge.and hxpos).exists with ⟨x, hMx, hx⟩
  rcases hbundle x hx with ⟨hlower, hupper, hinvariant⟩
  have hforced :=
    pwInvariantEnergy_conditioning_forced (energy x) hlower hupper hinvariant
  have hgain : m * pwSingularReflectionGain x ^ (2 : ℕ) ≤ M :=
    le_trans
      (mul_le_mul_of_nonneg_left
        (le_max_left (pwSingularReflectionGain x ^ (2 : ℕ))
          ((pwSingularReflectionGain x)⁻¹ ^ (2 : ℕ))) hm.le)
      hforced
  have hresponse :
      m * pwNeutralChannelEnergy (pwSingularReflectionBlock x (0, 1)) ≤ M := by
    rwa [pwNeutralChannelEnergy_singularReflectionBlock_zero_one]
  have hcancel : m * (M / m) = M := by
    field_simp [hm.ne']
  nlinarith

/-- The exact source-adapted energy has the forced reciprocal-gain min/max conditioning. -/
theorem pwSingularReflectionEnergy_minmax_bounds
    (x : ℝ) (w : PWReflectionPair) :
    min (pwSingularReflectionGain x)⁻¹ (pwSingularReflectionGain x) *
        pwNeutralChannelEnergy w ≤ pwSingularReflectionEnergy x w ∧
      pwSingularReflectionEnergy x w ≤
        max (pwSingularReflectionGain x)⁻¹ (pwSingularReflectionGain x) *
          pwNeutralChannelEnergy w := by
  rcases w with ⟨u, v⟩
  have hminLeft := min_le_left
    (pwSingularReflectionGain x)⁻¹ (pwSingularReflectionGain x)
  have hminRight := min_le_right
    (pwSingularReflectionGain x)⁻¹ (pwSingularReflectionGain x)
  have hmaxLeft := le_max_left
    (pwSingularReflectionGain x)⁻¹ (pwSingularReflectionGain x)
  have hmaxRight := le_max_right
    (pwSingularReflectionGain x)⁻¹ (pwSingularReflectionGain x)
  have hu : 0 ≤ u ^ (2 : ℕ) := sq_nonneg u
  have hv : 0 ≤ v ^ (2 : ℕ) := sq_nonneg v
  simp only [pwNeutralChannelEnergy, pwSingularReflectionEnergy]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hminLeft) hu,
      mul_nonneg (sub_nonneg.mpr hminRight) hv]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hmaxLeft) hu,
      mul_nonneg (sub_nonneg.mpr hmaxRight) hv]

theorem pwSingularReflectionEnergy_min_coefficient_pos
    {x : ℝ} (hx : 0 < x) :
    0 < min (pwSingularReflectionGain x)⁻¹
      (pwSingularReflectionGain x) := by
  exact lt_min (inv_pos.mpr (pwSingularReflectionGain_pos hx))
    (pwSingularReflectionGain_pos hx)

/-- Closed certificate: regular source-dependent Hilbert completion is impossible, and the exact
source-adapted completion realizes the forced singular conditioning. -/
def PWSingularUniformlyConditionedEnergyBundleNoGo : Prop :=
  (∀ (energy : PWReflectionPair → ℝ) (x m M : ℝ),
    (∀ w, m * pwNeutralChannelEnergy w ≤ energy w) →
    (∀ w, energy w ≤ M * pwNeutralChannelEnergy w) →
    (∀ w, energy (pwSingularReflectionBlock x w) = energy w) →
    m * max (pwSingularReflectionGain x ^ (2 : ℕ))
      ((pwSingularReflectionGain x)⁻¹ ^ (2 : ℕ)) ≤ M) ∧
  ¬ PWSingularUniformlyConditionedInvariantEnergyBundle ∧
  (∀ x : ℝ, 0 < x →
    0 < min (pwSingularReflectionGain x)⁻¹
      (pwSingularReflectionGain x) ∧
    ∀ w : PWReflectionPair,
      pwSingularReflectionEnergy x (pwSingularReflectionBlock x w) =
        pwSingularReflectionEnergy x w ∧
      min (pwSingularReflectionGain x)⁻¹ (pwSingularReflectionGain x) *
          pwNeutralChannelEnergy w ≤ pwSingularReflectionEnergy x w ∧
      pwSingularReflectionEnergy x w ≤
        max (pwSingularReflectionGain x)⁻¹ (pwSingularReflectionGain x) *
          pwNeutralChannelEnergy w)

/-- **[PW-B ROUTE-CLASS NO-GO].** Every invariant source-dependent energy bundle uniformly
comparable with physical neutral energy is impossible; singular conditioning is necessary. -/
theorem pwSingularUniformlyConditionedEnergyBundle_noGo :
    PWSingularUniformlyConditionedEnergyBundleNoGo := by
  refine ⟨?_, no_pwSingularUniformlyConditionedInvariantEnergyBundle, ?_⟩
  · intro energy x m M hlower hupper hinvariant
    exact pwInvariantEnergy_conditioning_forced energy hlower hupper hinvariant
  · intro x hx
    refine ⟨pwSingularReflectionEnergy_min_coefficient_pos hx, ?_⟩
    intro w
    exact ⟨pwSingularReflectionEnergy_invariant hx w,
      pwSingularReflectionEnergy_minmax_bounds x w⟩

end

end RHTower
