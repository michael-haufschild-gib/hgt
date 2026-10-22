import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheCertificateReadsTheScaleNotTheDepth

/-!
# The scale datum: sharp in its own unit, blind to the depth

In the width unit the aperture ladder is flat: every bounded stage certifies the trivial `½`. That
is a statement about the unit. In the **scale** unit the same ladder is sharp at every stage and
converges to the critical line, and this module proves both halves exactly.

The scale datum of a configuration is its set of **failure apertures**
`failureApertures Z = {a > 0 : Z is already not Weil-positive at aperture a}`. It is an up-set
(`failureApertures_upSet`), and:

* `failureApertures_eq_empty_iff_width_eq_zero` — it is empty exactly when the width is zero. The
  scale datum is therefore an exact criterion, for `ζ`'s configuration exactly RH.
* `failureApertures_subset_Ioi_of_aperturePositivity` together with
  `exists_mem_shadow_failureApertures_eq_Ioi` — the aperture-`a` certificate certifies exactly
  `failureApertures ⊆ (a, ∞)`, and that is attained: a configuration in its shadow has failure set
  exactly `(a, ∞)`. Since `⋂_{a > 0} (a, ∞) = ∅`, the stages of the ladder converge to the
  criterion (`apertureLadderConvergesInTheScaleUnit`), each one sharply.
* `resolutionLimit_width_of_refines_failureApertures` — and the whole scale datum, not merely one
  certificate, is blind to the depth: **every** reading determined by the failure set has
  resolution limit `½` for the width. Knowing exactly at which apertures a configuration fails
  says nothing about how deep its off-line zeros are.

So the finite-aperture programme is not worthless and not flat; it is a sharp ladder in the scale
unit whose limit is the criterion. What no amount of it reaches is the depth, which is a second,
independent coordinate (`scaleAndDepthAreIndependent`).
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The scale datum is an up-set and an exact criterion -/

/-- Failure propagates upwards: a configuration that fails at one aperture fails at every larger
one, because positivity at a larger aperture contains positivity at a smaller one. -/
theorem failureApertures_upSet {Z : TemperedZeroConfig} {a b : ℝ}
    (ha : a ∈ failureApertures Z) (hab : a ≤ b) : b ∈ failureApertures Z :=
  ⟨lt_of_lt_of_le ha.1 hab, fun hb => ha.2 (aperturePositivity_mono hab hb)⟩

/-- Every compactly supported test has an aperture. -/
theorem exists_aperture_of_hasCompactSupport {f : ℝ → ℂ} (hfc : HasCompactSupport f) :
    ∃ a : ℝ, 0 < a ∧ tsupport f ⊆ Icc (-a) a := by
  obtain ⟨r, hr⟩ := (IsCompact.isBounded hfc).subset_closedBall (0 : ℝ)
  refine ⟨max r 1, lt_of_lt_of_le zero_lt_one (le_max_right r 1), ?_⟩
  intro x hx
  have hmem := hr hx
  rw [Real.closedBall_eq_Icc] at hmem
  simp only [zero_sub, zero_add] at hmem
  exact ⟨by linarith [hmem.1, le_max_left r 1], by linarith [hmem.2, le_max_left r 1]⟩

/-- **The scale datum is an exact criterion.** A configuration has no failure aperture exactly
when its width is zero: for `ζ`'s configuration, exactly RH. -/
theorem failureApertures_eq_empty_iff_width_eq_zero (Z : TemperedZeroConfig) :
    failureApertures Z = ∅ ↔ width Z = 0 := by
  rw [Set.eq_empty_iff_forall_notMem]
  constructor
  · intro h
    refine (configWidth_eq_zero_iff_weil_nonneg Z.2).mpr fun f hf hfc => ?_
    obtain ⟨a, ha, hsub⟩ := exists_aperture_of_hasCompactSupport hfc
    by_contra hneg
    exact h a ⟨ha, fun hpos => hneg (hpos f hf hsub)⟩
  · intro hw a ha
    exact ha.2 fun f hf hfs =>
      (configWidth_eq_zero_iff_weil_nonneg Z.2).mp hw f hf
        (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
          ((subset_tsupport f).trans hfs))

/-! ### 2. The certificate certifies exactly an up-set, and sharply -/

/-- A certificate at aperture `a` confines the failure set to `(a, ∞)`. -/
theorem failureApertures_subset_Ioi_of_aperturePositivity {a : ℝ} {Z : TemperedZeroConfig}
    (hZ : aperturePositivity a Z) : failureApertures Z ⊆ Ioi a := by
  intro b hb
  rw [mem_Ioi]
  by_contra h
  exact hb.2 (aperturePositivity_mono (not_lt.mp h) hZ)

/-- **The scale datum of a lattice is the complement of its Nyquist aperture.** -/
theorem failureApertures_offLineLattice {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    failureApertures (offLineLattice hL hδ hδ') = Ioi (L / 2) := by
  ext b
  simp only [failureApertures, mem_setOf_eq, mem_Ioi,
    aperturePositivity_offLineLattice_iff hL hδ hδ', not_le]
  exact ⟨fun h => h.2, fun h => ⟨by linarith, h⟩⟩

/-- **The confinement is attained, at every depth.** Inside the shadow of the aperture-`a`
certificate there is, for each depth `δ`, a configuration whose failure set is exactly `(a, ∞)`. -/
theorem exists_mem_shadow_failureApertures_eq_Ioi {a : ℝ} (ha : 0 < a) {Z : TemperedZeroConfig}
    (hZ : aperturePositivity a Z) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    ∃ W ∈ shadow (aperturePositivity a) Z, failureApertures W = Ioi a ∧ width W = δ := by
  have hL : (0 : ℝ) < 2 * a := by linarith
  refine ⟨offLineLattice hL hδ hδ', propext (iff_of_true
    ((aperturePositivity_offLineLattice_iff hL hδ hδ' a).mpr (by linarith)) hZ), ?_, ?_⟩
  · rw [failureApertures_offLineLattice hL hδ hδ', show 2 * a / 2 = a by ring]
  · exact width_offLineLattice hL hδ hδ'

/-- **The ladder converges in the scale unit.** The aperture-`a` certificate confines the failure
set to `(a, ∞)` and no further, and the intersection of those confinements over all apertures is
the criterion `failureApertures = ∅`, that is, width zero. -/
theorem apertureLadderConvergesInTheScaleUnit (Z : TemperedZeroConfig) :
    ((∀ a : ℝ, 0 < a → failureApertures Z ⊆ Ioi a) ↔ width Z = 0) ∧
      ∀ a : ℝ, 0 < a → aperturePositivity a Z → failureApertures Z ⊆ Ioi a := by
  refine ⟨⟨fun h => ?_, fun hw a _ => ?_⟩,
    fun _ _ hZ => failureApertures_subset_Ioi_of_aperturePositivity hZ⟩
  · refine (failureApertures_eq_empty_iff_width_eq_zero Z).mp (Set.eq_empty_iff_forall_notMem.mpr
      fun b hb => ?_)
    have := h b hb.1 hb
    rw [mem_Ioi] at this
    exact absurd this (lt_irrefl b)
  · rw [(failureApertures_eq_empty_iff_width_eq_zero Z).mpr hw]
    exact Set.empty_subset _

/-! ### 3. The scale datum is blind to the depth -/

/-- **Nothing read from the failure set constrains the depth.** For a configuration whose failure
set is exactly `(a, ∞)`, every reading determined by the failure set — the set itself, the
visibility frequency, any aperture certificate, any statistic of them — has resolution limit `½`
for the width. -/
theorem resolutionLimit_width_of_refines_failureApertures {a : ℝ} (ha : 0 < a) {O : Type*}
    {r : TemperedZeroConfig → O} (href : Refines failureApertures r)
    {Z : TemperedZeroConfig} (hZ : failureApertures Z = Ioi a) :
    resolutionLimit width r Z = 1 / 2 := by
  have hL : (0 : ℝ) < 2 * a := by linarith
  have hδ : (0 : ℝ) < 1 / 2 := by norm_num
  have hfail : failureApertures (offLineLattice hL hδ le_rfl) = failureApertures Z := by
    rw [failureApertures_offLineLattice hL hδ le_rfl, show 2 * a / 2 = a by ring, hZ]
  have hmem : offLineLattice hL hδ le_rfl ∈ shadow r Z := href Z _ hfail
  refine le_antisymm (csSup_le (shadow_image_nonempty width r Z) ?_) ?_
  · rintro x ⟨W, -, rfl⟩
    exact width_le_half W
  · have hw : width (offLineLattice hL hδ le_rfl) = 1 / 2 :=
      width_offLineLattice hL hδ le_rfl
    exact hw ▸ le_csSup (bddAbove_width_image _) ⟨_, hmem, rfl⟩

/-- The visibility frequency is read from the failure set, so it inherits the blindness. -/
theorem refines_failureApertures_visibilityFrequency :
    Refines failureApertures visibilityFrequency :=
  refines_of_comp failureApertures
    (g := fun S : Set ℝ => sSup ((fun a : ℝ => a⁻¹) '' S)) (fun _ => rfl)

/-- **The exact scale leaves the depth free.** -/
theorem resolutionLimit_width_visibilityFrequency {a : ℝ} (ha : 0 < a)
    {Z : TemperedZeroConfig} (hZ : failureApertures Z = Ioi a) :
    resolutionLimit width visibilityFrequency Z = 1 / 2 :=
  resolutionLimit_width_of_refines_failureApertures ha
    refines_failureApertures_visibilityFrequency hZ

/-! ### 4. Scale and depth are independent coordinates -/

/-- **Independence.** Every pair (scale, depth) is realised: the two coordinates are unconstrained
by one another, and they vanish together exactly at the critical line. -/
theorem scaleAndDepthAreIndependent :
    (∀ a δ : ℝ, 0 < a → 0 < δ → δ ≤ 1 / 2 → ∃ Z : TemperedZeroConfig,
        failureApertures Z = Ioi a ∧ width Z = δ) ∧
      ∀ Z : TemperedZeroConfig, failureApertures Z = ∅ ↔ width Z = 0 := by
  refine ⟨fun a δ ha hδ hδ' => ?_, failureApertures_eq_empty_iff_width_eq_zero⟩
  have hL : (0 : ℝ) < 2 * a := by linarith
  exact ⟨offLineLattice hL hδ hδ', by
    rw [failureApertures_offLineLattice hL hδ hδ', show 2 * a / 2 = a by ring],
    width_offLineLattice hL hδ hδ'⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
