import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheResolutionLimitOfAReading
import GaloisForLFunctions.SquareRootThreshold.TheZeroWidthIsAnUnboundedApertureProperty

/-!
# The aperture certificate is blind in every unit

This module carries the field's vocabulary and its one negative mechanism.

A datum is a tempered zero configuration; its invariant is the `width`, the largest distance of a
zero from the critical line. A *reading* of it is what a method actually sees, and the readings of
the programme are certificates: `aperturePositivity a` (the Weil form is nonnegative on tests of
aperture `a`), its coercive strengthening `apertureGain a η`, a whole family `familyPositivity`, and
the unconditional `fullPositivity`.

The mechanism is a single construction. For every aperture there is a configuration of maximal
width `½` that satisfies the certificate for free — zeros spaced widely enough that no test of that
aperture reaches a pair of them. It therefore lies in the shadow of every datum satisfying the
certificate, and the floor theorem fixes the resolution limit:

`resolutionLimit width (aperturePositivity a) Z = ½`.

Everything else in this module is that one fact transported:

* to a coercive certificate at any level `η` (`resolutionLimit_width_apertureGain`) — coercivity buys
  nothing;
* to any monotone change of unit `g` (`resolutionLimit_comp_width_apertureGain`), so the floor is not
  an artefact of measuring depth in the width unit;
* to a family of configurations of any cardinality (`resolutionLimit_familyWidth_familyAperture`);
* and to the *lower* end: the on-line lattice lies in every aperture shadow, so the floor is `0` and
  the resolution interval is the entire range of the width
  (`resolutionInterval_width_aperturePositivity`). A bounded-aperture certificate can neither prove
  nor disprove the critical line.

The width realises exactly `[0, ½]` (`range_width`), so "limit `½`, floor `0`" is the statement that
the reading says nothing at all. This is the obstruction the positive half of the field answers by
reading magnitudes instead of signs.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold
open Zeta23
open Zeta23 _root_.RHTower

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

set_option autoImplicit false

-- from BoundedApertureReadingsHaveTheTrivialResolutionLimit.lean
/-! ### 1. The data and the unit -/

/-- The data of the trans-Nyquist calculus: tempered zero configurations. -/
def TemperedZeroConfig : Type := {Z : ZeroConfig // TemperedConfig Z}

/-- The unit: the width `sup |Re ρ − ½|` of the configuration. -/
noncomputable def width (Z : TemperedZeroConfig) : ℝ := configWidth Z.1

theorem width_nonneg (Z : TemperedZeroConfig) : 0 ≤ width Z := configWidth_nonneg Z.1

theorem width_le_half (Z : TemperedZeroConfig) : width Z ≤ 1 / 2 := configWidth_le_half Z.1

/-- The width image of any set of data is bounded by `½`, so every resolution limit below is
defined by a genuine supremum. -/
theorem bddAbove_width_image (s : Set TemperedZeroConfig) : BddAbove (width '' s) :=
  ⟨1 / 2, fun _ hx => by obtain ⟨Z, _, rfl⟩ := hx; exact width_le_half Z⟩

/-! ### 2. The aperture readings -/

/-- The aperture-`a` reading: the Weil form is nonnegative on every `C²` test supported in
`[−a, a]`. This is what a finite-aperture positivity certificate delivers. -/
def aperturePositivity (a : ℝ) (Z : TemperedZeroConfig) : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → 0 ≤ (Z.1.W f f).re

/-- The joint reading of a family of aperture certificates. -/
def familyPositivity {ι : Type*} (a : ι → ℝ) (Z : TemperedZeroConfig) : Prop :=
  ∀ i : ι, aperturePositivity (a i) Z

/-- The unbounded reading: positivity on every compactly supported `C²` test. -/
def fullPositivity (Z : TemperedZeroConfig) : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f → 0 ≤ (Z.1.W f f).re

/-- A certificate at a larger aperture contains the certificate at a smaller one. -/
theorem aperturePositivity_mono {a b : ℝ} (hab : a ≤ b) {Z : TemperedZeroConfig}
    (h : aperturePositivity b Z) : aperturePositivity a Z := fun f hf hs =>
  h f hf (hs.trans (Icc_subset_Icc (by linarith) hab))

/-- The off-line lattice of depth `½` and ordinate spacing `π/a`: width `½`, yet positive at
aperture `a`. -/
theorem exists_width_eq_half_aperturePositivity {a : ℝ} (ha : 0 < a) :
    ∃ Z : TemperedZeroConfig, width Z = 1 / 2 ∧ aperturePositivity a Z := by
  obtain ⟨Z, hZ, hw, hpos⟩ :=
    exists_configWidth_eq_and_weil_nonneg_on_aperture ha (by norm_num : (0 : ℝ) < 1 / 2) le_rfl
  exact ⟨⟨Z, hZ⟩, hw, hpos⟩

/-! ### 3. One aperture reads nothing -/

/-- **Every finite aperture has the trivial resolution limit.** A configuration certified positive
at aperture `a` shares that reading with configurations of every width up to `½`. -/
theorem resolutionLimit_width_aperturePositivity {a : ℝ} (ha : 0 < a) {Z : TemperedZeroConfig}
    (hZ : aperturePositivity a Z) :
    resolutionLimit width (aperturePositivity a) Z = 1 / 2 := by
  obtain ⟨Z', hw', hpos'⟩ := exists_width_eq_half_aperturePositivity ha
  refine le_antisymm ?_ ?_
  · refine csSup_le (shadow_image_nonempty width (aperturePositivity a) Z) ?_
    rintro x ⟨W, -, rfl⟩
    exact width_le_half W
  · have hmem : Z' ∈ shadow (aperturePositivity a) Z :=
      propext (iff_of_true hpos' hZ)
    exact hw' ▸ le_csSup (bddAbove_width_image _) ⟨Z', hmem, rfl⟩

/-- A finite-aperture certificate certifies the bound `β` on the width exactly when `β ≥ ½`: it
certifies nothing beyond what holds for every configuration. -/
theorem certifies_width_aperturePositivity_iff {a : ℝ} (ha : 0 < a) {Z : TemperedZeroConfig}
    (hZ : aperturePositivity a Z) {β : ℝ} :
    Certifies width (aperturePositivity a) Z β ↔ 1 / 2 ≤ β := by
  rw [certifies_iff_resolutionLimit_le (bddAbove_width_image _),
    resolutionLimit_width_aperturePositivity ha hZ]

/-! ### 4. Bounded families read nothing either -/

/-- **No bounded family of aperture certificates improves the trivial bound.** Joining the
certificates of an arbitrary family of apertures bounded by `A` intersects the shadows, and the
one lattice of spacing `π/A` lies in all of them. -/
theorem resolutionLimit_width_familyPositivity {ι : Type*} (a : ι → ℝ) {A : ℝ} (hA : 0 < A)
    (hbd : ∀ i : ι, a i ≤ A) {Z : TemperedZeroConfig} (hZ : familyPositivity a Z) :
    resolutionLimit width (familyPositivity a) Z = 1 / 2 := by
  obtain ⟨Z', hw', hpos'⟩ := exists_width_eq_half_aperturePositivity hA
  refine le_antisymm ?_ ?_
  · refine csSup_le (shadow_image_nonempty width (familyPositivity a) Z) ?_
    rintro x ⟨W, -, rfl⟩
    exact width_le_half W
  · have hfam : familyPositivity a Z' := fun i => aperturePositivity_mono (hbd i) hpos'
    have hmem : Z' ∈ shadow (familyPositivity a) Z := propext (iff_of_true hfam hZ)
    exact hw' ▸ le_csSup (bddAbove_width_image _) ⟨Z', hmem, rfl⟩

/-! ### 5. The unbounded reading is faithful, and the limit jumps -/

/-- **The unbounded aperture is faithful at the critical line.** Positivity on all compactly
supported tests is width zero, so the reading pins the width to `0`. -/
theorem resolutionLimit_width_fullPositivity {Z : TemperedZeroConfig} (hZ : fullPositivity Z) :
    resolutionLimit width fullPositivity Z = 0 := by
  have hzero : ∀ W ∈ shadow fullPositivity Z, width W = 0 := fun W hW =>
    (configWidth_eq_zero_iff_weil_nonneg W.2).mpr
      (fun f hf hs => ((mem_shadow_iff.mp hW) ▸ hZ : fullPositivity W) f hf hs)
  refine le_antisymm (csSup_le (shadow_image_nonempty width fullPositivity Z) ?_) ?_
  · rintro x ⟨W, hW, rfl⟩
    exact (hzero W hW).le
  · have := le_csSup (bddAbove_width_image (shadow fullPositivity Z))
      ⟨Z, mem_shadow_self fullPositivity Z, rfl⟩
    rw [hzero Z (mem_shadow_self fullPositivity Z)] at this
    exact this

/-- **The trans-Nyquist jump.** For a configuration positive at every aperture, every bounded
family of aperture certificates has resolution limit `½` while the unbounded reading has
resolution limit `0`: the information of the width lies entirely at infinity. -/
theorem apertureResolutionJump {Z : TemperedZeroConfig} (hZ : fullPositivity Z) :
    (∀ A : ℝ, 0 < A → resolutionLimit width (aperturePositivity A) Z = 1 / 2) ∧
      resolutionLimit width fullPositivity Z = 0 :=
  ⟨fun _ hA => resolutionLimit_width_aperturePositivity hA
      (fun f hf hs => hZ f hf (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
        ((subset_tsupport f).trans hs))),
    resolutionLimit_width_fullPositivity hZ⟩

/-- **No bounded-aperture reading resolves the critical line.** The reading of any family of
apertures bounded by `A` is shared by a configuration of width `½`, so it cannot decide width
zero — which, for the configuration of `ζ`, is RH. -/
theorem not_resolves_onLine_familyPositivity {ι : Type*} (a : ι → ℝ) {A : ℝ} (hA : 0 < A)
    (hbd : ∀ i : ι, a i ≤ A) {Z : TemperedZeroConfig} (hZ : familyPositivity a Z)
    (hw : width Z = 0) : ¬ Resolves (familyPositivity a) (fun W => width W = 0) := by
  obtain ⟨Z', hw', hpos'⟩ := exists_width_eq_half_aperturePositivity hA
  have hfam : familyPositivity a Z' := fun i => aperturePositivity_mono (hbd i) hpos'
  intro hres
  have h0 : width Z' = 0 := (hres Z Z' (propext (iff_of_true hfam hZ))).mpr hw
  rw [hw'] at h0
  norm_num at h0

-- the on-line lattice, the zero-width member of every aperture shadow
noncomputable def onLineLattice {L : ℝ} (hL : 0 < L) : TemperedZeroConfig :=
  ⟨onLineLatticeConfig hL, temperedConfig_onLineLatticeConfig hL⟩

theorem width_onLineLattice {L : ℝ} (hL : 0 < L) : width (onLineLattice hL) = 0 := by
  show configWidth (onLineLatticeConfig hL) = 0
  refine configWidth_eq_zero_iff_onLine.mpr ?_
  rintro ρ ⟨k, rfl⟩
  simp [verticalLatticePoint]

/-- A compactly supported test has an aperture. -/
theorem exists_aperture_of_hasCompactSupport {f : ℝ → ℂ} (hfc : HasCompactSupport f) :
    ∃ a : ℝ, 0 < a ∧ tsupport f ⊆ Icc (-a) a := by
  obtain ⟨r, hr⟩ := (IsCompact.isBounded hfc).subset_closedBall (0 : ℝ)
  refine ⟨max r 1, lt_of_lt_of_le zero_lt_one (le_max_right r 1), ?_⟩
  intro x hx
  have hmem := hr hx
  rw [Real.closedBall_eq_Icc] at hmem
  simp only [zero_sub, zero_add] at hmem
  exact ⟨by linarith [hmem.1, le_max_left r 1], by linarith [hmem.2, le_max_left r 1]⟩


theorem fullPositivity_onLineLattice {L : ℝ} (hL : 0 < L) : fullPositivity (onLineLattice hL) :=
  fun f _ _ => re_W_onLineLatticeConfig_nonneg hL f

/-- The critical line is positive at every aperture: the certificate never forces an off-line
zero. -/
theorem aperturePositivity_onLineLattice {L : ℝ} (hL : 0 < L) (a : ℝ) :
    aperturePositivity a (onLineLattice hL) := fun f _ _ =>
  re_W_onLineLatticeConfig_nonneg hL f

/-- A background lattice of spacing `2π/L` with one off-line pair inserted at height `γ₀`. -/
noncomputable def latticeWithPairAt {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (γ₀ : ℝ) : TemperedZeroConfig :=
  ⟨isolatedPairConfig hL hδ hδ' γ₀, temperedConfig_isolatedPairConfig hL hδ hδ' γ₀⟩

/-- The inserted pair sits at depth `δ`, so the width is at least `δ`. -/
theorem depth_le_width_latticeWithPairAt {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (γ₀ : ℝ) : δ ≤ width (latticeWithPairAt hL hδ hδ' γ₀) := by
  have hmem : offLinePoint δ γ₀ ∈ (isolatedPairConfig hL hδ hδ' γ₀).carrier :=
    Or.inl (Or.inr rfl)
  have h := abs_re_sub_half_le_configWidth hmem
  have hre : |(offLinePoint δ γ₀).re - 1 / 2| = δ := by
    simp only [offLinePoint]
    rw [show (1 / 2 + δ : ℝ) - 1 / 2 = δ by ring, abs_of_pos hδ]
  rwa [hre] at h

/-- **The witness's certificate is one explicit inequality.** Below the Nyquist aperture of the
background, the inserted pair is hidden at aperture `a` exactly when
`sinh (2 δ a) / δ ≤ 2 L + 2 a`. -/
theorem aperturePositivity_latticeWithPairAt_iff {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (γ₀ : ℝ) {a : ℝ} (ha : 0 < a) (haL : a ≤ L / 2) :
    aperturePositivity a (latticeWithPairAt hL hδ hδ' γ₀) ↔
      Real.sinh (2 * δ * a) / δ ≤ 2 * L + 2 * a :=
  isolatedPairConfig_weil_nonneg_iff hL hδ hδ' γ₀ ha haL

-- from TheResolutionIntervalIsTheWholeRange.lean
variable {D O O' : Type*} {I : D → ℝ}

/-! ### 2. The range of the width -/

theorem bddBelow_width_image (s : Set TemperedZeroConfig) : BddBelow (width '' s) :=
  ⟨0, fun _ hx => by obtain ⟨Z, _, rfl⟩ := hx; exact width_nonneg Z⟩

/-- The off-line lattice of spacing `2π/L` and depth `δ` as a datum of the calculus. -/
noncomputable def offLineLattice {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    TemperedZeroConfig :=
  ⟨offLineLatticeConfig hL hδ hδ', temperedConfig_offLineLatticeConfig hL hδ hδ'⟩

theorem width_offLineLattice {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    width (offLineLattice hL hδ hδ') = δ := configWidth_offLineLatticeConfig hL hδ hδ'

/-- **The width realises exactly `[0, ½]`**: the on-line lattice gives `0` and the depth-`δ`
off-line lattice gives `δ`. -/
theorem range_width : range width = Icc 0 (1 / 2) := by
  refine Set.Subset.antisymm ?_ fun δ hδ => ?_
  · rintro x ⟨Z, rfl⟩
    exact ⟨width_nonneg Z, width_le_half Z⟩
  · rcases eq_or_lt_of_le hδ.1 with rfl | hpos
    · exact ⟨onLineLattice (by norm_num : (0 : ℝ) < 1),
        width_onLineLattice (by norm_num : (0 : ℝ) < 1)⟩
    · exact ⟨offLineLattice (by norm_num : (0 : ℝ) < 1) hpos hδ.2,
        width_offLineLattice (by norm_num : (0 : ℝ) < 1) hpos hδ.2⟩

/-! ### 3. The floor of the bounded-aperture readings is zero -/

/-- **The on-line lattice lies in every aperture shadow.** Positivity at a fixed aperture is a
property the critical line always has, so it never forces an off-line zero. -/
theorem onLineLattice_mem_shadow_aperturePositivity {a : ℝ} {Z : TemperedZeroConfig}
    (hZ : aperturePositivity a Z) :
    onLineLattice (by norm_num : (0 : ℝ) < 1) ∈ shadow (aperturePositivity a) Z :=
  propext (iff_of_true
    (aperturePositivity_onLineLattice (by norm_num : (0 : ℝ) < 1) a) hZ)

/-- **The floor at every bounded aperture is `0`.** A finite-aperture certificate never certifies
a positive lower bound on the width: it cannot witness an off-line zero. -/
theorem resolutionFloor_width_aperturePositivity {a : ℝ} {Z : TemperedZeroConfig}
    (hZ : aperturePositivity a Z) : resolutionFloor width (aperturePositivity a) Z = 0 := by
  refine le_antisymm ?_ ((certifiesLower_iff_le_resolutionFloor (bddBelow_width_image _)).mp
    fun e _ => width_nonneg e)
  have h := csInf_le (bddBelow_width_image (shadow (aperturePositivity a) Z))
    ⟨_, onLineLattice_mem_shadow_aperturePositivity hZ, rfl⟩
  rwa [width_onLineLattice] at h

/-- The same for an arbitrary family of apertures. -/
theorem resolutionFloor_width_familyPositivity {ι : Type*} (a : ι → ℝ) {Z : TemperedZeroConfig}
    (hZ : familyPositivity a Z) : resolutionFloor width (familyPositivity a) Z = 0 := by
  have hmem : onLineLattice (by norm_num : (0 : ℝ) < 1) ∈ shadow (familyPositivity a) Z :=
    propext (iff_of_true
      (fun i => aperturePositivity_onLineLattice (by norm_num : (0 : ℝ) < 1) (a i)) hZ)
  refine le_antisymm ?_ ((certifiesLower_iff_le_resolutionFloor (bddBelow_width_image _)).mp
    fun e _ => width_nonneg e)
  have h := csInf_le (bddBelow_width_image (shadow (familyPositivity a) Z)) ⟨_, hmem, rfl⟩
  rwa [width_onLineLattice] at h

/-! ### 4. The interval is the whole range -/

/-- **Two-sided vacuity of a finite-aperture certificate.** The resolution interval of the width at
aperture `a` is the entire range of the width: the certificate neither bounds the width below `½`
nor bounds it above `0`, so it can neither prove nor disprove the critical line. -/
theorem resolutionInterval_width_aperturePositivity {a : ℝ} (ha : 0 < a)
    {Z : TemperedZeroConfig} (hZ : aperturePositivity a Z) :
    resolutionInterval width (aperturePositivity a) Z = range width := by
  rw [resolutionInterval, resolutionFloor_width_aperturePositivity hZ,
    resolutionLimit_width_aperturePositivity ha hZ, range_width]

/-- **Two-sided vacuity of any bounded family of certificates.** -/
theorem resolutionInterval_width_familyPositivity {ι : Type*} (a : ι → ℝ) {A : ℝ} (hA : 0 < A)
    (hbd : ∀ i : ι, a i ≤ A) {Z : TemperedZeroConfig} (hZ : familyPositivity a Z) :
    resolutionInterval width (familyPositivity a) Z = range width := by
  rw [resolutionInterval, resolutionFloor_width_familyPositivity a hZ,
    resolutionLimit_width_familyPositivity a hA hbd hZ, range_width]

-- from CoercivityAtABoundedApertureIsStillBlind.lean
/-! ### 1. The graded aperture reading -/

/-- The aperture-`a` certificate at level `η`: the Weil form of `Z` dominates `η ‖f‖²` on every
`C²` test supported in `[−a, a]`. At `η = 0` this is bare positivity; at `η > 0` it is a coercive
certificate with gap `η`. -/
def apertureGain (a η : ℝ) (Z : TemperedZeroConfig) : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
    η * ∫ t, ‖f t‖ ^ 2 ≤ (Z.1.W f f).re

theorem apertureGain_zero_iff {a : ℝ} {Z : TemperedZeroConfig} :
    apertureGain a 0 Z ↔ aperturePositivity a Z := by
  simp only [apertureGain, aperturePositivity, zero_mul]

/-- A larger gap is a stronger certificate. -/
theorem apertureGain_mono_level {a η η' : ℝ} (h : η' ≤ η) {Z : TemperedZeroConfig}
    (hZ : apertureGain a η Z) : apertureGain a η' Z := fun f hf hfs =>
  le_trans (mul_le_mul_of_nonneg_right h (MeasureTheory.integral_nonneg fun _ => by positivity)) (hZ f hf hfs)

/-- A certificate at a larger aperture contains the certificate at a smaller one. -/
theorem apertureGain_mono_aperture {a b η : ℝ} (hab : a ≤ b) {Z : TemperedZeroConfig}
    (hZ : apertureGain b η Z) : apertureGain a η Z := fun f hf hfs =>
  hZ f hf (hfs.trans (Icc_subset_Icc (by linarith) hab))

/-! ### 2. The gap and the width are independent parameters -/

/-- **Any prescribed gap at a bounded aperture coexists with the maximal width.** The background
lattice spacing fixes the gap and the inserted pair fixes the width. -/
theorem exists_width_eq_half_apertureGain {a : ℝ} (ha : 0 < a) (η : ℝ) :
    ∃ Z : TemperedZeroConfig, width Z = 1 / 2 ∧ apertureGain a η Z := by
  set L : ℝ := 2 * a + |pairEnergy (1 / 2) a| + |η| + 1 with hLdef
  have hL : 0 < L := by
    have := abs_nonneg (pairEnergy (1 / 2) a)
    have := abs_nonneg η
    simp only [hLdef]; linarith
  have haL : a ≤ L / 2 := by
    have := abs_nonneg (pairEnergy (1 / 2) a)
    have := abs_nonneg η
    simp only [hLdef]; linarith
  have hgap : η ≤ 2 * (L - pairEnergy (1 / 2) a) := by
    have h1 : pairEnergy (1 / 2) a ≤ |pairEnergy (1 / 2) a| := le_abs_self _
    have h2 : η ≤ |η| := le_abs_self _
    have h3 : (0 : ℝ) ≤ |η| := abs_nonneg _
    have h4 : (0 : ℝ) ≤ |pairEnergy (1 / 2) a| := abs_nonneg _
    simp only [hLdef]; linarith
  refine ⟨latticeWithPairAt hL (by norm_num : (0 : ℝ) < 1 / 2) le_rfl 0,
    le_antisymm (width_le_half _)
      (depth_le_width_latticeWithPairAt hL (by norm_num) le_rfl 0), fun f hf hfs => ?_⟩
  have hbase := re_W_isolatedPairConfig_ge hL (by norm_num : (0 : ℝ) < 1 / 2) le_rfl 0
    ha.le haL hf hfs
  have hint : (0 : ℝ) ≤ ∫ t, ‖f t‖ ^ 2 := MeasureTheory.integral_nonneg fun _ => by positivity
  exact le_trans (mul_le_mul_of_nonneg_right hgap hint) hbase

/-! ### 3. Every level has the trivial limit -/

/-- **The resolution limit of the width is `½` at every aperture and every gap.** A coercivity
constant, however large, certifies nothing about the width. -/
theorem resolutionLimit_width_apertureGain {a η : ℝ} (ha : 0 < a) {Z : TemperedZeroConfig}
    (hZ : apertureGain a η Z) : resolutionLimit width (apertureGain a η) Z = 1 / 2 := by
  obtain ⟨Z', hw', hpos'⟩ := exists_width_eq_half_apertureGain ha η
  refine le_antisymm (csSup_le (shadow_image_nonempty width (apertureGain a η) Z) ?_) ?_
  · rintro x ⟨W, -, rfl⟩
    exact width_le_half W
  · have hmem : Z' ∈ shadow (apertureGain a η) Z := propext (iff_of_true hpos' hZ)
    exact hw' ▸ le_csSup (bddAbove_width_image _) ⟨Z', hmem, rfl⟩

/-- A coercive finite-aperture certificate certifies the bound `β` on the width exactly when
`β ≥ ½`, at every level. -/
theorem certifies_width_apertureGain_iff {a η : ℝ} (ha : 0 < a) {Z : TemperedZeroConfig}
    (hZ : apertureGain a η Z) {β : ℝ} :
    Certifies width (apertureGain a η) Z β ↔ 1 / 2 ≤ β := by
  rw [certifies_iff_resolutionLimit_le (bddAbove_width_image _),
    resolutionLimit_width_apertureGain ha hZ]

/-- **No coercive finite-aperture certificate decides the critical line.** -/
theorem not_resolves_onLine_apertureGain {a η : ℝ} (ha : 0 < a) {Z : TemperedZeroConfig}
    (hZ : apertureGain a η Z) (hw : width Z = 0) :
    ¬ Resolves (apertureGain a η) (fun W => width W = 0) := by
  obtain ⟨Z', hw', hpos'⟩ := exists_width_eq_half_apertureGain ha η
  intro hres
  have h0 : width Z' = 0 := (hres Z Z' (propext (iff_of_true hpos' hZ))).mpr hw
  rw [hw'] at h0
  norm_num at h0

/-- **The gap ladder.** At a fixed bounded aperture the certificates are ordered by their gap, and
every stage of that chain has resolution limit `½` for the width: strengthening the constant gains
information, and none of it is the width. -/
theorem gainLadderIsTrivial {a : ℝ} (ha : 0 < a) :
    ∀ η : ℝ, ∃ Z : TemperedZeroConfig, width Z = 1 / 2 ∧ apertureGain a η Z ∧
      resolutionLimit width (apertureGain a η) Z = 1 / 2 := fun η => by
  obtain ⟨Z, hw, hZ⟩ := exists_width_eq_half_apertureGain ha η
  exact ⟨Z, hw, hZ, resolutionLimit_width_apertureGain ha hZ⟩

-- from NoChangeOfDepthUnitEscapesTheFloor.lean
variable {g : ℝ → ℝ}

/-! ### 1. Boundedness in an arbitrary monotone unit -/

theorem bddAbove_comp_width_image (hg : MonotoneOn g (Icc 0 (1 / 2)))
    (s : Set TemperedZeroConfig) : BddAbove ((g ∘ width) '' s) := by
  refine ⟨g (1 / 2), ?_⟩
  rintro x ⟨Z, -, rfl⟩
  exact hg ⟨width_nonneg Z, width_le_half Z⟩ ⟨by norm_num, le_rfl⟩ (width_le_half Z)

theorem bddBelow_comp_width_image (hg : MonotoneOn g (Icc 0 (1 / 2)))
    (s : Set TemperedZeroConfig) : BddBelow ((g ∘ width) '' s) := by
  refine ⟨g 0, ?_⟩
  rintro x ⟨Z, -, rfl⟩
  exact hg ⟨le_rfl, by norm_num⟩ ⟨width_nonneg Z, width_le_half Z⟩ (width_nonneg Z)

/-! ### 2. The limit in an arbitrary monotone unit -/

/-- **Every monotone depth unit has the trivial limit.** At every aperture and every coercivity
level, a certificate reads `g ∘ width` only up to `g(½)`. -/
theorem resolutionLimit_comp_width_apertureGain (hg : MonotoneOn g (Icc 0 (1 / 2))) {a η : ℝ}
    (ha : 0 < a) {Z : TemperedZeroConfig} (hZ : apertureGain a η Z) :
    resolutionLimit (g ∘ width) (apertureGain a η) Z = g (1 / 2) := by
  obtain ⟨Z', hw', hpos'⟩ := exists_width_eq_half_apertureGain ha η
  refine le_antisymm (csSup_le (shadow_image_nonempty (g ∘ width) (apertureGain a η) Z) ?_) ?_
  · rintro x ⟨W, -, rfl⟩
    exact hg ⟨width_nonneg W, width_le_half W⟩ ⟨by norm_num, le_rfl⟩ (width_le_half W)
  · have hmem : Z' ∈ shadow (apertureGain a η) Z := propext (iff_of_true hpos' hZ)
    calc g (1 / 2) = (g ∘ width) Z' := by simp [Function.comp, hw']
      _ ≤ resolutionLimit (g ∘ width) (apertureGain a η) Z :=
          le_csSup (bddAbove_comp_width_image hg _) ⟨Z', hmem, rfl⟩

/-- The same for bare positivity, the level-`0` case. -/
theorem resolutionLimit_comp_width_aperturePositivity (hg : MonotoneOn g (Icc 0 (1 / 2)))
    {a : ℝ} (ha : 0 < a) {Z : TemperedZeroConfig} (hZ : aperturePositivity a Z) :
    resolutionLimit (g ∘ width) (aperturePositivity a) Z = g (1 / 2) := by
  obtain ⟨Z', hw', hpos'⟩ := exists_width_eq_half_aperturePositivity ha
  refine le_antisymm (csSup_le (shadow_image_nonempty (g ∘ width) (aperturePositivity a) Z) ?_) ?_
  · rintro x ⟨W, -, rfl⟩
    exact hg ⟨width_nonneg W, width_le_half W⟩ ⟨by norm_num, le_rfl⟩ (width_le_half W)
  · have hmem : Z' ∈ shadow (aperturePositivity a) Z := propext (iff_of_true hpos' hZ)
    calc g (1 / 2) = (g ∘ width) Z' := by simp [Function.comp, hw']
      _ ≤ resolutionLimit (g ∘ width) (aperturePositivity a) Z :=
          le_csSup (bddAbove_comp_width_image hg _) ⟨Z', hmem, rfl⟩

/-! ### 3. The floor in an arbitrary monotone unit -/

/-- **And the floor is the other endpoint.** The on-line lattice shares every aperture
certificate, so the reading never bounds `g ∘ width` above `g(0)`. -/
theorem resolutionFloor_comp_width_aperturePositivity (hg : MonotoneOn g (Icc 0 (1 / 2)))
    {a : ℝ} {Z : TemperedZeroConfig} (hZ : aperturePositivity a Z) :
    resolutionFloor (g ∘ width) (aperturePositivity a) Z = g 0 := by
  refine le_antisymm ?_
    ((certifiesLower_iff_le_resolutionFloor (bddBelow_comp_width_image hg _)).mp fun W _ =>
      hg ⟨le_rfl, by norm_num⟩ ⟨width_nonneg W, width_le_half W⟩ (width_nonneg W))
  calc resolutionFloor (g ∘ width) (aperturePositivity a) Z
      ≤ (g ∘ width) (onLineLattice (by norm_num : (0 : ℝ) < 1)) :=
        csInf_le (bddBelow_comp_width_image hg _)
          ⟨_, onLineLattice_mem_shadow_aperturePositivity hZ, rfl⟩
    _ = g 0 := by simp [Function.comp, width_onLineLattice]

/-- **The interval in an arbitrary monotone unit.** -/
theorem resolutionInterval_comp_width_aperturePositivity (hg : MonotoneOn g (Icc 0 (1 / 2)))
    {a : ℝ} (ha : 0 < a) {Z : TemperedZeroConfig} (hZ : aperturePositivity a Z) :
    resolutionInterval (g ∘ width) (aperturePositivity a) Z = Icc (g 0) (g (1 / 2)) := by
  rw [resolutionInterval, resolutionFloor_comp_width_aperturePositivity hg hZ,
    resolutionLimit_comp_width_aperturePositivity hg ha hZ]

/-! ### 4. Unit independence -/

/-- **The floor is unit independent.** In any strictly monotone depth unit the interval left open
by a finite-aperture certificate is still a nondegenerate interval reaching both ends of the
possible range: no reparametrisation of the depth turns the certificate into a bound. -/
theorem theFloorIsUnitIndependent {a : ℝ} (ha : 0 < a) {Z : TemperedZeroConfig}
    (hZ : aperturePositivity a Z) (hg : StrictMonoOn g (Icc 0 (1 / 2))) :
    resolutionInterval (g ∘ width) (aperturePositivity a) Z = Icc (g 0) (g (1 / 2)) ∧
      g 0 < g (1 / 2) :=
  ⟨resolutionInterval_comp_width_aperturePositivity hg.monotoneOn ha hZ,
    hg ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩ (by norm_num)⟩

-- from NoFamilyOfConfigurationsHelps.lean
/-! ### 1. Families and their worst width -/

/-- A family of configurations, of any cardinality. -/
def FamilyConfig (ι : Type*) : Type _ := ι → TemperedZeroConfig

/-- The worst width in the family. -/
noncomputable def familyWidth {ι : Type*} (Z : FamilyConfig ι) : ℝ :=
  sSup (Set.range fun i => width (Z i))

theorem familyWidth_le_half {ι : Type*} (Z : FamilyConfig ι) : familyWidth Z ≤ 1 / 2 := by
  refine Real.sSup_le ?_ (by norm_num)
  rintro x ⟨i, rfl⟩
  exact width_le_half (Z i)

/-- The joint certificate: the aperture-`a` certificate of every member. -/
def familyAperture {ι : Type*} (a : ℝ) (Z : FamilyConfig ι) : Prop :=
  ∀ i : ι, aperturePositivity a (Z i)

/-! ### 2. The constant extremal family -/

/-- The family all of whose members are the depth-`½` witness. -/
theorem exists_familyWidth_eq_half {ι : Type*} [Nonempty ι] {a : ℝ} (ha : 0 < a) :
    ∃ Z : FamilyConfig ι, familyWidth Z = 1 / 2 ∧ familyAperture a Z := by
  obtain ⟨W, hw, hpos⟩ := exists_width_eq_half_aperturePositivity ha
  refine ⟨fun _ => W, ?_, fun _ => hpos⟩
  have hrange : (Set.range fun _ : ι => width W) = {width W} := by
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · intro hx
      obtain ⟨-, h⟩ := hx
      exact h.symm
    · intro h
      exact ⟨Classical.arbitrary ι, h.symm⟩
  unfold familyWidth
  rw [hrange, csSup_singleton, hw]

/-! ### 3. The floor -/

/-- **No family helps.** The joint certificate over a family of any cardinality has resolution
limit `½` for the worst width. -/
theorem resolutionLimit_familyWidth_familyAperture {ι : Type*} [Nonempty ι] {a : ℝ} (ha : 0 < a)
    {Z : FamilyConfig ι} (hZ : familyAperture a Z) :
    resolutionLimit familyWidth (familyAperture a) Z = 1 / 2 := by
  obtain ⟨W, hw, hpos⟩ := exists_familyWidth_eq_half (ι := ι) ha
  exact resolutionLimit_eq_of_mem_shadow_of_max familyWidth_le_half
    (propext (iff_of_true hpos hZ)) hw

/-- **And the extremal family is constant**, so no averaging over it can do better than its single
member: the worst case and the average coincide there. -/
theorem resolutionLimit_familyWidth_eq_half_of_constant {ι : Type*} [Nonempty ι] {a : ℝ}
    (ha : 0 < a) {Z : FamilyConfig ι} (hZ : familyAperture a Z) :
    ∃ W : TemperedZeroConfig, width W = 1 / 2 ∧ aperturePositivity a W ∧
      familyWidth (fun _ : ι => W) = 1 / 2 ∧
      resolutionLimit familyWidth (familyAperture a) Z = 1 / 2 := by
  obtain ⟨W, hw, hpos⟩ := exists_width_eq_half_aperturePositivity ha
  refine ⟨W, hw, hpos, ?_, resolutionLimit_familyWidth_familyAperture ha hZ⟩
  have hrange : (Set.range fun _ : ι => width W) = {width W} := by
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · intro hx
      obtain ⟨-, h⟩ := hx
      exact h.symm
    · intro h
      exact ⟨Classical.arbitrary ι, h.symm⟩
  unfold familyWidth
  rw [hrange, csSup_singleton, hw]

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
