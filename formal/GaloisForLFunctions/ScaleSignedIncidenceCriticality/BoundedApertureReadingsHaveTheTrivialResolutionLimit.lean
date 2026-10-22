import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheResolutionLimitOfAReading
import GaloisForLFunctions.SquareRootThreshold.TheZeroWidthIsAnUnboundedApertureProperty

/-!
# Bounded-aperture readings have the trivial resolution limit

The datum is a tempered zero configuration, the invariant is its width
`Δ(Z) = sup |Re ρ − ½| ∈ [0, ½]`, and the reading is a positivity certificate: "the Weil form of
`Z` is nonnegative on every `C²` test supported in `[−a, a]`".

* **One aperture.** For every `a > 0` the resolution limit of the width is exactly `½`
  (`resolutionLimit_width_aperturePositivity`): the certificate at aperture `a` is shared by
  configurations of every width, so it certifies no bound at all
  (`certifies_width_aperturePositivity_iff`).
* **Any bounded family.** Taking *all* certificates of a family of apertures bounded by `A`
  intersects the shadows, and the limit is still `½`
  (`resolutionLimit_width_familyPositivity`): no finite stack of certificates, and no bounded
  family of any cardinality, improves the trivial bound.
* **The jump.** The unbounded family — positivity on all compactly supported tests — has
  resolution limit `0` (`resolutionLimit_width_fullPositivity`), and the width-zero property is
  RH (`SquareRootThreshold.riemannHypothesis_iff_configWidth_zetaZeroConfig_eq_zero`). The
  resolution limit therefore jumps from `½` to `0` only in the limit `A → ∞`
  (`apertureResolutionJump`): the whole information of the width sits at infinity, and no
  bounded-aperture reading resolves it (`not_resolves_onLine_familyPositivity`).

The witness is the off-line lattice of ordinate spacing `π/A` and depth `½`
(`SquareRootThreshold.exists_configWidth_eq_and_weil_nonneg_on_aperture`): below the Nyquist
aperture it *is*, for every test the aperture admits, a positive on-line configuration.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23

set_option autoImplicit false

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

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
