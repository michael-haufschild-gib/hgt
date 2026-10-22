import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheHorizonSeamIsEmptyToo

/-!
# The two-by-two table of units

The field's central claim is that its bounded readings see one coordinate of a configuration exactly
and the other not at all. In interval form the claim is a two-by-two table, and this module
completes and assembles it.

| reading | in the width unit | in its own scale unit |
| --- | --- | --- |
| aperture `a` certificate | `[0, ½]`, the whole range | `[0, a⁻¹]`, proper |
| divisor truncated at `T` | `[0, ½]`, the whole range | `[0, (1+T)⁻¹]`, proper |

The two width entries are `resolutionInterval_width_aperturePositivity` and
`resolutionInterval_width_heightReading`: the interval is the entire range of the invariant, so
neither reading can prove or disprove anything about the depth. The horizon entry is
`resolutionInterval_horizonFrequency_heightReading`. The missing entry is supplied here:
`resolutionFloor_visibilityFrequency_aperturePositivity` computes the floor of the frequency unit —
it is `0`, because the on-line lattice shares every certificate and never fails — whence
`resolutionInterval_visibilityFrequency_aperturePositivity` gives `[0, a⁻¹]`.

`theTwoByTwoTable` states all four entries at once. The diagonal is the content: a reading is
informative exactly in the unit built from its own parameter, and vacuous in the unit that carries
RH. Every positive result of the programme — the trans-Nyquist level, the uniform deficit, the
aperture–mass seam — works by leaving this table, either by making the aperture unbounded or by
adding data of a third kind.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The missing entry: the frequency floor -/

theorem visibilityFrequency_nonneg (Z : TemperedZeroConfig) : 0 ≤ visibilityFrequency Z := by
  refine Real.sSup_nonneg ?_
  rintro x ⟨b, hb, rfl⟩
  exact (inv_pos.mpr hb.1).le

theorem bddBelow_visibilityFrequency_image (s : Set TemperedZeroConfig) :
    BddBelow (visibilityFrequency '' s) :=
  ⟨0, by rintro x ⟨Z, -, rfl⟩; exact visibilityFrequency_nonneg Z⟩

/-- The on-line lattice never fails, so its frequency is `0`. -/
theorem visibilityFrequency_onLineLattice {L : ℝ} (hL : 0 < L) :
    visibilityFrequency (onLineLattice hL) = 0 := by
  have hE : failureApertures (onLineLattice hL) = ∅ :=
    (failureApertures_eq_empty_iff_width_eq_zero _).mpr (width_onLineLattice hL)
  unfold visibilityFrequency
  rw [hE, Set.image_empty, Real.sSup_empty]

/-- **The frequency floor of an aperture certificate is `0`.** -/
theorem resolutionFloor_visibilityFrequency_aperturePositivity {a : ℝ} (_ha : 0 < a)
    {Z : TemperedZeroConfig} (hZ : aperturePositivity a Z) :
    resolutionFloor visibilityFrequency (aperturePositivity a) Z = 0 := by
  have hbdd : BddBelow (visibilityFrequency '' shadow (aperturePositivity a) Z) := by
    refine ⟨0, ?_⟩
    rintro x ⟨W, -, rfl⟩
    exact visibilityFrequency_nonneg W
  refine le_antisymm ?_
    ((certifiesLower_iff_le_resolutionFloor hbdd).mp fun W _ => visibilityFrequency_nonneg W)
  have hle := csInf_le hbdd ⟨_, onLineLattice_mem_shadow_aperturePositivity hZ, rfl⟩
  rwa [visibilityFrequency_onLineLattice] at hle

/-- **The certificate is informative in the frequency unit.** -/
theorem resolutionInterval_visibilityFrequency_aperturePositivity {a : ℝ} (ha : 0 < a)
    {Z : TemperedZeroConfig} (hZ : aperturePositivity a Z) :
    resolutionInterval visibilityFrequency (aperturePositivity a) Z = Icc 0 a⁻¹ := by
  rw [resolutionInterval, resolutionFloor_visibilityFrequency_aperturePositivity ha hZ,
    resolutionLimit_visibilityFrequency_aperturePositivity ha hZ]

/-! ### 2. The table -/

/-- **The two-by-two table.** Each bounded reading is vacuous in the width unit — its interval is
the whole range — and informative in the unit built from its own parameter. -/
theorem theTwoByTwoTable {L a T : ℝ} (hL : 0 < L) (ha : 0 < a) (hT : 0 ≤ T)
    {Z : TemperedZeroConfig} (hZ : aperturePositivity a Z) :
    resolutionInterval width (aperturePositivity a) Z = range width ∧
      resolutionInterval visibilityFrequency (aperturePositivity a) Z = Icc 0 a⁻¹ ∧
      resolutionInterval width (heightReading T) (onLineLattice hL) = range width ∧
      resolutionInterval horizonFrequency (heightReading T) (onLineLattice hL) =
        Icc 0 ((1 + T)⁻¹) :=
  ⟨resolutionInterval_width_aperturePositivity ha hZ,
    resolutionInterval_visibilityFrequency_aperturePositivity ha hZ,
    resolutionInterval_width_heightReading hL T,
    resolutionInterval_horizonFrequency_heightReading hL hT⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
