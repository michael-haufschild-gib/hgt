import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheApertureLadderIsStrictYetEveryStageIsTrivial

/-!
# The resolution interval, and its exact value for the bounded zero-side readings

A resolution limit bounds an invariant from above, a resolution floor from below. Together they
delimit the exact set of values a method reading `r` leaves open: the **resolution interval**
`[resolutionFloor I r d, resolutionLimit I r d]`. A reading is informative for `I` at `d` precisely
when this interval is proper, and it pins `I` precisely when the interval degenerates
(`resolutionFloor_eq_resolutionLimit_iff`).

The upper end of the interval was known for the bounded zero-side readings: `½` at every bounded
aperture and at every bounded height. The lower end is computed here, and it is `0`:

* `resolutionFloor_width_aperturePositivity`, `resolutionFloor_width_familyPositivity` — the
  on-line lattice is Weil-positive at every aperture, hence lies in every aperture shadow, hence
  the floor is `0` at **every** configuration the certificate admits;
* `range_width` — the width takes exactly the values `[0, ½]` on tempered configurations;
* `resolutionInterval_width_aperturePositivity`, `resolutionInterval_width_familyPositivity`,
  `resolutionInterval_width_heightReading` — the interval is therefore the *entire* range of the
  invariant.

The consequence is the two-sided form of the trans-Nyquist wall, which the one-sided floors do not
give: a finite-aperture certificate, or a divisor truncated at a finite height, can neither bound
the width below `½` nor bound it above `0`. Such a reading can neither prove nor disprove the
critical line. It is a complete vacuity statement, not a weak bound.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

variable {D O O' : Type*} {I : D → ℝ}

/-! ### 1. The interval of a reading -/

/-- The **resolution interval**: the exact set of values of `I` a method reading `r` leaves open
at `d`. -/
noncomputable def resolutionInterval (I : D → ℝ) (r : D → O) (d : D) : Set ℝ :=
  Icc (resolutionFloor I r d) (resolutionLimit I r d)

theorem mem_resolutionInterval {r : D → O} {d : D} (hb : BddBelow (I '' shadow r d))
    (ha : BddAbove (I '' shadow r d)) : I d ∈ resolutionInterval I r d :=
  ⟨resolutionFloor_le hb, le_resolutionLimit ha⟩

/-- Refinement shrinks the interval from both ends: more data, fewer open values. -/
theorem resolutionInterval_subset_of_refines {r : D → O} {r' : D → O'} (h : Refines r r')
    {d : D} (hb : BddBelow (I '' shadow r' d)) (ha : BddAbove (I '' shadow r' d)) :
    resolutionInterval I r d ⊆ resolutionInterval I r' d :=
  Icc_subset_Icc
    (csInf_le_csInf hb (shadow_image_nonempty I r d) (Set.image_mono (shadow_subset_of_refines h d)))
    (resolutionLimit_le_of_refines h ha)

/-- **Degeneracy criterion.** The interval collapses to a point exactly when the reading pins the
invariant on its whole shadow. -/
theorem resolutionFloor_eq_resolutionLimit_iff {r : D → O} {d : D}
    (hb : BddBelow (I '' shadow r d)) (ha : BddAbove (I '' shadow r d)) :
    resolutionFloor I r d = resolutionLimit I r d ↔ ∀ e ∈ shadow r d, I e = I d := by
  refine ⟨fun h e he => ?_, fun h => ?_⟩
  · have h1 : resolutionFloor I r d ≤ I e := csInf_le hb ⟨e, he, rfl⟩
    have h2 : I e ≤ resolutionLimit I r d := le_csSup ha ⟨e, he, rfl⟩
    have h3 : resolutionFloor I r d ≤ I d := resolutionFloor_le hb
    have h4 : I d ≤ resolutionLimit I r d := le_resolutionLimit ha
    rw [h] at h1 h3
    linarith
  · have hfl : resolutionFloor I r d = I d :=
      le_antisymm (resolutionFloor_le hb)
        ((certifiesLower_iff_le_resolutionFloor hb).mp fun e he => (h e he).ge)
    have hli : resolutionLimit I r d = I d :=
      le_antisymm ((certifies_iff_resolutionLimit_le ha).mp fun e he => (h e he).le)
        (le_resolutionLimit ha)
    rw [hfl, hli]

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

/-- **Two-sided vacuity of a finite-height divisor.** -/
theorem resolutionInterval_width_heightReading {L : ℝ} (hL : 0 < L) (T : ℝ) :
    resolutionInterval width (heightReading T) (onLineLattice hL) = range width := by
  have hfl : resolutionFloor width (heightReading T) (onLineLattice hL) = 0 := by
    refine le_antisymm ?_ ((certifiesLower_iff_le_resolutionFloor (bddBelow_width_image _)).mp
      fun e _ => width_nonneg e)
    have h := resolutionFloor_le (I := width) (r := heightReading T)
      (d := onLineLattice hL) (bddBelow_width_image _)
    rwa [width_onLineLattice hL] at h
  rw [resolutionInterval, hfl, resolutionLimit_width_heightReading hL T, range_width]

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
