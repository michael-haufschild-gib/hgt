import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheResolutionIntervalIsTheWholeRange

/-!
# A finite-aperture certificate reads the scale, never the depth

Every statement of this programme so far says what a bounded-aperture certificate *cannot* do. It
can do something, and this module says exactly what.

A tempered configuration has a **visibility frequency**: the supremum of `a⁻¹` over the apertures
`a` at which its Weil form already fails to be nonnegative (`visibilityFrequency`). It is `0`
exactly when the configuration never fails — the reciprocal-aperture unit, in which "the
information is at infinity" becomes "the critical line is the origin". For the off-line lattice of
spacing `2π/L` the frequency is `2/L` at every depth
(`visibilityFrequency_offLineLattice`): it is a function of the lattice *scale* alone.

* `resolutionLimit_visibilityFrequency_aperturePositivity` — the aperture-`a` certificate has
  resolution limit exactly `a⁻¹` for the frequency, and the limit is **attained**, by the lattice
  whose Nyquist aperture is exactly `a`. So the certificate is sharp in this unit: it proves
  `visibilityFrequency ≤ a⁻¹` and that bound is the truth for one of the data it admits.
* `exists_mem_shadow_visibilityFrequency_eq_and_width_eq` — and inside that one value of the
  frequency the shadow still carries **every** depth `δ ∈ (0, ½]`.

Hence the **scale–depth separation**
(`aperturePositivity_reads_scale_not_depth`): a finite-aperture positivity certificate is faithful
for the scale coordinate of a configuration and completely blind to its depth coordinate. The
width is a depth; that is why every bounded-aperture limit is the trivial `½`, and it is also why
the reading is not worthless — it measures the one coordinate it can see, exactly.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The visibility frequency -/

/-- The apertures at which the configuration's Weil form already fails. -/
def failureApertures (Z : TemperedZeroConfig) : Set ℝ :=
  {a : ℝ | 0 < a ∧ ¬ aperturePositivity a Z}

/-- The **visibility frequency**: the largest reciprocal aperture at which `Z` fails. It is `0`
for a configuration that is positive at every aperture, and large for one that fails early. -/
noncomputable def visibilityFrequency (Z : TemperedZeroConfig) : ℝ :=
  sSup ((fun a : ℝ => a⁻¹) '' failureApertures Z)

/-- A certificate at aperture `a` caps the frequency at `a⁻¹`: failure can only happen later. -/
theorem visibilityFrequency_le_inv {a : ℝ} (ha : 0 < a) {Z : TemperedZeroConfig}
    (hZ : aperturePositivity a Z) : visibilityFrequency Z ≤ a⁻¹ := by
  refine Real.sSup_le ?_ (by positivity)
  rintro x ⟨b, ⟨hb, hbf⟩, rfl⟩
  have hab : a < b := by
    by_contra h
    exact hbf (aperturePositivity_mono (not_lt.mp h) hZ)
  exact le_of_lt ((inv_lt_inv₀ hb ha).mpr hab)

/-! ### 2. The frequency of a lattice is its scale -/

/-- Positivity of the off-line lattice at aperture `a` is exactly the Nyquist condition. -/
theorem aperturePositivity_offLineLattice_iff {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (a : ℝ) :
    aperturePositivity a (offLineLattice hL hδ hδ') ↔ a ≤ L / 2 :=
  offLineLattice_weil_positive_iff hL hδ hδ' a

/-- **The frequency of the off-line lattice is `2/L` at every depth.** The reading of a lattice in
this unit is its scale, with no trace of its depth. -/
theorem visibilityFrequency_offLineLattice {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    visibilityFrequency (offLineLattice hL hδ hδ') = 2 / L := by
  have hhalf : (0 : ℝ) < L / 2 := by linarith
  have hinv : (L / 2 : ℝ)⁻¹ = 2 / L := inv_div L 2
  set S := (fun a : ℝ => a⁻¹) '' failureApertures (offLineLattice hL hδ hδ') with hSdef
  have hmemS : ∀ b : ℝ, L / 2 < b → b⁻¹ ∈ S := fun b hb =>
    ⟨b, ⟨by linarith, fun hpos =>
      absurd ((aperturePositivity_offLineLattice_iff hL hδ hδ' b).mp hpos) (not_le.mpr hb)⟩, rfl⟩
  have hub : ∀ x ∈ S, x ≤ 2 / L := by
    rintro x ⟨b, ⟨hb0, hbf⟩, rfl⟩
    have hb : L / 2 < b := by
      by_contra h
      exact hbf ((aperturePositivity_offLineLattice_iff hL hδ hδ' b).mpr (not_lt.mp h))
    rw [← hinv]
    exact le_of_lt ((inv_lt_inv₀ hb0 hhalf).mpr hb)
  have hbdd : BddAbove S := ⟨2 / L, hub⟩
  have hne : S.Nonempty := ⟨L⁻¹, hmemS L (by linarith)⟩
  show sSup S = 2 / L
  refine le_antisymm (Real.sSup_le hub (by positivity)) ?_
  rw [Real.le_sSup_iff hbdd hne]
  intro ε hε
  rcases le_or_gt (2 / L + ε) 0 with ht | ht
  · refine ⟨L⁻¹, hmemS L (by linarith), ?_⟩
    have : (0 : ℝ) < L⁻¹ := by positivity
    linarith
  · have htlt : 2 / L + ε < 2 / L := by linarith
    have hti : L / 2 < (2 / L + ε)⁻¹ := by
      rw [inv_eq_one_div, lt_div_iff₀ ht]
      have hid : L / 2 * (2 / L + ε) = 1 + L / 2 * ε := by field_simp
      rw [hid]
      nlinarith [hhalf, hε]
    set b : ℝ := (L / 2 + (2 / L + ε)⁻¹) / 2 with hbdef
    have hb0 : (0 : ℝ) < b := by simp only [hbdef]; linarith
    have hblt : b < (2 / L + ε)⁻¹ := by simp only [hbdef]; linarith
    refine ⟨b⁻¹, hmemS b (by simp only [hbdef]; linarith), ?_⟩
    have hmul : (2 / L + ε) * b < 1 := by
      calc (2 / L + ε) * b < (2 / L + ε) * (2 / L + ε)⁻¹ :=
            mul_lt_mul_of_pos_left hblt ht
        _ = 1 := mul_inv_cancel₀ (ne_of_gt ht)
    rw [inv_eq_one_div, lt_div_iff₀ hb0]
    linarith

/-! ### 3. The limit in the frequency unit is sharp and attained -/

/-- **The certificate is faithful for the scale.** At aperture `a` the resolution limit of the
visibility frequency is exactly `a⁻¹`, attained by the lattice whose Nyquist aperture is `a`. -/
theorem resolutionLimit_visibilityFrequency_aperturePositivity {a : ℝ} (ha : 0 < a)
    {Z : TemperedZeroConfig} (hZ : aperturePositivity a Z) :
    resolutionLimit visibilityFrequency (aperturePositivity a) Z = a⁻¹ := by
  have hL : (0 : ℝ) < 2 * a := by linarith
  have hδ : (0 : ℝ) < 1 / 2 := by norm_num
  have hbdd : BddAbove (visibilityFrequency '' shadow (aperturePositivity a) Z) := by
    refine ⟨a⁻¹, ?_⟩
    rintro x ⟨W, hW, rfl⟩
    exact visibilityFrequency_le_inv ha
      ((mem_shadow_iff.mp hW) ▸ hZ : aperturePositivity a W)
  refine le_antisymm (Real.sSup_le ?_ (by positivity)) ?_
  · rintro x ⟨W, hW, rfl⟩
    exact visibilityFrequency_le_inv ha ((mem_shadow_iff.mp hW) ▸ hZ : aperturePositivity a W)
  · have hpos : aperturePositivity a (offLineLattice hL hδ le_rfl) :=
      (aperturePositivity_offLineLattice_iff hL hδ le_rfl a).mpr (by linarith)
    have hmem : offLineLattice hL hδ le_rfl ∈ shadow (aperturePositivity a) Z :=
      propext (iff_of_true hpos hZ)
    have hfreq : visibilityFrequency (offLineLattice hL hδ le_rfl) = a⁻¹ := by
      rw [visibilityFrequency_offLineLattice hL hδ le_rfl]
      rw [show (2 : ℝ) / (2 * a) = a⁻¹ by field_simp]
    exact hfreq ▸ le_csSup hbdd ⟨_, hmem, rfl⟩

/-! ### 4. The depth stays free inside one value of the scale -/

/-- **Every depth survives at the extremal scale.** For each `δ ∈ (0, ½]` the shadow contains a
configuration of width `δ` whose frequency is the extremal value `a⁻¹`. -/
theorem exists_mem_shadow_visibilityFrequency_eq_and_width_eq {a : ℝ} (ha : 0 < a)
    {Z : TemperedZeroConfig} (hZ : aperturePositivity a Z) {δ : ℝ} (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) :
    ∃ W ∈ shadow (aperturePositivity a) Z,
      visibilityFrequency W = a⁻¹ ∧ width W = δ := by
  have hL : (0 : ℝ) < 2 * a := by linarith
  refine ⟨offLineLattice hL hδ hδ', propext (iff_of_true
    ((aperturePositivity_offLineLattice_iff hL hδ hδ' a).mpr (by linarith)) hZ), ?_, ?_⟩
  · rw [visibilityFrequency_offLineLattice hL hδ hδ',
      show (2 : ℝ) / (2 * a) = a⁻¹ by field_simp]
  · exact width_offLineLattice hL hδ hδ'

/-- **Scale–depth separation.** The aperture-`a` certificate determines the visibility frequency
sharply (`limit = a⁻¹`, attained) and determines nothing at all about the depth (`limit = ½` for
the width, with every depth realised at the extremal frequency). The two coordinates of a
configuration are read completely differently by one and the same certificate. -/
theorem aperturePositivity_reads_scale_not_depth {a : ℝ} (ha : 0 < a)
    {Z : TemperedZeroConfig} (hZ : aperturePositivity a Z) :
    resolutionLimit visibilityFrequency (aperturePositivity a) Z = a⁻¹ ∧
      resolutionLimit width (aperturePositivity a) Z = 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ∃ W ∈ shadow (aperturePositivity a) Z,
        visibilityFrequency W = a⁻¹ ∧ width W = δ :=
  ⟨resolutionLimit_visibilityFrequency_aperturePositivity ha hZ,
    resolutionLimit_width_aperturePositivity ha hZ,
    fun _ hδ hδ' => exists_mem_shadow_visibilityFrequency_eq_and_width_eq ha hZ hδ hδ'⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
