import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheTwoFacesReadOneScaleDatum
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheHeightApertureSeamIsEmpty

/-!
# The height face has a unit, and it is the first off-line horizon

The bounded-height reading had only the trivial entry: resolution limit `½` for the width. That is
the wrong unit for it. What a truncated divisor actually controls is not how deep the off-line
zeros are but how *low* they can be, and in that unit the reading is sharp.

The **horizon frequency** of a configuration is
`horizonFrequency Z = sup {(1 + |γ|)⁻¹ : ½ + iγ-ish off-line zero of Z}`, a number in `[0, 1]`
which vanishes exactly on the critical line (`horizonFrequency_eq_zero_iff`). Then:

* `horizonFrequency_le_of_mem_shadow` — every configuration sharing the divisor of the on-line
  lattice up to height `T` has horizon frequency at most `(1 + T)⁻¹`: a truncated divisor really
  does certify that no off-line zero sits below its own height;
* `resolutionLimit_horizonFrequency_heightReading` — and `(1 + T)⁻¹` is exactly the limit, the
  witnesses being the inserted pairs just above `T`;
* `riemannHypothesis_iff_horizonFrequency_zetaConfig_eq_zero` — on `ζ` the vanishing of the unit is
  RH, so the height ladder converges to the criterion as `T → ∞`, each stage sharply.

So the height face joins the aperture and prime faces: a bounded reading is *faithful* for the
coordinate it was built to see — here the horizon — and trivial for the depth. The programme's
`½` entries record the blind coordinate; this records the seeing one, and
`theHeightFaceSeesTheHorizonNotTheDepth` states both together.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The horizon unit -/

/-- The heights at which the configuration has an off-line zero. -/
def offLineHeights (Z : TemperedZeroConfig) : Set ℝ :=
  {h : ℝ | ∃ ρ ∈ Z.1.carrier, ρ.re ≠ 1 / 2 ∧ h = |ρ.im|}

/-- The **horizon frequency**: the reciprocal of the lowest off-line height, read in the bounded
unit `(1 + h)⁻¹`. It is `0` when there is no off-line zero and close to `1` when one sits low. -/
noncomputable def horizonFrequency (Z : TemperedZeroConfig) : ℝ :=
  sSup ((fun h : ℝ => (1 + h)⁻¹) '' offLineHeights Z)

theorem bddAbove_horizonFrequency_image (Z : TemperedZeroConfig) :
    BddAbove ((fun h : ℝ => (1 + h)⁻¹) '' offLineHeights Z) := by
  refine ⟨1, ?_⟩
  rintro x ⟨h, ⟨ρ, -, -, rfl⟩, rfl⟩
  rw [inv_le_one_iff₀]
  exact Or.inr (by linarith [abs_nonneg ρ.im])

/-- With no off-line zero the unit is `0`. -/
theorem horizonFrequency_of_empty {Z : TemperedZeroConfig} (h : offLineHeights Z = ∅) :
    horizonFrequency Z = 0 := by
  simp only [horizonFrequency, h, Set.image_empty, Real.sSup_empty]

theorem horizonFrequency_nonneg (Z : TemperedZeroConfig) : 0 ≤ horizonFrequency Z := by
  rcases Set.eq_empty_or_nonempty (offLineHeights Z) with hE | ⟨h, hh⟩
  · rw [horizonFrequency_of_empty hE]
  · have hh0 : 0 ≤ h := by
      obtain ⟨ρ, -, -, rfl⟩ := hh
      exact abs_nonneg _
    have hpos : (0 : ℝ) < (1 + h)⁻¹ := inv_pos.mpr (by linarith)
    exact hpos.le.trans (le_csSup (bddAbove_horizonFrequency_image Z) ⟨h, hh, rfl⟩)

/-- **The unit vanishes exactly on the critical line.** -/
theorem horizonFrequency_eq_zero_iff (Z : TemperedZeroConfig) :
    horizonFrequency Z = 0 ↔ width Z = 0 := by
  constructor
  · intro h
    refine configWidth_eq_zero_iff_onLine.mpr fun ρ hρ => ?_
    by_contra hre
    have hmem : |ρ.im| ∈ offLineHeights Z := ⟨ρ, hρ, hre, rfl⟩
    have hle : (1 + |ρ.im|)⁻¹ ≤ horizonFrequency Z :=
      le_csSup (bddAbove_horizonFrequency_image Z) ⟨_, hmem, rfl⟩
    rw [h] at hle
    exact absurd hle (not_le.mpr (by positivity))
  · intro hw
    have hon : ∀ ρ ∈ Z.1.carrier, ρ.re = 1 / 2 := configWidth_eq_zero_iff_onLine.mp hw
    refine horizonFrequency_of_empty (Set.eq_empty_iff_forall_notMem.mpr fun h hmem => ?_)
    obtain ⟨ρ, hρ, hre, -⟩ := hmem
    exact hre (hon ρ hρ)

/-! ### 2. A truncated divisor certifies its own horizon -/

/-- Members of the height-`T` shadow of the on-line lattice have no off-line zero below `T`. -/
theorem onLine_below_of_mem_shadow {L T : ℝ} (hL : 0 < L) {W : TemperedZeroConfig}
    (hW : W ∈ shadow (heightReading T) (onLineLattice hL)) {ρ : ℂ} (hρ : ρ ∈ W.1.carrier)
    (hT : |ρ.im| ≤ T) : ρ.re = 1 / 2 := by
  by_contra hre
  have hmemW : ρ ∈ heightWindow T W := mem_heightWindow.mpr ⟨hρ, hT⟩
  have hnz : heightReading T W ρ ≠ 0 := by
    rw [heightReading_of_mem hmemW]
    have h1 := W.1.one_le_mult ρ hρ
    omega
  have hzero : heightReading T (onLineLattice hL) ρ = 0 := by
    refine heightReading_of_notMem fun hmem => ?_
    obtain ⟨⟨k, hk⟩, -⟩ := mem_heightWindow.mp hmem
    refine hre ?_
    rw [← hk]
    simp [verticalLatticePoint]
  rw [mem_shadow_iff.mp hW] at hnz
  exact hnz hzero

/-- **The truncated divisor certifies the horizon.** -/
theorem horizonFrequency_le_of_mem_shadow {L T : ℝ} (hL : 0 < L) (hT : 0 ≤ T)
    {W : TemperedZeroConfig} (hW : W ∈ shadow (heightReading T) (onLineLattice hL)) :
    horizonFrequency W ≤ (1 + T)⁻¹ := by
  refine Real.sSup_le ?_ (by positivity)
  rintro x ⟨h, ⟨ρ, hρ, hre, rfl⟩, rfl⟩
  have hgt : T < |ρ.im| := by
    by_contra hle
    exact hre (onLine_below_of_mem_shadow hL hW hρ (not_lt.mp hle))
  exact le_of_lt ((inv_lt_inv₀ (by positivity) (by positivity)).mpr (by linarith))

/-! ### 3. The limit is exactly the reciprocal height -/

/-- The inserted pair is the only off-line zero of the perturbed lattice. -/
theorem offLineHeights_latticeWithPairAt {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (γ₀ : ℝ) : offLineHeights (latticeWithPairAt hL hδ hδ' γ₀) = {|γ₀|} := by
  ext h
  simp only [offLineHeights, mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨ρ, hρ, hre, rfl⟩
    rcases hρ with (⟨k, rfl⟩ | hp) | hp
    · exact absurd (by simp [verticalLatticePoint] : (verticalLatticePoint L 0 k).re = 1 / 2) hre
    · rw [Set.mem_singleton_iff] at hp; subst hp; simp [offLinePoint]
    · rw [Set.mem_singleton_iff] at hp; subst hp; simp [offLinePoint]
  · rintro rfl
    exact ⟨offLinePoint δ γ₀, Or.inl (Or.inr rfl), by
      simp only [offLinePoint]
      intro hc
      exact absurd (by linarith : δ = 0) (ne_of_gt hδ), by simp [offLinePoint]⟩

theorem horizonFrequency_latticeWithPairAt {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (γ₀ : ℝ) : horizonFrequency (latticeWithPairAt hL hδ hδ' γ₀) = (1 + |γ₀|)⁻¹ := by
  unfold horizonFrequency
  rw [offLineHeights_latticeWithPairAt hL hδ hδ' γ₀, Set.image_singleton, csSup_singleton]

/-- **The height face's unit.** At truncation height `T` the resolution limit of the horizon
frequency is exactly `(1 + T)⁻¹`. -/
theorem resolutionLimit_horizonFrequency_heightReading {L T : ℝ} (hL : 0 < L) (hT : 0 ≤ T) :
    resolutionLimit horizonFrequency (heightReading T) (onLineLattice hL) = (1 + T)⁻¹ := by
  have hδ : (0 : ℝ) < 1 / 2 := by norm_num
  set S := horizonFrequency '' shadow (heightReading T) (onLineLattice hL) with hS
  have hub : ∀ x ∈ S, x ≤ (1 + T)⁻¹ := by
    rintro x ⟨W, hW, rfl⟩
    exact horizonFrequency_le_of_mem_shadow hL hT hW
  have hmemS : ∀ γ : ℝ, T < γ → (1 + γ)⁻¹ ∈ S := by
    intro γ hγ
    have hγ0 : 0 ≤ γ := by linarith
    refine ⟨latticeWithPairAt hL hδ le_rfl γ, ?_, ?_⟩
    · exact heightReading_latticeWithPairAt hL hδ le_rfl (by rwa [abs_of_nonneg hγ0])
    · rw [horizonFrequency_latticeWithPairAt hL hδ le_rfl γ, abs_of_nonneg hγ0]
  have hbdd : BddAbove S := ⟨(1 + T)⁻¹, hub⟩
  have hne : S.Nonempty := ⟨(1 + (T + 1))⁻¹, hmemS (T + 1) (by linarith)⟩
  show sSup S = (1 + T)⁻¹
  refine le_antisymm (Real.sSup_le hub (by positivity)) ?_
  rw [Real.le_sSup_iff hbdd hne]
  intro ε hε
  rcases le_or_gt ((1 + T)⁻¹ + ε) 0 with ht | ht
  · refine ⟨(1 + (T + 1))⁻¹, hmemS (T + 1) (by linarith), ?_⟩
    have : (0 : ℝ) < (1 + (T + 1))⁻¹ := by positivity
    linarith
  · have htlt : (1 + T)⁻¹ + ε < (1 + T)⁻¹ := by linarith
    have h1T : (0 : ℝ) < 1 + T := by positivity
    have hinvgt : 1 + T < ((1 + T)⁻¹ + ε)⁻¹ := by
      have h := (inv_lt_inv₀ (inv_pos.mpr h1T) ht).mpr htlt
      rwa [inv_inv] at h
    set γ : ℝ := ((1 + T) + ((1 + T)⁻¹ + ε)⁻¹) / 2 - 1 with hγdef
    have hγT : T < γ := by simp only [hγdef]; linarith
    have hγ1 : 1 + γ < ((1 + T)⁻¹ + ε)⁻¹ := by simp only [hγdef]; linarith
    have hγ0 : (0 : ℝ) < 1 + γ := by linarith
    refine ⟨(1 + γ)⁻¹, hmemS γ hγT, ?_⟩
    have h := (inv_lt_inv₀ (inv_pos.mpr ht) hγ0).mpr hγ1
    rwa [inv_inv] at h

/-! ### 4. On `ζ` the unit is a criterion -/

/-- **RH is the vanishing of the horizon frequency of `ζ`.** -/
theorem riemannHypothesis_iff_horizonFrequency_zetaConfig_eq_zero :
    RiemannHypothesis ↔ horizonFrequency zetaConfig = 0 := by
  rw [horizonFrequency_eq_zero_iff]
  exact riemannHypothesis_iff_configWidth_zetaZeroConfig_eq_zero

/-- **The height face sees the horizon, not the depth.** At every truncation height the reading is
sharp in the horizon unit and trivial in the depth unit, and the horizon unit vanishes exactly on
the critical line. -/
theorem theHeightFaceSeesTheHorizonNotTheDepth {L T : ℝ} (hL : 0 < L) (hT : 0 ≤ T) :
    resolutionLimit horizonFrequency (heightReading T) (onLineLattice hL) = (1 + T)⁻¹ ∧
      resolutionLimit width (heightReading T) (onLineLattice hL) = 1 / 2 ∧
      (RiemannHypothesis ↔ horizonFrequency zetaConfig = 0) :=
  ⟨resolutionLimit_horizonFrequency_heightReading hL hT,
    resolutionLimit_width_heightReading hL T,
    riemannHypothesis_iff_horizonFrequency_zetaConfig_eq_zero⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
