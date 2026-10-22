import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheSquareRootPrecisionLawOfDepthResolution
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheResolutionIntervalIsTheWholeRange

/-!
# The level filtration of the depth interval

The level reading just above the Nyquist aperture is the field's one convergent ladder in the depth
unit. This module gives its two-sided form and shows the stages are nested, so that the ladder is a
genuine filtration and not merely a sequence of unrelated bounds.

* `resolutionFloor_depth_levelReading` — the floor is `0`: arbitrarily shallow data pass every
  level, so the reading never forces a positive depth. The level reading confirms and does not
  refute, the opposite one-sidedness from the height face
  (`RefutationIsFiniteConfirmationIsNot`).
* `resolutionInterval_depth_levelReading` — hence the interval is exactly
  `[0, min ½ (depthResolution L η)]`, proper for every level below the depth-`½` threshold.
* `depthResolution_mono` and `resolutionInterval_depth_levelReading_subset` — the intervals are
  **nested**: sharpening the level shrinks the interval, never moves it. Together with
  `WhichLaddersAreProgressMeasures` the intervals decrease to `{0}`.

So the level ladder behaves as an approximation scheme should: each stage certifies an interval, the
intervals are nested, and their intersection is the criterion. That is exactly what the positivity
ladder cannot do (`TheScaleDatumIsFaithfulOnlyAtTheAnswer`), and it is the precise sense in which
the trans-Nyquist deficit, not the trans-Nyquist sign, is the quantity a mechanism should estimate.
-/

open Set

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The floor is zero -/

theorem bddBelow_depth_image (s : Set DepthDatum) : BddBelow (depth '' s) :=
  ⟨0, by rintro x ⟨d, -, rfl⟩; exact d.2.1.le⟩

/-- **The level reading never forces a positive depth.** -/
theorem resolutionFloor_depth_levelReading {L a η : ℝ} (hL : 0 < L) (ha : L / 2 < a)
    (haL : a ≤ L) (hη : 0 ≤ η) {d₀ : DepthDatum} (hd₀ : levelReading hL a η d₀) :
    resolutionFloor depth (levelReading hL a η) d₀ = 0 := by
  have hD : 0 < depthResolution L η :=
    lt_of_lt_of_le d₀.2.1 ((levelReading_iff hL ha haL hη d₀).mp hd₀)
  refine le_antisymm ?_
    ((certifiesLower_iff_le_resolutionFloor (bddBelow_depth_image _)).mp fun d _ => d.2.1.le)
  by_contra hcon
  push Not at hcon
  set s : ℝ := min (min (1 / 2) (depthResolution L η))
    (resolutionFloor depth (levelReading hL a η) d₀) / 2 with hs
  have hpos : 0 < min (min (1 / 2 : ℝ) (depthResolution L η))
      (resolutionFloor depth (levelReading hL a η) d₀) :=
    lt_min (lt_min (by norm_num) hD) hcon
  have hs0 : 0 < s := by simp only [hs]; linarith
  have hshalf : s ≤ 1 / 2 := by
    have := min_le_left (min (1 / 2 : ℝ) (depthResolution L η))
      (resolutionFloor depth (levelReading hL a η) d₀)
    have h2 := min_le_left (1 / 2 : ℝ) (depthResolution L η)
    simp only [hs]; linarith
  have hsD : s ≤ depthResolution L η := by
    have := min_le_left (min (1 / 2 : ℝ) (depthResolution L η))
      (resolutionFloor depth (levelReading hL a η) d₀)
    have h2 := min_le_right (1 / 2 : ℝ) (depthResolution L η)
    simp only [hs]; linarith
  have hsfl : s < resolutionFloor depth (levelReading hL a η) d₀ := by
    have := min_le_right (min (1 / 2 : ℝ) (depthResolution L η))
      (resolutionFloor depth (levelReading hL a η) d₀)
    simp only [hs]; linarith
  set d₁ : DepthDatum := ⟨s, hs0, hshalf⟩ with hd₁
  have hread : levelReading hL a η d₁ := (levelReading_iff hL ha haL hη d₁).mpr hsD
  have hmem : d₁ ∈ shadow (levelReading hL a η) d₀ := propext (iff_of_true hread hd₀)
  have hle := csInf_le (bddBelow_depth_image (shadow (levelReading hL a η) d₀)) ⟨d₁, hmem, rfl⟩
  exact absurd hle (not_le.mpr hsfl)

/-! ### 2. The interval -/

/-- **The interval of a level.** -/
theorem resolutionInterval_depth_levelReading {L a η : ℝ} (hL : 0 < L) (ha : L / 2 < a)
    (haL : a ≤ L) (hη : 0 ≤ η) {d₀ : DepthDatum} (hd₀ : levelReading hL a η d₀) :
    resolutionInterval depth (levelReading hL a η) d₀ =
      Icc 0 (min (1 / 2) (depthResolution L η)) := by
  rw [resolutionInterval, resolutionFloor_depth_levelReading hL ha haL hη hd₀,
    resolutionLimit_depth_levelReading hL ha haL hη hd₀]

/-! ### 3. The stages are nested -/

/-- The depth resolution is monotone in the level. -/
theorem depthResolution_mono {L η η' : ℝ} (hL : 0 < L) (hη : 0 ≤ η) (hηη' : η ≤ η') :
    depthResolution L η ≤ depthResolution L η' := by
  have h1 : (0 : ℝ) < 1 + η / (2 * L) := by positivity
  have hη' : (0 : ℝ) ≤ η' := hη.trans hηη'
  have h2 : (0 : ℝ) < 1 + η' / (2 * L) := by
    have hq : (0 : ℝ) ≤ η' / (2 * L) := by positivity
    linarith
  have hmono : 1 + η / (2 * L) ≤ 1 + η' / (2 * L) := by
    have hd : η / (2 * L) ≤ η' / (2 * L) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hηη' (by positivity)
    linarith
  have harc : Real.arcosh (1 + η / (2 * L)) ≤ Real.arcosh (1 + η' / (2 * L)) :=
    (Real.arcosh_le_arcosh h1 h2).mpr hmono
  rw [depthResolution, depthResolution, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right harc (by positivity)

/-- **Sharpening the level shrinks the interval.** -/
theorem resolutionInterval_depth_levelReading_subset {L a η η' : ℝ} (hL : 0 < L) (ha : L / 2 < a)
    (haL : a ≤ L) (hη : 0 ≤ η) (hηη' : η ≤ η') {d₀ d₀' : DepthDatum}
    (hd₀ : levelReading hL a η d₀) (hd₀' : levelReading hL a η' d₀') :
    resolutionInterval depth (levelReading hL a η) d₀ ⊆
      resolutionInterval depth (levelReading hL a η') d₀' := by
  rw [resolutionInterval_depth_levelReading hL ha haL hη hd₀,
    resolutionInterval_depth_levelReading hL ha haL (hη.trans hηη') hd₀']
  exact Icc_subset_Icc le_rfl (min_le_min le_rfl (depthResolution_mono hL hη hηη'))

/-- **The level ladder is a filtration.** Each stage certifies a proper interval with floor `0`,
and the stages are nested in the level. -/
theorem theLevelFiltration {L a η η' : ℝ} (hL : 0 < L) (ha : L / 2 < a) (haL : a ≤ L)
    (hη : 0 ≤ η) (hηη' : η ≤ η') {d₀ d₀' : DepthDatum} (hd₀ : levelReading hL a η d₀)
    (hd₀' : levelReading hL a η' d₀') :
    resolutionInterval depth (levelReading hL a η) d₀ =
        Icc 0 (min (1 / 2) (depthResolution L η)) ∧
      resolutionInterval depth (levelReading hL a η) d₀ ⊆
        resolutionInterval depth (levelReading hL a η') d₀' :=
  ⟨resolutionInterval_depth_levelReading hL ha haL hη hd₀,
    resolutionInterval_depth_levelReading_subset hL ha haL hη hηη' hd₀ hd₀'⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
