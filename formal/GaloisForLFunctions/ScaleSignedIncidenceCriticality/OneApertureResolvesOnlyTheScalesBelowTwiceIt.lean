import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheSquareRootPrecisionLawOfDepthResolution

/-!
# One aperture resolves only the scales below twice it

The depth resolution `min ½ (depthResolution L η)` of a level-`η` certificate was computed on
apertures `a` just above the Nyquist aperture `L/2` of the configuration. Below that aperture the
same certificate is worth nothing at all, and the transition is a discontinuity:

* `resolutionLimit_depth_levelReading_of_subNyquist` — for `a ≤ L/2` and any level `η ≥ 0` the
  certificate holds for **every** depth (`levelReading_of_le_half`, because the lattice is
  Weil-positive there), so its shadow is the whole family and the resolution limit of the depth is
  the trivial `½`;
* `resolutionLimit_depth_levelReading_lt_half` — for `L/2 < a ≤ L` and any level below the
  depth-`½` threshold the limit is strictly below `½`.

`theNyquistTransitionIsADiscontinuity` states both at once. The consequence is a dictionary between
the aperture of a method and the scales it can address: a certificate of aperture `a` says nothing
about any configuration whose scale satisfies `L ≥ 2a`, whatever its level. Since the zero
configuration of `ζ` has a scale that varies with the height, no single aperture addresses all of
it: a mechanism must carry a family of apertures growing with the scale it wants to reach. This is
the "every scale, not almost every" criterion in the level unit, and it explains why the aperture
ladder of the programme has to be unbounded — not because the width is subtle, but because each
stage of it is blind to all scales above its own.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. Below the Nyquist aperture every depth passes -/

/-- **Sub-Nyquist certificates are automatic.** At an aperture below `L/2` the lattice is
Weil-positive at every depth, so it has a floor at every nonnegative level. -/
theorem levelReading_of_le_half {L a η : ℝ} (hL : 0 < L) (ha : a ≤ L / 2) (hη : 0 ≤ η)
    (d : DepthDatum) : levelReading hL a η d := by
  intro f hf hfs _ _
  have hpos : 0 ≤ ((offLineLatticeConfig hL d.2.1 d.2.2).W f f).re :=
    (offLineLattice_weil_positive_iff hL d.2.1 d.2.2 a).mpr ha f hf hfs
  have hint : (0 : ℝ) ≤ ∫ u, ‖f u‖ ^ 2 :=
    MeasureTheory.integral_nonneg fun _ => by positivity
  nlinarith

/-- **Total blindness below the Nyquist aperture.** The shadow is the whole depth family, so the
resolution limit of the depth is the trivial `½`. -/
theorem resolutionLimit_depth_levelReading_of_subNyquist {L a η : ℝ} (hL : 0 < L)
    (ha : a ≤ L / 2) (hη : 0 ≤ η) (d₀ : DepthDatum) :
    resolutionLimit depth (levelReading hL a η) d₀ = 1 / 2 := by
  have hbdd : BddAbove (depth '' shadow (levelReading hL a η) d₀) :=
    ⟨1 / 2, by rintro x ⟨d, -, rfl⟩; exact d.2.2⟩
  refine le_antisymm (csSup_le (shadow_image_nonempty depth (levelReading hL a η) d₀) ?_) ?_
  · rintro x ⟨d, -, rfl⟩
    exact d.2.2
  · set d₁ : DepthDatum := ⟨1 / 2, by norm_num, le_rfl⟩ with hd₁
    have hmem : d₁ ∈ shadow (levelReading hL a η) d₀ :=
      propext (iff_of_true (levelReading_of_le_half hL ha hη d₁)
        (levelReading_of_le_half hL ha hη d₀))
    exact le_csSup hbdd ⟨d₁, hmem, rfl⟩

/-! ### 2. Above it the limit drops strictly -/

/-- **A strict drop just above the Nyquist aperture.** A level below the depth-`½` threshold
resolves the depth strictly better than the trivial bound. -/
theorem resolutionLimit_depth_levelReading_lt_half {L a η : ℝ} (hL : 0 < L) (ha : L / 2 < a)
    (haL : a ≤ L) (hη : 0 ≤ η) (hsmall : η < weilFloorThreshold L (1 / 2))
    {d₀ : DepthDatum} (hd₀ : levelReading hL a η d₀) :
    resolutionLimit depth (levelReading hL a η) d₀ < 1 / 2 := by
  have hD : depthResolution L η < 1 / 2 := by
    by_contra h
    exact absurd ((weilFloorThreshold_le_iff hL (by norm_num : (0 : ℝ) < 1 / 2) hη).mpr
      (not_lt.mp h)) (not_le.mpr hsmall)
  rw [resolutionLimit_depth_levelReading hL ha haL hη hd₀]
  exact lt_of_le_of_lt (min_le_right _ _) hD

/-! ### 3. The transition -/

/-- **The Nyquist transition is a discontinuity in the resolution limit.** One and the same level
certificate is worth the trivial bound at every aperture below `L/2` and strictly better than it
just above, so the aperture a method uses fixes the scales it can address: nothing with
`L ≥ 2a`. -/
theorem theNyquistTransitionIsADiscontinuity {L η : ℝ} (hL : 0 < L) (hη : 0 ≤ η)
    (hsmall : η < weilFloorThreshold L (1 / 2)) (d₀ : DepthDatum) :
    (∀ a : ℝ, a ≤ L / 2 → resolutionLimit depth (levelReading hL a η) d₀ = 1 / 2) ∧
      ∀ a : ℝ, L / 2 < a → a ≤ L → levelReading hL a η d₀ →
        resolutionLimit depth (levelReading hL a η) d₀ < 1 / 2 :=
  ⟨fun _ ha => resolutionLimit_depth_levelReading_of_subNyquist hL ha hη d₀,
    fun _ ha haL hd₀ => resolutionLimit_depth_levelReading_lt_half hL ha haL hη hsmall hd₀⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
