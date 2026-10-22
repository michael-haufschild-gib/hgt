import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheSquareRootPrecisionLawOfDepthResolution
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheFloorTheorem

/-!
# The sign is uninformative at every aperture

The trans-Nyquist jump is usually read as a jump in information: below the Nyquist aperture the
certificate holds, above it fails, and the failure is what detects the depth. On the depth family at
a fixed scale that reading is wrong, and this module says why.

The sign of the Weil form at aperture `a` is **constant in the depth** on both sides of the Nyquist
aperture: positive for every depth when `a ≤ L/2` (`apertureSign_of_le_half`) and negative for every
depth when `a > L/2` (`not_apertureSign_of_half_lt`), because the lattice positivity law
`SquareRootThreshold.offLineLattice_weil_positive_iff` is the condition `a ≤ L/2` and mentions no
depth. A constant reading has the whole family as its shadow, so

`resolutionLimit depth (apertureSign L a) = ½`  (`resolutionLimit_depth_apertureSign`)

at **every** aperture — below Nyquist and above it alike. The jump at `L/2` is a jump in the sign's
*value*, not in its information content.

What does carry information above the Nyquist aperture is the magnitude: the level reading has limit
`min ½ (depthResolution L η)`, strictly smaller
(`theSignCarriesNothingTheLevelCarriesEverything`). So the lesson of the aperture face is not "go
past Nyquist" but "past Nyquist, measure the deficit": crossing the threshold with a sign test
exchanges one uninformative constant for another.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The sign reading on the depth family -/

/-- The sign of the Weil form at aperture `a`, read on the depths of a lattice of scale `L`. -/
def apertureSign {L : ℝ} (hL : 0 < L) (a : ℝ) (d : DepthDatum) : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
    0 ≤ ((offLineLatticeConfig hL d.2.1 d.2.2).W f f).re

/-- Below the Nyquist aperture the sign is positive at every depth. -/
theorem apertureSign_of_le_half {L a : ℝ} (hL : 0 < L) (ha : a ≤ L / 2) (d : DepthDatum) :
    apertureSign hL a d :=
  (offLineLattice_weil_positive_iff hL d.2.1 d.2.2 a).mpr ha

/-- Above it the sign is negative at every depth. -/
theorem not_apertureSign_of_half_lt {L a : ℝ} (hL : 0 < L) (ha : L / 2 < a) (d : DepthDatum) :
    ¬ apertureSign hL a d := fun h =>
  absurd ((offLineLattice_weil_positive_iff hL d.2.1 d.2.2 a).mp h) (not_le.mpr ha)

/-! ### 2. The sign is constant, hence uninformative -/

/-- **The sign reading has the trivial limit at every aperture.** -/
theorem resolutionLimit_depth_apertureSign {L a : ℝ} (hL : 0 < L) (_ha : 0 < a)
    (d₀ : DepthDatum) : resolutionLimit depth (apertureSign hL a) d₀ = 1 / 2 := by
  set d₁ : DepthDatum := ⟨1 / 2, by norm_num, le_rfl⟩ with hd₁
  have hmem : d₁ ∈ shadow (apertureSign hL a) d₀ := by
    rcases le_or_gt a (L / 2) with hsub | hsup
    · exact propext (iff_of_true (apertureSign_of_le_half hL hsub d₁)
        (apertureSign_of_le_half hL hsub d₀))
    · exact propext (iff_of_false (not_apertureSign_of_half_lt hL hsup d₁)
        (not_apertureSign_of_half_lt hL hsup d₀))
  exact resolutionLimit_eq_of_mem_shadow_of_max (fun d => d.2.2) hmem rfl

/-! ### 3. The magnitude is what carries the depth -/

/-- **The sign carries nothing, the level carries everything.** At every aperture the sign reading
is floored at `½`; just above the Nyquist aperture the level reading is floored at
`min ½ (depthResolution L η)`, which the square-root law drives to `0`. -/
theorem theSignCarriesNothingTheLevelCarriesEverything {L a η : ℝ} (hL : 0 < L) (ha : L / 2 < a)
    (haL : a ≤ L) (hη : 0 ≤ η) {d₀ : DepthDatum} (hd₀ : levelReading hL a η d₀) :
    (∀ b : ℝ, 0 < b → ∀ d : DepthDatum, resolutionLimit depth (apertureSign hL b) d = 1 / 2) ∧
      resolutionLimit depth (levelReading hL a η) d₀ =
        min (1 / 2) (depthResolution L η) ∧
      resolutionLimit depth (levelReading hL a η) d₀ ≤ Real.sqrt (η / L ^ 3) :=
  ⟨fun _ hb d => resolutionLimit_depth_apertureSign hL hb d,
    resolutionLimit_depth_levelReading hL ha haL hη hd₀,
    resolutionLimit_depth_levelReading_le_sqrt hL ha haL hη hd₀⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
