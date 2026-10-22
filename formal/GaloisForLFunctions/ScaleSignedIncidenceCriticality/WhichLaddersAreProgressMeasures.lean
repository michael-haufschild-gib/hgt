import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheHeightFaceUnitIsTheFirstOffLineHorizon
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheSquareRootPrecisionLawOfDepthResolution

/-!
# Which ladders are progress measures

A mechanism is incremental when its output improves as its resources grow. In this calculus that is
a property of a *ladder*: a family of readings indexed by a resource, together with a unit, such
that the resolution limits decrease to the criterion. The field has three ladders, and exactly two
of them qualify.

* **The height ladder, in the horizon unit, converges** (`heightLadderConverges`): the limit is
  `(1+T)⁻¹`, and every tolerance is reached at a finite height.
* **The level ladder, in the depth unit, converges** (`levelLadderConverges`): the limit is
  `min ½ (depthResolution L η)`, which the square-root precision law drives below any tolerance at
  a finite level — explicitly at `η = L³ε²/4`.
* **The aperture ladder, in the width unit, is flat** (`apertureLadderIsFlat`): the limit is `½` at
  every stage, and the criterion is reached only in the limit.

`theProgressMeasureClassification` states the three together. The consequence is a constraint on the
*shape* of a mechanism, not on its strength: an argument that improves gradually must be indexed by
the truncation height or by the deficit level, and an argument indexed by the aperture must reach
infinity before it says anything. Both convergent ladders are quantitative — a horizon and a
precision — which is the same lesson as `TheScaleDatumIsFaithfulOnlyAtTheAnswer`: the qualitative
positivity unit admits no intermediate state.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The height ladder converges -/

/-- **Every tolerance is reached at a finite height.** -/
theorem heightLadderConverges {L : ℝ} (hL : 0 < L) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 0 ≤ T ∧
      resolutionLimit horizonFrequency (heightReading T) (onLineLattice hL) < ε := by
  refine ⟨1 / ε, by positivity, ?_⟩
  rw [resolutionLimit_horizonFrequency_heightReading hL (by positivity)]
  have h1 : (0 : ℝ) < 1 + 1 / ε := by positivity
  rw [inv_lt_iff_one_lt_mul₀ h1]
  have : ε * (1 / ε) = 1 := by field_simp
  nlinarith [this]

/-! ### 2. The level ladder converges -/

/-- **Every tolerance is reached at a finite level.** The explicit level is `L³ε²/4`. -/
theorem levelLadderConverges {L a : ℝ} (hL : 0 < L) (ha : L / 2 < a) (haL : a ≤ L) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ d₀ : DepthDatum, levelReading hL a η d₀ →
      resolutionLimit depth (levelReading hL a η) d₀ < ε := by
  refine ⟨L ^ 3 * ε ^ 2 / 4, by positivity, fun d₀ hd₀ => ?_⟩
  have hηnn : (0 : ℝ) ≤ L ^ 3 * ε ^ 2 / 4 := by positivity
  have hle := resolutionLimit_depth_levelReading_le_sqrt hL ha haL hηnn hd₀
  have hquot : L ^ 3 * ε ^ 2 / 4 / L ^ 3 = (ε / 2) ^ 2 := by
    have hL3 : L ^ 3 ≠ 0 := by positivity
    field_simp
    ring
  rw [hquot, Real.sqrt_sq (by positivity : (0 : ℝ) ≤ ε / 2)] at hle
  linarith

/-! ### 3. The aperture ladder is flat -/

/-- **The aperture ladder never improves.** -/
theorem apertureLadderIsFlat {Z : TemperedZeroConfig} (hZ : fullPositivity Z) :
    ∀ a : ℝ, 0 < a → resolutionLimit width (aperturePositivity a) Z = 1 / 2 :=
  (apertureResolutionJump hZ).1

/-! ### 4. The classification -/

/-- **The progress-measure classification.** The height ladder in the horizon unit and the level
ladder in the depth unit reach every tolerance at a finite stage; the aperture ladder in the width
unit is constant at `½`. An incremental mechanism must be indexed by a height or a level. -/
theorem theProgressMeasureClassification {L a : ℝ} (hL : 0 < L) (ha : L / 2 < a) (haL : a ≤ L)
    {Z : TemperedZeroConfig} (hZ : fullPositivity Z) :
    (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 ≤ T ∧
        resolutionLimit horizonFrequency (heightReading T) (onLineLattice hL) < ε) ∧
      (∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ d₀ : DepthDatum, levelReading hL a η d₀ →
        resolutionLimit depth (levelReading hL a η) d₀ < ε) ∧
      ∀ b : ℝ, 0 < b → resolutionLimit width (aperturePositivity b) Z = 1 / 2 :=
  ⟨fun _ hε => heightLadderConverges hL hε, fun _ hε => levelLadderConverges hL ha haL hε,
    apertureLadderIsFlat hZ⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
