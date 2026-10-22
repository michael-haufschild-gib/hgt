import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheDepthBecomesVisibleJustAboveTheNyquistAperture

/-!
# The square-root precision law of depth resolution

Every limit in this programme so far has been trivial: `½` for the width, `0` for the unbounded
aperture, vacuity for the node and prime-window faces. Just above the Nyquist aperture the depth
*is* visible, so there the limit should be a genuine number. It is, and this module computes it.

The data are the depths `δ ∈ (0, ½]` of the off-line lattice of a fixed spacing `2π/L`, the
invariant is the depth, and the reading is the level-`η` Weil floor on an aperture `a` in
`(L/2, L]`. By the threshold law that reading is exactly `δ ≤ depthResolution L η`
(`levelReading_iff`), with

`depthResolution L η = arcosh(1 + η/(2L)) / L`,

and hence (`resolutionLimit_depth_levelReading`)

`resolutionLimit depth (levelReading a η) = min ½ (depthResolution L η)`.

This is the first nontrivial exact limit of the programme: a level-`η` certificate resolves the
depth to exactly that value and no further, and the value is attained.

Its asymptotic form is the **square-root precision law**
(`resolutionLimit_depth_levelReading_le_sqrt`):

`depthResolution L η ≤ √(η / L³)`.

A method that controls the Weil deficit to precision `η` resolves depths only down to the square
root of `η/L³`. To certify a depth bound `δ` at scale `L` it must therefore control the deficit to
`L³δ²` — the corpus's "square-root precision at every scale" criterion, here derived as a statement
about what a class of readings can prove rather than imposed as a requirement.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The depth resolution of a level -/

/-- The depth a level-`η` certificate resolves at scale `L`: the inverse of the threshold law. -/
noncomputable def depthResolution (L η : ℝ) : ℝ := Real.arcosh (1 + η / (2 * L)) / L

/-- **The threshold law inverted.** A depth has deficit at most `η` exactly when it is at most the
depth resolution of `η`. -/
theorem weilFloorThreshold_le_iff {L δ η : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hη : 0 ≤ η) :
    weilFloorThreshold L δ ≤ η ↔ δ ≤ depthResolution L η := by
  have h2L : (0 : ℝ) < 2 * L := by linarith
  have h1 : (1 : ℝ) ≤ 1 + η / (2 * L) := by
    have h : 0 ≤ η / (2 * L) := by positivity
    linarith
  have harc : Real.cosh (Real.arcosh (1 + η / (2 * L))) = 1 + η / (2 * L) := Real.cosh_arcosh h1
  have harcnn : 0 ≤ Real.arcosh (1 + η / (2 * L)) := Real.arcosh_nonneg h1
  have hδL : (0 : ℝ) < δ * L := by positivity
  have hstep : weilFloorThreshold L δ ≤ η ↔ Real.cosh (δ * L) ≤ 1 + η / (2 * L) := by
    rw [weilFloorThreshold]
    constructor
    · intro h
      have hd : Real.cosh (δ * L) - 1 ≤ η / (2 * L) := by
        rw [le_div_iff₀ h2L]; nlinarith
      linarith
    · intro h
      have hd : Real.cosh (δ * L) - 1 ≤ η / (2 * L) := by linarith
      rw [le_div_iff₀ h2L] at hd
      nlinarith
  rw [hstep, ← harc, Real.cosh_le_cosh, abs_of_pos hδL, abs_of_nonneg harcnn,
    depthResolution, le_div_iff₀ hL]

/-- The depth resolution is strictly positive at a positive level. -/
theorem depthResolution_pos {L η : ℝ} (hL : 0 < L) (hη : 0 < η) : 0 < depthResolution L η := by
  have h1 : (1 : ℝ) < 1 + η / (2 * L) := by
    have h : 0 < η / (2 * L) := by positivity
    linarith
  exact div_pos (Real.arcosh_pos h1) hL

/-! ### 2. The data of a depth family at one scale -/

/-- A depth of the lattice family: the datum a method studying a configuration of known scale
actually varies. -/
def DepthDatum : Type := {δ : ℝ // 0 < δ ∧ δ ≤ 1 / 2}

/-- The invariant: the depth itself. -/
def depth (d : DepthDatum) : ℝ := d.1

/-- The reading: the level-`η` Weil floor of the lattice of spacing `2π/L` on aperture `a`. -/
def levelReading {L : ℝ} (hL : 0 < L) (a η : ℝ) (d : DepthDatum) : Prop :=
  WeilFloorAtLevel (offLineLatticeConfig hL d.2.1 d.2.2) a η

/-- **The reading is exactly a depth bound.** -/
theorem levelReading_iff {L a η : ℝ} (hL : 0 < L) (ha : L / 2 < a) (haL : a ≤ L) (hη : 0 ≤ η)
    (d : DepthDatum) : levelReading hL a η d ↔ depth d ≤ depthResolution L η := by
  rw [levelReading, weilFloorAtLevel_offLineLattice_iff_cosh hL d.2.1 d.2.2 ha haL,
    ← weilFloorThreshold, weilFloorThreshold_le_iff hL d.2.1 hη]
  rfl

/-! ### 3. The exact limit -/

/-- **The first nontrivial exact limit.** A level-`η` certificate just above the Nyquist aperture
resolves the depth to exactly `min ½ (depthResolution L η)`, and the value is attained. -/
theorem resolutionLimit_depth_levelReading {L a η : ℝ} (hL : 0 < L) (ha : L / 2 < a)
    (haL : a ≤ L) (hη : 0 ≤ η) {d₀ : DepthDatum} (hd₀ : levelReading hL a η d₀) :
    resolutionLimit depth (levelReading hL a η) d₀ = min (1 / 2) (depthResolution L η) := by
  have hD : 0 < depthResolution L η :=
    lt_of_lt_of_le d₀.2.1 ((levelReading_iff hL ha haL hη d₀).mp hd₀)
  have hm0 : 0 < min (1 / 2 : ℝ) (depthResolution L η) := lt_min (by norm_num) hD
  have hmle : min (1 / 2 : ℝ) (depthResolution L η) ≤ 1 / 2 := min_le_left _ _
  have hbdd : BddAbove (depth '' shadow (levelReading hL a η) d₀) := by
    refine ⟨min (1 / 2) (depthResolution L η), ?_⟩
    rintro x ⟨d, hd, rfl⟩
    have hread : levelReading hL a η d := (mem_shadow_iff.mp hd) ▸ hd₀
    exact le_min d.2.2 ((levelReading_iff hL ha haL hη d).mp hread)
  refine le_antisymm (csSup_le (shadow_image_nonempty depth (levelReading hL a η) d₀) ?_) ?_
  · rintro x ⟨d, hd, rfl⟩
    have hread : levelReading hL a η d := (mem_shadow_iff.mp hd) ▸ hd₀
    exact le_min d.2.2 ((levelReading_iff hL ha haL hη d).mp hread)
  · set d₁ : DepthDatum := ⟨min (1 / 2) (depthResolution L η), hm0, hmle⟩ with hd₁
    have hread₁ : levelReading hL a η d₁ :=
      (levelReading_iff hL ha haL hη d₁).mpr (min_le_right _ _)
    have hmem : d₁ ∈ shadow (levelReading hL a η) d₀ := propext (iff_of_true hread₁ hd₀)
    exact le_csSup hbdd ⟨d₁, hmem, rfl⟩

/-! ### 4. The square-root precision law -/

/-- **The square-root precision law.** The depth resolution of a level is at most the square root
of the level divided by the cube of the scale. -/
theorem depthResolution_le_sqrt {L η : ℝ} (hL : 0 < L) (hη : 0 ≤ η) :
    depthResolution L η ≤ Real.sqrt (η / L ^ 3) := by
  rcases le_or_gt (depthResolution L η) 0 with h | h
  · exact h.trans (Real.sqrt_nonneg _)
  · have hthr : weilFloorThreshold L (depthResolution L η) ≤ η :=
      (weilFloorThreshold_le_iff hL h hη).mpr le_rfl
    have hcube := cube_mul_sq_le_weilFloorThreshold hL h
    have hsq : depthResolution L η ^ 2 ≤ η / L ^ 3 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < L ^ 3)]
      nlinarith
    calc depthResolution L η = Real.sqrt (depthResolution L η ^ 2) :=
          (Real.sqrt_sq h.le).symm
      _ ≤ Real.sqrt (η / L ^ 3) := Real.sqrt_le_sqrt hsq

/-- **The limit obeys the square-root law.** A method controlling the Weil deficit to precision
`η` at scale `L` certifies no depth bound sharper than `√(η/L³)`. -/
theorem resolutionLimit_depth_levelReading_le_sqrt {L a η : ℝ} (hL : 0 < L) (ha : L / 2 < a)
    (haL : a ≤ L) (hη : 0 ≤ η) {d₀ : DepthDatum} (hd₀ : levelReading hL a η d₀) :
    resolutionLimit depth (levelReading hL a η) d₀ ≤ Real.sqrt (η / L ^ 3) := by
  rw [resolutionLimit_depth_levelReading hL ha haL hη hd₀]
  exact (min_le_right _ _).trans (depthResolution_le_sqrt hL hη)

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
