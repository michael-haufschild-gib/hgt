import GaloisForLFunctions.ScaleSignedIncidenceCriticality.BoundedHeightReadingsCannotResolveTheWidth

/-!
# The aperture ladder is strict, yet every stage is trivial

Enlarging the aperture is a genuine gain of information: for `a < b` the depth-`½` lattice of
ordinate spacing `2π/(a+b)` is Weil-positive at aperture `a` and negative at aperture `b`
(`SquareRootThreshold.offLineLattice_weil_positive_iff`), so the aperture-`b` reading separates a
pair the aperture-`a` reading identifies, and the shadows strictly decrease
(`shadow_aperturePositivity_ssubset`).

Yet the resolution limit of the width is `½` at every stage of this strictly increasing ladder and
`0` at its limit (`apertureLadder`). The information of the width is therefore not accumulated along
the ladder at all: every finite stage of an infinite strictly increasing chain of data certifies
only the trivial bound, and the entire content appears in the limit.

This is the precise sense in which the trans-Nyquist regime is not an asymptotic refinement of the
finite-aperture regime, and why no sequence of finite-aperture certificates — however long and
however strictly improving — approximates the critical line.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The on-line lattice is positive at every aperture -/

theorem fullPositivity_onLineLattice {L : ℝ} (hL : 0 < L) : fullPositivity (onLineLattice hL) :=
  fun f _ _ => re_W_onLineLatticeConfig_nonneg hL f

theorem aperturePositivity_onLineLattice {L : ℝ} (hL : 0 < L) (a : ℝ) :
    aperturePositivity a (onLineLattice hL) := fun f _ _ =>
  re_W_onLineLatticeConfig_nonneg hL f

/-! ### 2. Each aperture step separates a new pair -/

/-- **A new pair at every step.** For `0 < a < b` the depth-`½` lattice of period `2π/(a+b)` is
positive at aperture `a` and negative at aperture `b`. -/
theorem exists_aperturePositivity_and_not {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ Z : TemperedZeroConfig, width Z = 1 / 2 ∧ aperturePositivity a Z ∧
      ¬ aperturePositivity b Z := by
  have hL : (0 : ℝ) < a + b := by linarith
  have hδ : (0 : ℝ) < 1 / 2 := by norm_num
  refine ⟨⟨offLineLatticeConfig hL hδ le_rfl, temperedConfig_offLineLatticeConfig hL hδ le_rfl⟩,
    configWidth_offLineLatticeConfig hL hδ le_rfl, ?_, ?_⟩
  · exact (offLineLattice_weil_positive_iff hL hδ le_rfl a).mpr (by linarith)
  · exact fun h => absurd ((offLineLattice_weil_positive_iff hL hδ le_rfl b).mp h)
      (by linarith)

/-- **The shadows strictly decrease along the ladder.** -/
theorem shadow_aperturePositivity_ssubset {L a b : ℝ} (hL : 0 < L) (ha : 0 < a) (hab : a < b) :
    shadow (aperturePositivity b) (onLineLattice hL) ⊂
      shadow (aperturePositivity a) (onLineLattice hL) := by
  obtain ⟨Z, -, hposa, hposb⟩ := exists_aperturePositivity_and_not ha hab
  have hsub : shadow (aperturePositivity b) (onLineLattice hL) ⊆
      shadow (aperturePositivity a) (onLineLattice hL) := by
    intro W hW
    have hWb : aperturePositivity b W := by
      rw [mem_shadow_iff] at hW
      rw [hW]
      exact aperturePositivity_onLineLattice hL b
    exact propext (iff_of_true (aperturePositivity_mono hab.le hWb)
      (aperturePositivity_onLineLattice hL a))
  refine (Set.ssubset_iff_of_subset hsub).mpr ⟨Z, ?_, ?_⟩
  · exact propext (iff_of_true hposa (aperturePositivity_onLineLattice hL a))
  · intro hZ
    rw [mem_shadow_iff] at hZ
    refine hposb ?_
    rw [hZ]
    exact aperturePositivity_onLineLattice hL b

/-! ### 3. The ladder -/

/-- **The aperture ladder.** The readings strictly refine one another along the aperture, every
stage certifies only the trivial bound `½` on the width, and the limiting reading certifies `0`.
Information is gained at every step and none of it is the width. -/
theorem apertureLadder {L : ℝ} (hL : 0 < L) :
    (∀ a b : ℝ, 0 < a → a < b →
        shadow (aperturePositivity b) (onLineLattice hL) ⊂
          shadow (aperturePositivity a) (onLineLattice hL)) ∧
      (∀ a : ℝ, 0 < a →
        resolutionLimit width (aperturePositivity a) (onLineLattice hL) = 1 / 2) ∧
      resolutionLimit width fullPositivity (onLineLattice hL) = 0 :=
  ⟨fun _ _ ha hab => shadow_aperturePositivity_ssubset hL ha hab,
    fun a ha => resolutionLimit_width_aperturePositivity ha (aperturePositivity_onLineLattice hL a),
    resolutionLimit_width_fullPositivity (fullPositivity_onLineLattice hL)⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
