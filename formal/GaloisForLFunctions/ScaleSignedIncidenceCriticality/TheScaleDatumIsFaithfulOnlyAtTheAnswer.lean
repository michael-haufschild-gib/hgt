import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheCompositionLawAndThePushforwardInvariant

/-!
# The scale datum is faithful only at the answer

The failure-aperture set is the whole aperture ladder read at once: a configuration is
Weil-positive at aperture `a` exactly when `a` is not a failure aperture
(`aperturePositivity_iff_notMem_failureApertures`). So the scale datum is the join of every
certificate the field can write down, and it decides RH — emptiness is width zero. One might expect
it to be a progress measure. It is not.

* `resolutionLimit_width_failureApertures_of_empty` — at a datum whose failure set is empty the
  limit of the width is `0`: the reading is **faithful**, and it has proved the critical line.
* `resolutionLimit_width_failureApertures_of_Ioi` — at a datum whose failure set is `(a, ∞)` the
  limit is `½`: the reading is **maximally blind**, and says nothing about how far off the line the
  configuration is.

`theScaleDatumIsAllOrNothing` states the pair. The scale datum is therefore all-or-nothing: it is
perfect at the answer and useless at every datum that is not the answer, with no intermediate
behaviour. There is no way to be "closer" in this unit.

That is the strategic content. An incremental mechanism — one whose output improves continuously as
its resources grow — cannot be built on positivity certificates, because the invariant they control
jumps from `0` to `½` as soon as the configuration leaves the line. It can be built on the
*level* readings, whose limit `min ½ (depthResolution L η)` decreases continuously with the
precision `η` (`TheSquareRootPrecisionLawOfDepthResolution`), and on the mass-and-certificate pair,
whose bound decreases with the aperture (`TheApertureMassSeamIsProductive`). Progress lives in the
quantitative units, never in the qualitative one.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The scale datum is the whole ladder -/

/-- **The scale datum is the aperture ladder.** -/
theorem aperturePositivity_iff_notMem_failureApertures {a : ℝ} (ha : 0 < a)
    (Z : TemperedZeroConfig) : aperturePositivity a Z ↔ a ∉ failureApertures Z := by
  simp only [failureApertures, mem_setOf_eq, not_and, not_not]
  exact ⟨fun h _ => h, fun h => h ha⟩

/-! ### 2. Faithful at the answer -/

/-- **At the critical line the scale datum is faithful.** Its shadow there consists of
configurations of width zero. -/
theorem resolutionLimit_width_failureApertures_of_empty {Z : TemperedZeroConfig}
    (hZ : failureApertures Z = ∅) :
    resolutionLimit width failureApertures Z = 0 := by
  have hzero : ∀ W ∈ shadow failureApertures Z, width W = 0 := fun W hW =>
    (failureApertures_eq_empty_iff_width_eq_zero W).mp ((mem_shadow_iff.mp hW).trans hZ)
  refine le_antisymm (csSup_le (shadow_image_nonempty width failureApertures Z) ?_) ?_
  · rintro x ⟨W, hW, rfl⟩
    exact (hzero W hW).le
  · have hle := le_csSup (bddAbove_width_image (shadow failureApertures Z))
      ⟨Z, mem_shadow_self failureApertures Z, rfl⟩
    rwa [hzero Z (mem_shadow_self failureApertures Z)] at hle

/-! ### 3. Maximally blind elsewhere -/

/-- **Off the line the scale datum is maximally blind.** -/
theorem resolutionLimit_width_failureApertures_of_Ioi {a : ℝ} (ha : 0 < a)
    {Z : TemperedZeroConfig} (hZ : failureApertures Z = Ioi a) :
    resolutionLimit width failureApertures Z = 1 / 2 :=
  resolutionLimit_width_eq_half_of_factors (r := id) ha hZ

/-! ### 4. All or nothing -/

/-- **The scale datum is all-or-nothing.** It is faithful exactly at the answer and carries the
trivial bound at every datum off the line, so it supports no incremental strategy. -/
theorem theScaleDatumIsAllOrNothing {a : ℝ} (ha : 0 < a) :
    (∀ Z : TemperedZeroConfig, failureApertures Z = ∅ →
        resolutionLimit width failureApertures Z = 0) ∧
      ∀ Z : TemperedZeroConfig, failureApertures Z = Ioi a →
        resolutionLimit width failureApertures Z = 1 / 2 :=
  ⟨fun _ hZ => resolutionLimit_width_failureApertures_of_empty hZ,
    fun _ hZ => resolutionLimit_width_failureApertures_of_Ioi ha hZ⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
