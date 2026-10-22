import GaloisForLFunctions.ScaleSignedIncidenceCriticality.OneApertureResolvesOnlyTheScalesBelowTwiceIt
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheTwoFacesReadOneScaleDatum

/-!
# The graded aperture jump is uniformity itself

Two results of this programme pull in opposite directions. A coercive certificate at a bounded
aperture has the trivial limit `½` for the width, at **every** level `η`. The unbounded certificate
has limit `0`. The question left open is which feature of the unbounded certificate carries the
whole content: the size of its gap, the growth of its aperture, or the uniformity of the two.

It is uniformity alone, and at the lowest level. For any level `η ≥ 0`, a certificate that holds at
*every* aperture with that one gap already forces Weil positivity on all compactly supported tests
(`fullPositivity_of_uniformGain`), hence

`resolutionLimit width (uniformGain η) = 0`  (`resolutionLimit_width_uniformGain`),

while at each fixed aperture the same level reads only `½`. `theGradedApertureJump` states the pair.
The jump therefore happens at the step from "every bounded family" to "all apertures", for every
level at once, and nothing is gained by raising the gap: a positive gap at all apertures is worth
exactly what a zero gap at all apertures is worth.

On `ζ`'s configuration this is a criterion rather than a floor: a uniform gain-`η` certificate at
all apertures proves RH (`riemannHypothesis_of_uniformGain_zetaConfig`), for every `η ≥ 0`. So a
mechanism that transports one energy bound along the whole aperture axis needs no margin at all —
it needs only to keep the bound from degrading as the aperture grows.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The uniform certificate -/

/-- The level-`η` certificate held at every aperture with one and the same gap. -/
def uniformGain (η : ℝ) (Z : TemperedZeroConfig) : Prop :=
  ∀ a : ℝ, 0 < a → apertureGain a η Z

/-- **Uniformity forces full positivity.** One gap holding at every aperture already gives the
unbounded certificate, whatever the gap is. -/
theorem fullPositivity_of_uniformGain {η : ℝ} (hη : 0 ≤ η) {Z : TemperedZeroConfig}
    (h : uniformGain η Z) : fullPositivity Z := by
  intro f hf hfc
  obtain ⟨a, ha, hsub⟩ := exists_aperture_of_hasCompactSupport hfc
  have hint : (0 : ℝ) ≤ ∫ t, ‖f t‖ ^ 2 :=
    MeasureTheory.integral_nonneg fun _ => by positivity
  have hgain := h a ha f hf hsub
  nlinarith

/-! ### 2. The uniform certificate is faithful -/

/-- **The uniform certificate pins the width to zero**, at every level `η ≥ 0`. -/
theorem resolutionLimit_width_uniformGain {η : ℝ} (hη : 0 ≤ η) {Z : TemperedZeroConfig}
    (hZ : uniformGain η Z) : resolutionLimit width (uniformGain η) Z = 0 := by
  have hzero : ∀ W ∈ shadow (uniformGain η) Z, width W = 0 := fun W hW =>
    (configWidth_eq_zero_iff_weil_nonneg W.2).mpr
      (fun f hf hfc =>
        fullPositivity_of_uniformGain hη ((mem_shadow_iff.mp hW) ▸ hZ : uniformGain η W) f hf hfc)
  refine le_antisymm (csSup_le (shadow_image_nonempty width (uniformGain η) Z) ?_) ?_
  · rintro x ⟨W, hW, rfl⟩
    exact (hzero W hW).le
  · have hle := le_csSup (bddAbove_width_image (shadow (uniformGain η) Z))
      ⟨Z, mem_shadow_self (uniformGain η) Z, rfl⟩
    rwa [hzero Z (mem_shadow_self (uniformGain η) Z)] at hle

/-- **The graded aperture jump.** At every level `η ≥ 0`: each bounded aperture certifies only the
trivial `½`, while the same level held at all apertures certifies `0`. The content of the unbounded
certificate is its uniformity, not its margin. -/
theorem theGradedApertureJump {η : ℝ} (hη : 0 ≤ η) {Z : TemperedZeroConfig}
    (hZ : uniformGain η Z) :
    (∀ a : ℝ, 0 < a → resolutionLimit width (apertureGain a η) Z = 1 / 2) ∧
      resolutionLimit width (uniformGain η) Z = 0 :=
  ⟨fun a ha => resolutionLimit_width_apertureGain ha (hZ a ha),
    resolutionLimit_width_uniformGain hη hZ⟩

/-! ### 3. On `ζ` the uniform certificate is a criterion -/

/-- **A uniform certificate at all apertures proves RH**, at every level `η ≥ 0`: no margin is
needed, only that the one bound survive every aperture. -/
theorem riemannHypothesis_of_uniformGain_zetaConfig {η : ℝ} (hη : 0 ≤ η)
    (h : uniformGain η zetaConfig) : RiemannHypothesis := by
  refine riemannHypothesis_iff_failureApertures_zetaConfig_eq_empty.mpr ?_
  refine (failureApertures_eq_empty_iff_width_eq_zero zetaConfig).mpr ?_
  exact (configWidth_eq_zero_iff_weil_nonneg zetaConfig.2).mpr
    (fun f hf hfc => fullPositivity_of_uniformGain hη h f hf hfc)

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
