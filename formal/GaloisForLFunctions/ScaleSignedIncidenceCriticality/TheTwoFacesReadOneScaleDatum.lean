import GaloisForLFunctions.ScaleSignedIncidenceCriticality.ThePrimeSideScaleUnitAndItsUniversalFloor
import GaloisForLFunctions.SquareRootThreshold.ZetaSmallApertureHeightWindowPositivity

/-!
# The two faces read one scale datum

The zero side and the prime side of the critical form were given scale units separately: the
failure apertures of a configuration and the failure apertures of a prime weight. On `ζ` they are
the *same set*, because the explicit formula identifies the two functionals
(`RHTower.zeta_W_eq_weilFullFunctional`):

`failureApertures ζ = weightFailureApertures Λ`  (`failureApertures_zetaConfig`).

Three things follow.

* `riemannHypothesis_iff_failureApertures_zetaConfig_eq_empty` — RH is emptiness of that one set.
  Together with the prime-side criterion this gives a single scale-unit characterisation valid on
  both faces at once (`theSharedScaleCriterion`).
* `failureApertures_zetaConfig_subset_Ioi_threeTenths` — the prime-side universal floor transfers
  to the zero side: the configuration of `ζ` has **no** failure aperture below `3/10`,
  unconditionally. A failure of RH must therefore show itself at an aperture above that floor, and
  never below it.
* Floors proved on either face transfer to the other in this unit, because they are floors for one
  set. The scale unit is thus the first invariant of the programme that is literally shared by two
  faces rather than merely numerically equal on them.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The configuration of `ζ` as a datum -/

/-- The zero configuration of `ζ` as a datum of the calculus. -/
noncomputable def zetaConfig : TemperedZeroConfig :=
  ⟨zetaZeroConfig, temperedConfig_zetaZeroConfig⟩

/-- **The two faces are one reading.** At every aperture, positivity of the Weil form of `ζ`'s
configuration is positivity of the full Weil functional of the von Mangoldt weight. -/
theorem aperturePositivity_zetaConfig_iff (a : ℝ) :
    aperturePositivity a zetaConfig ↔
      weightAperturePositivity a (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) := by
  constructor
  · intro h f hf hfs
    have hfc : HasCompactSupport f :=
      HasCompactSupport.of_support_subset_isCompact isCompact_Icc
        ((subset_tsupport f).trans hfs)
    rw [← zeta_W_eq_weilFullFunctional hf hfc]
    exact h f hf hfs
  · intro h f hf hfs
    have hfc : HasCompactSupport f :=
      HasCompactSupport.of_support_subset_isCompact isCompact_Icc
        ((subset_tsupport f).trans hfs)
    have := h f hf hfs
    rwa [← zeta_W_eq_weilFullFunctional hf hfc] at this

/-- **One scale datum.** -/
theorem failureApertures_zetaConfig :
    failureApertures zetaConfig =
      weightFailureApertures (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) := by
  ext a
  simp only [failureApertures, weightFailureApertures, mem_setOf_eq,
    aperturePositivity_zetaConfig_iff]

/-! ### 2. The universal floor transfers to the zero side -/

/-- **The configuration of `ζ` has no failure aperture below `3/10`**, unconditionally: the
prime-side quiet zone is a statement about the zeros as well. -/
theorem failureApertures_zetaConfig_subset_Ioi_threeTenths :
    failureApertures zetaConfig ⊆ Ioi (3 / 10) := by
  rw [failureApertures_zetaConfig]
  exact weightFailureApertures_subset_Ioi_threeTenths _

/-- `ζ`'s configuration is Weil-positive at aperture `3/10`. -/
theorem aperturePositivity_zetaConfig_threeTenths : aperturePositivity (3 / 10) zetaConfig :=
  (aperturePositivity_zetaConfig_iff _).mpr (weightAperturePositivity_threeTenths _)

/-! ### 3. RH in the shared unit -/

/-- **RH is emptiness of the failure set.** -/
theorem riemannHypothesis_iff_failureApertures_zetaConfig_eq_empty :
    RiemannHypothesis ↔ failureApertures zetaConfig = ∅ := by
  rw [failureApertures_eq_empty_iff_width_eq_zero]
  exact riemannHypothesis_iff_configWidth_zetaZeroConfig_eq_zero

/-- **The shared scale criterion.** RH, emptiness of the zero-side failure set, emptiness of the
prime-side failure set and membership of `Λ` in the full Weil cone are one statement; and the
failure set, were it nonempty, would start above `3/10`. -/
theorem theSharedScaleCriterion :
    (RiemannHypothesis ↔ failureApertures zetaConfig = ∅) ∧
      (failureApertures zetaConfig =
        weightFailureApertures (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))) ∧
      (RiemannHypothesis ↔
        WeilPositiveFull (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))) ∧
      failureApertures zetaConfig ⊆ Ioi (3 / 10) :=
  ⟨riemannHypothesis_iff_failureApertures_zetaConfig_eq_empty, failureApertures_zetaConfig,
    ⟨fun hRH =>
      WeilSpectral.weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mpr
        ⟨hRH, fun _ _ => rfl⟩,
      fun hW =>
      (WeilSpectral.weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mp hW).1⟩,
    failureApertures_zetaConfig_subset_Ioi_threeTenths⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
