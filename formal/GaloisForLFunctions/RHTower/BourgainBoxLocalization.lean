/-
# Four-dimensional box localization

The one-dimensional interval-recovery identity tensorizes over Bourgain's
four phase coordinates.  This file defines the resulting local boxes and
product multipliers, proves their explicit norm bound, and proves exact
recovery of the four-dimensional additive character.
-/
import GaloisForLFunctions.RHTower.BourgainIntervalLocalization
import GaloisForLFunctions.RHTower.BourgainFejerMomentTransfer

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Product of normalized localization intervals centered at `x`. -/
def bourgainLocalBox
    (Y L x : BourgainPhaseSpace) : Set BourgainPhaseSpace :=
  Set.univ.pi fun j : Fin 4 =>
    Set.Ioc
      ((x j - bourgainLocalizationEpsilon (Y j)) / L j)
      ((x j + bourgainLocalizationEpsilon (Y j)) / L j)

/-- Product of the four reciprocal interval multipliers. -/
def bourgainProductLocalizationMultiplier
    (Y L y : BourgainPhaseSpace) : ℂ :=
  ∏ j : Fin 4,
    bourgainLocalizationMultiplier (Y j) (L j) (y j)

theorem norm_bourgainProductLocalizationMultiplier_le
    {Y L y : BourgainPhaseSpace}
    (hY : ∀ j, 0 < Y j) (hL : ∀ j, 0 < L j)
    (hy : ∀ j, |y j| ≤ Y j) :
    ‖bourgainProductLocalizationMultiplier Y L y‖ ≤
      ∏ j : Fin 4, (2 * Real.pi * Y j * L j) := by
  unfold bourgainProductLocalizationMultiplier
  rw [norm_prod]
  apply Finset.prod_le_prod
  · intro j hj
    positivity
  · intro j hj
    exact norm_bourgainLocalizationMultiplier_le
      (hY j) (hL j) (hy j)

/-- The localized four-dimensional character integral is the product of
the four one-dimensional interval integrals. -/
theorem integral_bourgainLocalBox_character
    {Y L : BourgainPhaseSpace} (x y : BourgainPhaseSpace)
    (hY : ∀ j, 0 < Y j) (hL : ∀ j, 0 < L j) :
    (∫ z in bourgainLocalBox Y L x,
        bourgainAdditiveCharacter
          (bourgainCoordinateScale L z) y) =
      ∏ j : Fin 4,
        (∫ t in
          ((x j - bourgainLocalizationEpsilon (Y j)) / L j)..
          ((x j + bourgainLocalizationEpsilon (Y j)) / L j),
          bourgainUnitCharacter ((L j * y j) * t)) := by
  rw [show
      (fun z : BourgainPhaseSpace =>
        bourgainAdditiveCharacter (bourgainCoordinateScale L z) y) =
      fun z : BourgainPhaseSpace =>
        ∏ j : Fin 4,
          bourgainUnitCharacter ((L j * y j) * z j) by
    funext z
    rw [bourgainAdditiveCharacter_eq_prod_unitCharacter]
    apply Finset.prod_congr rfl
    intro j hj
    unfold bourgainCoordinateScale
    congr 1
    ring]
  unfold bourgainLocalBox
  rw [volume_pi, Measure.restrict_pi_pi]
  have hprod :=
    integral_fintype_prod_eq_prod
      (𝕜 := ℂ)
      (fun j : Fin 4 =>
        fun z : ℝ =>
          bourgainUnitCharacter ((L j * y j) * z))
      (μ := fun j : Fin 4 =>
        volume.restrict
          (Set.Ioc
            ((x j - bourgainLocalizationEpsilon (Y j)) / L j)
            ((x j + bourgainLocalizationEpsilon (Y j)) / L j)))
  rw [hprod]
  apply Finset.prod_congr rfl
  intro j hj
  rw [← intervalIntegral.integral_of_le]
  have heps : 0 < bourgainLocalizationEpsilon (Y j) := by
    unfold bourgainLocalizationEpsilon
    exact one_div_pos.mpr (mul_pos (by norm_num) (hY j))
  exact
    (div_le_div_iff_of_pos_right (hL j)).2 (by linarith)

/-- Exact four-dimensional character recovery from a normalized local
box. -/
theorem bourgain_recover_character_from_localBox
    {Y L x y : BourgainPhaseSpace}
    (hY : ∀ j, 0 < Y j) (hL : ∀ j, 0 < L j)
    (hy : ∀ j, |y j| ≤ Y j) :
    bourgainProductLocalizationMultiplier Y L y *
        (∫ z in bourgainLocalBox Y L x,
          bourgainAdditiveCharacter
            (bourgainCoordinateScale L z) y) =
      bourgainAdditiveCharacter x y := by
  rw [integral_bourgainLocalBox_character x y hY hL]
  unfold bourgainProductLocalizationMultiplier
  rw [← Finset.prod_mul_distrib]
  rw [bourgainAdditiveCharacter_eq_prod_unitCharacter]
  apply Finset.prod_congr rfl
  intro j hj
  simpa [mul_comm] using
    (bourgain_recover_character_from_interval
      (x := x j) (hY j) (hL j) (hy j))

end

end RHTower
