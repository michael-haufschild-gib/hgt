/-
# Four-dimensional box localization

The one-dimensional interval-recovery identity tensorizes over Bourgain's
four phase coordinates.  This file defines the resulting local boxes and
product multipliers, proves their explicit norm bound, and proves exact
recovery of the four-dimensional additive character.
-/
import GaloisForLFunctions.RHTower.BourgainIntervalLocalization
import GaloisForLFunctions.RHTower.BourgainFejerMomentTransfer
import GaloisForLFunctions.RHTower.BourgainGaussianLargeSieve

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

/-- Enlarged spatial scale making every localization box fit inside the
normalized four-cube. -/
def bourgainLocalizationScale
    (X Y : BourgainPhaseSpace) : BourgainPhaseSpace :=
  fun j => X j + bourgainLocalizationEpsilon (Y j)

theorem bourgainLocalizationScale_pos
    {X Y : BourgainPhaseSpace}
    (hX : ∀ j, 0 < X j) (hY : ∀ j, 0 < Y j) :
    ∀ j, 0 < bourgainLocalizationScale X Y j := by
  intro j
  unfold bourgainLocalizationScale bourgainLocalizationEpsilon
  have heps : 0 < 1 / (8 * Y j) :=
    one_div_pos.mpr (mul_pos (by norm_num) (hY j))
  linarith [hX j]

/-- A localization box centered at a point in the `X`-box lies in the
normalized four-cube. -/
theorem bourgainLocalBox_subset_fourCube
    {X Y x : BourgainPhaseSpace}
    (hX : ∀ j, 0 < X j) (hY : ∀ j, 0 < Y j)
    (hx : ∀ j, |x j| ≤ X j) :
    bourgainLocalBox Y (bourgainLocalizationScale X Y) x ⊆
      bourgainFourCube := by
  intro z hz
  have hz' :
      ∀ j : Fin 4,
        z j ∈ Set.Ioc
          ((x j - bourgainLocalizationEpsilon (Y j)) /
            bourgainLocalizationScale X Y j)
          ((x j + bourgainLocalizationEpsilon (Y j)) /
            bourgainLocalizationScale X Y j) := by
    simpa [bourgainLocalBox] using hz
  unfold bourgainFourCube
  change ‖z‖ ≤ 1
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
  intro j
  rw [Real.norm_eq_abs, abs_le]
  have heps : 0 < bourgainLocalizationEpsilon (Y j) := by
    unfold bourgainLocalizationEpsilon
    exact one_div_pos.mpr (mul_pos (by norm_num) (hY j))
  have hL : 0 < bourgainLocalizationScale X Y j :=
    bourgainLocalizationScale_pos hX hY j
  have hxab := abs_le.mp (hx j)
  constructor
  · have hlow := (hz' j).1
    apply le_of_lt
    rw [div_lt_iff₀ hL] at hlow
    unfold bourgainLocalizationScale at hlow
    nlinarith
  · have hupp := (hz' j).2
    rw [le_div_iff₀ hL] at hupp
    unfold bourgainLocalizationScale at hupp
    nlinarith

/-- Two localization boxes can meet only if their centers are a sharp
scaled-near pair. -/
theorem bourgainScaledNear_of_mem_localBoxes
    {Y L x x' z : BourgainPhaseSpace}
    (hY : ∀ j, 0 < Y j) (hL : ∀ j, 0 < L j)
    (hz : z ∈ bourgainLocalBox Y L x)
    (hz' : z ∈ bourgainLocalBox Y L x') :
    BourgainScaledNear Y x x' := by
  have hzmem :
      ∀ j : Fin 4,
        z j ∈ Set.Ioc
          ((x j - bourgainLocalizationEpsilon (Y j)) / L j)
          ((x j + bourgainLocalizationEpsilon (Y j)) / L j) := by
    simpa [bourgainLocalBox] using hz
  have hzmem' :
      ∀ j : Fin 4,
        z j ∈ Set.Ioc
          ((x' j - bourgainLocalizationEpsilon (Y j)) / L j)
          ((x' j + bourgainLocalizationEpsilon (Y j)) / L j) := by
    simpa [bourgainLocalBox] using hz'
  intro j
  have heps :
      bourgainLocalizationEpsilon (Y j) =
        1 / (8 * Y j) := rfl
  have h₁ := (hzmem j).1
  have h₂ := (hzmem j).2
  have h₁' := (hzmem' j).1
  have h₂' := (hzmem' j).2
  rw [div_lt_iff₀ (hL j)] at h₁ h₁'
  rw [le_div_iff₀ (hL j)] at h₂ h₂'
  have habs :
      |x j - x' j| <
        2 * bourgainLocalizationEpsilon (Y j) := by
    rw [abs_lt]
    constructor <;> linarith
  rw [abs_mul, abs_of_pos (hY j)]
  rw [heps] at habs
  have hcalc :
      Y j * (2 * (1 / (8 * Y j))) = 1 / 4 := by
    field_simp [(hY j).ne']
    ring
  calc
    Y j * |x j - x' j| <
        Y j * (2 * (1 / (8 * Y j))) :=
      mul_lt_mul_of_pos_left habs (hY j)
    _ = 1 / 4 := hcalc
    _ < 1 / 2 := by norm_num

/-- Exact real volume of every normalized localization box. -/
theorem volume_bourgainLocalBox_toReal
    {Y L x : BourgainPhaseSpace}
    (hY : ∀ j, 0 < Y j) (hL : ∀ j, 0 < L j) :
    (volume (bourgainLocalBox Y L x)).toReal =
      ∏ j : Fin 4,
        (2 * bourgainLocalizationEpsilon (Y j) / L j) := by
  unfold bourgainLocalBox
  rw [Real.volume_pi_Ioc, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro j hj
  rw [ENNReal.toReal_ofReal]
  · ring
  · have heps : 0 < bourgainLocalizationEpsilon (Y j) := by
      unfold bourgainLocalizationEpsilon
      exact one_div_pos.mpr (mul_pos (by norm_num) (hY j))
    have hdiv :
        (x j - bourgainLocalizationEpsilon (Y j)) / L j ≤
          (x j + bourgainLocalizationEpsilon (Y j)) / L j :=
      (div_le_div_iff_of_pos_right (hL j)).2 (by linarith)
    linarith

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
