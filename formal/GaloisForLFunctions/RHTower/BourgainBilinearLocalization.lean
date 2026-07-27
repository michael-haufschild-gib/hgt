/-
# Exact bilinear localization

This file packages the bilinear form in Bourgain's double-large-sieve step.
The first variable is represented by its local-box coefficient sum; the
second by a Fourier sum whose weights include the reciprocal localization
multiplier.  Tensorized interval recovery proves that their integral is
exactly the original finite bilinear form.
-/
import GaloisForLFunctions.RHTower.BourgainLocalizedCoefficientL2

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

def bourgainBilinearForm
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → BourgainPhaseSpace) (y : κ → BourgainPhaseSpace)
    (a : ι → ℂ) (b : κ → ℂ) : ℂ :=
  ∑ i : ι, ∑ j : κ,
    a i * b j * bourgainAdditiveCharacter (x i) (y j)

def bourgainLocalizedFourierWeight
    {κ : Type*} [Fintype κ]
    (Y L : BourgainPhaseSpace) (y : κ → BourgainPhaseSpace)
    (b : κ → ℂ) (j : κ) : ℂ :=
  b j * bourgainProductLocalizationMultiplier Y L (y j)

def bourgainLocalBoxCharacter
    (Y L x y z : BourgainPhaseSpace) : ℂ := by
  classical
  exact if z ∈ bourgainLocalBox Y L x
    then bourgainAdditiveCharacter (bourgainCoordinateScale L z) y
    else 0

def bourgainLocalBoxCharacterTerm
    (Y L x y : BourgainPhaseSpace) (c : ℂ)
    (z : BourgainPhaseSpace) : ℂ := by
  classical
  exact if z ∈ bourgainLocalBox Y L x
    then c * bourgainProductLocalizationMultiplier Y L y *
      bourgainAdditiveCharacter (bourgainCoordinateScale L z) y
    else 0

theorem integrable_bourgainLocalBoxCharacter
    (Y L x y : BourgainPhaseSpace) :
    Integrable (bourgainLocalBoxCharacter Y L x y) := by
  classical
  let S := bourgainLocalBox Y L x
  let f : BourgainPhaseSpace → ℂ := fun z =>
    if z ∈ S
    then bourgainAdditiveCharacter (bourgainCoordinateScale L z) y
    else 0
  let g : BourgainPhaseSpace → ℂ :=
    S.indicator (fun _ => 1)
  have hS : MeasurableSet S :=
    measurableSet_bourgainLocalBox Y L x
  have hgOn :
      IntegrableOn (fun _ : BourgainPhaseSpace => (1 : ℂ)) S :=
    integrableOn_const
      (volume_bourgainLocalBox_ne_top Y L x) (by finiteness)
  have hg : Integrable g := hgOn.integrable_indicator hS
  have hfmeas : AEStronglyMeasurable f := by
    apply Measurable.aestronglyMeasurable
    unfold f
    apply Measurable.ite hS
    · unfold bourgainAdditiveCharacter
        bourgainCoordinateScale bourgainDot
      fun_prop
    · exact measurable_const
  have hf : Integrable f := by
    apply hg.mono hfmeas
    filter_upwards [] with z
    by_cases hz : z ∈ S
    · simp [f, g, hz, norm_bourgainAdditiveCharacter]
    · simp [f, g, hz]
  simpa [bourgainLocalBoxCharacter, f, S] using hf

theorem integral_bourgainLocalBoxCharacterTerm
    {Y L x y : BourgainPhaseSpace}
    (c : ℂ) (hY : ∀ j, 0 < Y j) (hL : ∀ j, 0 < L j)
    (hy : ∀ j, |y j| ≤ Y j) :
    (∫ z : BourgainPhaseSpace,
      bourgainLocalBoxCharacterTerm Y L x y c z) =
      c * bourgainAdditiveCharacter x y := by
  classical
  let S := bourgainLocalBox Y L x
  have hS : MeasurableSet S :=
    measurableSet_bourgainLocalBox Y L x
  rw [show
      bourgainLocalBoxCharacterTerm Y L x y c =
      S.indicator (fun z =>
        c * bourgainProductLocalizationMultiplier Y L y *
          bourgainAdditiveCharacter
            (bourgainCoordinateScale L z) y) by
    funext z
    by_cases hz : z ∈ S
    · simp [bourgainLocalBoxCharacterTerm, S, hz]
    · simp [bourgainLocalBoxCharacterTerm, S, hz]]
  rw [integral_indicator hS, integral_const_mul]
  rw [mul_assoc,
    bourgain_recover_character_from_localBox hY hL hy]

open Classical in
/-- A constant multiple of the localized box character is integrable: the constant factors out of
the indicator. -/
private theorem integrable_const_mul_bourgainLocalBoxCharacter
    (Y L xi yj : BourgainPhaseSpace) (c : ℂ) :
    Integrable (fun z =>
      if z ∈ bourgainLocalBox Y L xi
      then c * bourgainAdditiveCharacter (bourgainCoordinateScale L z) yj
      else 0) := by
  have hbase := integrable_bourgainLocalBoxCharacter Y L xi yj
  have hc :
      (fun z =>
        if z ∈ bourgainLocalBox Y L xi
        then c * bourgainAdditiveCharacter (bourgainCoordinateScale L z) yj
        else 0) =
      fun z => c *
        (if z ∈ bourgainLocalBox Y L xi
         then bourgainAdditiveCharacter (bourgainCoordinateScale L z) yj
         else 0) := by
    funext z
    split_ifs <;> ring
  rw [hc]
  exact hbase.const_mul _


theorem integrable_bourgainBilinearIntegrand
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y L : BourgainPhaseSpace)
    (x : ι → BourgainPhaseSpace) (y : κ → BourgainPhaseSpace)
    (a : ι → ℂ) (b : κ → ℂ) :
    Integrable (fun z =>
      bourgainLocalCoefficientSum Y L x a z *
        bourgainWeightedFourierSum L y
          (bourgainLocalizedFourierWeight Y L y b) z) := by
  classical
  rw [show
      (fun z =>
        bourgainLocalCoefficientSum Y L x a z *
          bourgainWeightedFourierSum L y
            (bourgainLocalizedFourierWeight Y L y b) z) =
      fun z => ∑ i : ι, ∑ j : κ,
        if z ∈ bourgainLocalBox Y L (x i)
        then a i * bourgainLocalizedFourierWeight Y L y b j *
          bourgainAdditiveCharacter
            (bourgainCoordinateScale L z) (y j)
        else 0 by
    funext z
    unfold bourgainLocalCoefficientSum bourgainWeightedFourierSum
      bourgainLocalizedFourierWeight
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hz : z ∈ bourgainLocalBox Y L (x i)
    · simp [hz]
      ring
    · simp [hz]]
  apply integrable_finsetSum
  intro i hi
  apply integrable_finsetSum
  intro j hj
  exact integrable_const_mul_bourgainLocalBoxCharacter Y L (x i) (y j) _

/-- Exact bilinear integral representation. -/
theorem integral_bourgainBilinearIntegrand
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {Y L : BourgainPhaseSpace}
    (x : ι → BourgainPhaseSpace) (y : κ → BourgainPhaseSpace)
    (a : ι → ℂ) (b : κ → ℂ)
    (hY : ∀ j, 0 < Y j) (hL : ∀ j, 0 < L j)
    (hy : ∀ q j, |y q j| ≤ Y j) :
    (∫ z : BourgainPhaseSpace,
      bourgainLocalCoefficientSum Y L x a z *
        bourgainWeightedFourierSum L y
          (bourgainLocalizedFourierWeight Y L y b) z) =
      bourgainBilinearForm x y a b := by
  classical
  rw [show
      (fun z =>
        bourgainLocalCoefficientSum Y L x a z *
          bourgainWeightedFourierSum L y
            (bourgainLocalizedFourierWeight Y L y b) z) =
      fun z => ∑ i : ι, ∑ j : κ,
        if z ∈ bourgainLocalBox Y L (x i)
        then a i * b j *
          bourgainProductLocalizationMultiplier Y L (y j) *
          bourgainAdditiveCharacter
            (bourgainCoordinateScale L z) (y j)
        else 0 by
    funext z
    unfold bourgainLocalCoefficientSum bourgainWeightedFourierSum
      bourgainLocalizedFourierWeight
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hz : z ∈ bourgainLocalBox Y L (x i)
    · simp [hz]
      ring
    · simp [hz]]
  rw [integral_finsetSum]
  · unfold bourgainBilinearForm
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      exact integral_bourgainLocalBoxCharacterTerm
        (a i * b j) hY hL (hy j)
    · intro j hj
      exact integrable_const_mul_bourgainLocalBoxCharacter Y L (x i) (y j) _
  · intro i hi
    apply integrable_finsetSum
    intro j hj
    exact integrable_const_mul_bourgainLocalBoxCharacter Y L (x i) (y j) _

end

end RHTower
