import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheTranslationPhaseSeparatesTheUnramifiedSquare
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheTranslatedThetaProductReadsThePhasedSquare

/-!
# The translated difference is the unramified square

Pairing opposite frequencies removes the additive phase. The difference
between the full theta square and its translated correlation is exactly
three halves of the contribution outside `3O`.
-/

noncomputable section
open scoped BigOperators Classical

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
  MetaplecticMobiusDescent.CubicEisenstein

/-- The squared coefficient on the unramified source layer. -/
def unramifiedSquareCoeff (h : O) : ℂ :=
  if (3 : O) ∣ h then 0 else rationalSourceResidualFourierCoefficient h ^ 2

theorem summable_translatedDirichlet_term (s : ℂ) (hs : 4 < s.re) :
    Summable (fun h : O => if h = 0 then (0 : ℂ) else translatedCoeff h *
      ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)) := by
  refine Summable.of_norm_bounded (summable_thetaSqDirichlet_term s hs).norm fun h => ?_
  split_ifs with hh
  · rfl
  · simp only [translatedCoeff, norm_mul, norm_pow, tracePhase_norm, mul_one, le_refl]

theorem translatedCoeff_neg (h : O) :
    translatedCoeff (-h) = rationalSourceResidualFourierCoefficient h ^ 2 *
      tracePhase (-(2 * (cuspFrequency h * ringComplex omega))) := by
  rw [translatedCoeff, rationalSourceResidualFourierCoefficient_neg, cuspFrequency_neg,
    neg_mul, mul_neg]

/-- The Fourier selector survives the absolutely convergent Dirichlet sum. -/
theorem thetaSqDirichlet_sub_translated (s : ℂ) (hs : 4 < s.re) :
    thetaSqDirichlet s - besselDirichlet translatedCoeff s =
      (3 / 2 : ℂ) * besselDirichlet unramifiedSquareCoeff s := by
  let F : O → ℂ := fun h => if h = 0 then 0 else
    rationalSourceResidualFourierCoefficient h ^ 2 *
      ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)
  let C : O → ℂ := fun h => if h = 0 then 0 else translatedCoeff h *
    ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)
  have hF : Summable F := summable_thetaSqDirichlet_term s hs
  have hC : Summable C := summable_translatedDirichlet_term s hs
  have hneg : Summable (fun h => C (-h)) := hC.comp_injective neg_injective
  have he : (∑' h, C (-h)) = ∑' h, C h := (Equiv.neg O).tsum_eq C
  change (∑' h, F h) - (∑' h, C h) = _
  calc
    _ = (∑' h, F h) - ((∑' h, C h) + ∑' h, C (-h)) / 2 := by rw [he]; ring
    _ = ∑' h, (F h - (C h + C (-h)) / 2) := by
      rw [← hC.tsum_add hneg, ← tsum_div_const, hF.tsum_sub ((hC.add hneg).div_const 2)]
    _ = ∑' h : O, (3 / 2 : ℂ) * (if h = 0 then 0 else unramifiedSquareCoeff h *
        ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)) := by
      refine tsum_congr fun h => ?_
      by_cases hh : h = 0
      · simp [F, C, hh]
      · simp only [F, C, hh, neg_ne_zero.mpr hh, if_false, cuspFrequency_neg, norm_neg,
          translatedCoeff_neg]
        have hp := thetaSquare_translation_selector h
        change _ = (3 / 2 : ℂ) * ((if (3 : O) ∣ h then 0 else
          rationalSourceResidualFourierCoefficient h ^ 2) * _)
        dsimp only [translatedCoeff]
        linear_combination ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s) * hp
    _ = _ := tsum_mul_left

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
