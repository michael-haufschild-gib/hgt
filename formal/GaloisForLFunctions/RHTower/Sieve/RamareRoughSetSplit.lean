import GaloisForLFunctions.RHTower.Sieve.RamareSquareMultiple

/-!
# The exact Ramaré decomposition of the Möbius mean square over a frequency set

`Sieve/RamareSquareMultiple.logPoly_moebius_eq_ramare_add_rough` is a pointwise identity, so it can
be integrated over **any** measurable set of frequencies, not only over a symmetric interval.  That
is what lets two different designated prime ranges be used on two different frequency sets: the
decomposition is never global, and the rough polynomial of each range is paid only where that range
is actually used.
-/

namespace RHTower.Sieve

open Finset MeasureTheory
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- **The Möbius mean square over a frequency set, split by a designated prime range.** -/
theorem setIntegral_normSq_logPoly_moebius_le_ramare_rough {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) (M : ℕ) {W δ : ℝ} (hδ : 0 < δ)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W) :
    (∫ w in E, ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2)
      ≤ (1 + δ) * (∫ w in E, ‖ramareBilinear P M w‖ ^ 2)
        + (1 + 1 / δ)
            * (∫ w in E, ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (roughSet P M) w‖ ^ 2) := by
  classical
  have hcontF : Continuous fun w : ℝ =>
      ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2 :=
    ((continuous_logPoly _ _).norm).pow 2
  have hcontB : Continuous fun w : ℝ => ‖ramareBilinear P M w‖ ^ 2 :=
    ((continuous_ramareBilinear P M).norm).pow 2
  have hcontR : Continuous fun w : ℝ =>
      ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (roughSet P M) w‖ ^ 2 :=
    ((continuous_logPoly _ _).norm).pow 2
  set F : ℝ → ℝ := fun w =>
    (1 + δ) * ‖ramareBilinear P M w‖ ^ 2
      + (1 + 1 / δ) * ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (roughSet P M) w‖ ^ 2 with hFdef
  have hcontMaj : Continuous F := by
    rw [hFdef]
    exact (hcontB.const_mul _).add (hcontR.const_mul _)
  have hle : ∀ w ∈ E,
      ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2 ≤ F w := by
    intro w _
    rw [logPoly_moebius_eq_ramare_add_rough hPprime M w, hFdef]
    exact normSq_add_le_weighted _ _ hδ
  have hintF : IntegrableOn (fun w : ℝ =>
      ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2) E volume :=
    (hcontF.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hintMaj : IntegrableOn F E volume :=
    (hcontMaj.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hintB : IntegrableOn (fun w : ℝ => ‖ramareBilinear P M w‖ ^ 2) E volume :=
    (hcontB.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hintR : IntegrableOn (fun w : ℝ =>
      ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (roughSet P M) w‖ ^ 2) E volume :=
    (hcontR.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hmono := setIntegral_mono_on hintF hintMaj hEm hle
  refine le_trans hmono (le_of_eq ?_)
  show (∫ w in E, ((1 + δ) * ‖ramareBilinear P M w‖ ^ 2
      + (1 + 1 / δ) * ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (roughSet P M) w‖ ^ 2)) = _
  rw [integral_add (hintB.const_mul _) (hintR.const_mul _), integral_const_mul,
    integral_const_mul]

/-- The rough polynomial's mean square over a frequency set, from the mean value theorem on the
whole window: only the **count** of rough integers enters, never a short-interval sieve. -/
theorem setIntegral_normSq_logPoly_moebius_roughSet_le {P : Finset ℕ} (M : ℕ) {W : ℝ}
    {E : Set ℝ} (hEs : E ⊆ Set.Icc (-W) W) :
    (∫ w in E, ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (roughSet P M) w‖ ^ 2)
      ≤ ∫ w in Set.Icc (-W) W, ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (roughSet P M) w‖ ^ 2 := by
  have hcontR : Continuous fun w : ℝ =>
      ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (roughSet P M) w‖ ^ 2 :=
    ((continuous_logPoly _ _).norm).pow 2
  exact MeasureTheory.setIntegral_mono_set hcontR.integrableOn_Icc
    (Filter.Eventually.of_forall fun w => by positivity)
    (Filter.Eventually.of_forall hEs)

end

end RHTower.Sieve
