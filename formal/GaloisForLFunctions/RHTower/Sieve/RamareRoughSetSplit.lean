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
    (∫ w in E, ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ (2 : ℕ))
      ≤ (1 + δ) * (∫ w in E, ‖ramareBilinear P M w‖ ^ (2 : ℕ))
        + (1 + 1 / δ)
            * (∫ w in E, ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (supportMeanSquareRoughSet P M) w‖ ^ (2 : ℕ)) := by
  classical
  have hcontF : Continuous fun w : ℝ =>
      ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ (2 : ℕ) :=
    ((continuous_logPoly _ _).norm).pow 2
  have hcontB : Continuous fun w : ℝ => ‖ramareBilinear P M w‖ ^ (2 : ℕ) :=
    ((continuous_ramareBilinear P M).norm).pow 2
  have hcontR : Continuous fun w : ℝ =>
      ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (supportMeanSquareRoughSet P M) w‖ ^ (2 : ℕ) :=
    ((continuous_logPoly _ _).norm).pow 2
  set F : ℝ → ℝ := fun w =>
    (1 + δ) * ‖ramareBilinear P M w‖ ^ (2 : ℕ)
      + (1 + 1 / δ) * ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (supportMeanSquareRoughSet P M) w‖ ^ (2 : ℕ) with hFdef
  have hcontMaj : Continuous F := by
    rw [hFdef]
    exact (hcontB.const_mul _).add (hcontR.const_mul _)
  have hle : ∀ w ∈ E,
      ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ (2 : ℕ) ≤ F w := by
    intro w _
    rw [logPoly_moebius_eq_ramare_add_rough hPprime M w, hFdef]
    exact normSq_add_le_weighted _ _ hδ
  have hintF : IntegrableOn (fun w : ℝ =>
      ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ (2 : ℕ)) E volume :=
    (hcontF.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hintMaj : IntegrableOn F E volume :=
    (hcontMaj.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hintB : IntegrableOn (fun w : ℝ => ‖ramareBilinear P M w‖ ^ (2 : ℕ)) E volume :=
    (hcontB.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hintR : IntegrableOn (fun w : ℝ =>
      ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (supportMeanSquareRoughSet P M) w‖ ^ (2 : ℕ)) E volume :=
    (hcontR.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hmono := setIntegral_mono_on hintF hintMaj hEm hle
  refine le_trans hmono (le_of_eq ?_)
  show (∫ w in E, ((1 + δ) * ‖ramareBilinear P M w‖ ^ (2 : ℕ)
      + (1 + 1 / δ) * ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (supportMeanSquareRoughSet P M) w‖ ^ (2 : ℕ))) = _
  rw [integral_add (hintB.const_mul _) (hintR.const_mul _), integral_const_mul,
    integral_const_mul]

/-- The rough polynomial's mean square over a frequency set, from the mean value theorem on the
whole window: only the **count** of rough integers enters, never a short-interval sieve. -/
theorem setIntegral_normSq_logPoly_moebius_roughSet_le {P : Finset ℕ} (M : ℕ) {W : ℝ}
    {E : Set ℝ} (hEs : E ⊆ Set.Icc (-W) W) :
    (∫ w in E, ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (supportMeanSquareRoughSet P M) w‖ ^ (2 : ℕ))
      ≤ ∫ w in Set.Icc (-W) W, ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (supportMeanSquareRoughSet P M) w‖ ^ (2 : ℕ) := by
  have hcontR : Continuous fun w : ℝ =>
      ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (supportMeanSquareRoughSet P M) w‖ ^ (2 : ℕ) :=
    ((continuous_logPoly _ _).norm).pow 2
  exact MeasureTheory.setIntegral_mono_set hcontR.integrableOn_Icc
    (Filter.Eventually.of_forall fun w => by positivity)
    (Filter.Eventually.of_forall hEs)

/-- **The rough polynomial's mean square, with the rough count discharged by Turán's bound.**  Only
the harmonic mass of the designated range enters: the rough integers have density `1/A`, and the
prime-counting correction `2|P|/A` is harmless whenever the range is shorter than the sum. -/
theorem integral_Icc_normSq_roughPoly_le_harmonic {P : Finset ℕ} (hPprime : ∀ p ∈ P, p.Prime)
    (M : ℕ) {W : ℝ} (hW : 1 ≤ W) (hA : 0 < ∑ p ∈ P, (1 : ℝ) / (p : ℝ)) :
    (∫ w in Set.Icc (-W) W, ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (supportMeanSquareRoughSet P M) w‖ ^ (2 : ℕ))
      ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ))
          * ((M : ℝ) / (∑ p ∈ P, (1 : ℝ) / (p : ℝ))
            + 2 * (P.card : ℝ) / (∑ p ∈ P, (1 : ℝ) / (p : ℝ))) := by
  have hW0 : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW
  have hcoef : (0 : ℝ) ≤ 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ) := by
    have := Real.pi_pos
    have := (Real.exp_pos 1).le
    have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
    positivity
  refine le_trans (integral_Icc_normSq_roughPoly_le P M hW) ?_
  exact mul_le_mul_of_nonneg_left (card_roughSet_le hPprime M hA) hcoef

end

end RHTower.Sieve
