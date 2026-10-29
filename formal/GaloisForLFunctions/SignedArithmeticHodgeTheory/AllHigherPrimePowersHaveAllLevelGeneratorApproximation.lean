import GaloisForLFunctions.SignedArithmeticHodgeTheory.EveryTranslationHasAnAllLevelGammaTailBound
import GaloisForLFunctions.SignedArithmeticHodgeTheory.CriticalEulerCoefficientMassStartsAtCubes

/-!
# One all-level Gamma budget for every cube and higher prime power

The literal critical coefficients of all prime powers of exponent at least
three have finite total mass. The uniform real-lag estimate therefore pays
their complete physical correlation and every finite truncation with the
same original-source Gamma reserve. One generator cutoff works for every
source horizon and every prime-power exhaustion, retaining all dyadic levels.
-/

noncomputable section
open MeasureTheory Set RHTower

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory
open HTGeometry ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry
open ArithmeticIndexDescent

local notation "PP" => Nat.Primes × ℕ
local notation "LineH" => Lp ℂ 2 (volume : Measure ℝ)
local notation "U" => wholeLineLogCellEmbedding
local notation "w₃" => criticalEulerTailWeight 2

/-- The cube-and-higher coefficient is the literal critical weight of its prime-power index. -/
theorem higherEulerWeight_eq (pk : PP) :
    w₃ pk = 2 * ArithmeticFunction.vonMangoldt (higherPrimePowerIndex pk) /
      Real.sqrt (higherPrimePowerIndex pk) := by
  simpa only [higherPrimePowerIndex, Nat.add_assoc, Nat.reduceAdd] using
    criticalEulerTailWeight_eq 2 pk

/-- Total coefficient mass of all critical Euler powers of exponent at least three. -/
def higherEulerCoefficientTotal : ℝ := ∑' pk : PP, w₃ pk

theorem higherEulerCoefficientTotal_nonneg : 0 ≤ higherEulerCoefficientTotal :=
  tsum_nonneg (criticalEulerTailWeight_nonneg 2)

/-- Every finite prime-power selection is charged at most the same complete coefficient mass. -/
theorem sum_higherEulerWeight_le_total (S : Finset PP) :
    ∑ pk ∈ S, w₃ pk ≤ higherEulerCoefficientTotal :=
  (summable_criticalEulerTailWeight_of_two_le (by norm_num : 2 ≤ 2)).sum_le_tsum S
    (fun pk _ => criticalEulerTailWeight_nonneg 2 pk)

/-- The complete physical correlation contribution from all cubes and higher prime powers. -/
def wholeLineHigherEulerCorrelation (F : LineH) : ℝ :=
  ∑' pk : PP, w₃ pk * wholeLineTranslationCorrelation (Real.log (higherPrimePowerIndex pk)) F

/-- An arbitrary finite selection from the same original prime-power source. -/
def wholeLineHigherEulerTruncation (S : Finset PP) (F : LineH) : ℝ :=
  ∑ pk ∈ S, w₃ pk * wholeLineTranslationCorrelation (Real.log (higherPrimePowerIndex pk)) F

private theorem abs_higherEulerTerm_le (pk : PP) (F : LineH) :
    |w₃ pk * wholeLineTranslationCorrelation (Real.log (higherPrimePowerIndex pk)) F| ≤
      w₃ pk * ‖F‖ ^ 2 := by
  rw [abs_mul, abs_of_nonneg (criticalEulerTailWeight_nonneg 2 pk)]
  exact mul_le_mul_of_nonneg_left (abs_wholeLineTranslationCorrelation_le _ F)
    (criticalEulerTailWeight_nonneg 2 pk)

/-- Absolute convergence holds on the entire whole-line L² space, across all primes and powers. -/
theorem summable_norm_wholeLineHigherEuler (F : LineH) :
    Summable (fun pk : PP => ‖w₃ pk *
      wholeLineTranslationCorrelation (Real.log (higherPrimePowerIndex pk)) F‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun pk => ?_)
    ((summable_criticalEulerTailWeight_of_two_le (by norm_num : 2 ≤ 2)).mul_right (‖F‖ ^ 2))
  simpa only [Real.norm_eq_abs] using abs_higherEulerTerm_le pk F

theorem summable_wholeLineHigherEuler (F : LineH) :
    Summable (fun pk : PP => w₃ pk *
      wholeLineTranslationCorrelation (Real.log (higherPrimePowerIndex pk)) F) :=
  (summable_norm_wholeLineHigherEuler F).of_norm

/-- The physical source is the limit of its directed finite prime-power sums. -/
theorem hasSum_wholeLineHigherEuler (F : LineH) :
    HasSum (fun pk : PP => w₃ pk *
      wholeLineTranslationCorrelation (Real.log (higherPrimePowerIndex pk)) F)
      (wholeLineHigherEulerCorrelation F) :=
  (summable_wholeLineHigherEuler F).hasSum

/-- A finite absolute coefficient mass bounds the complete physical correlation on L². -/
theorem abs_wholeLineHigherEulerCorrelation_le (F : LineH) :
    |wholeLineHigherEulerCorrelation F| ≤ higherEulerCoefficientTotal * ‖F‖ ^ 2 := by
  have h := RHTower.abs_tsum_le_tsum_of_abs_le
    ((summable_criticalEulerTailWeight_of_two_le (by norm_num : 2 ≤ 2)).mul_right (‖F‖ ^ 2))
    (fun pk => abs_higherEulerTerm_le pk F)
  rw [tsum_mul_right] at h
  exact h

private theorem abs_higherEulerTerm_head_error_le (pk : PP) (f : ℝ → ℝ)
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) {A : ℕ} (hA : 1 ≤ A) :
    |w₃ pk * wholeLineTranslationCorrelation (Real.log (higherPrimePowerIndex pk))
        (realSourceLp f hv hc) -
      w₃ pk * wholeLineTranslationCorrelation (Real.log (higherPrimePowerIndex pk))
        (realSourceLp f hv hc - wholeLineGeneratorTail A (realSourceLp f hv hc))| ≤
      w₃ pk * (96 * levyEnergy f / (1 + Real.log (A : ℝ))) := by
  rw [← mul_sub, abs_mul, abs_of_nonneg (criticalEulerTailWeight_nonneg 2 pk)]
  exact mul_le_mul_of_nonneg_left (abs_allLevel_translation_head_error_le f hv hc _ hA)
    (criticalEulerTailWeight_nonneg 2 pk)

/-- All higher powers of all primes share one original-source all-level Gamma budget. -/
theorem abs_wholeLineHigherEuler_head_error_le (f : ℝ → ℝ)
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) {A : ℕ} (hA : 1 ≤ A) :
    |wholeLineHigherEulerCorrelation (realSourceLp f hv hc) -
      wholeLineHigherEulerCorrelation
        (realSourceLp f hv hc - wholeLineGeneratorTail A (realSourceLp f hv hc))| ≤
      higherEulerCoefficientTotal * (96 * levyEnergy f / (1 + Real.log (A : ℝ))) := by
  unfold wholeLineHigherEulerCorrelation
  rw [← (summable_wholeLineHigherEuler (realSourceLp f hv hc)).tsum_sub
    (summable_wholeLineHigherEuler
      (realSourceLp f hv hc - wholeLineGeneratorTail A (realSourceLp f hv hc)))]
  have h := RHTower.abs_tsum_le_tsum_of_abs_le
    ((summable_criticalEulerTailWeight_of_two_le (by norm_num : 2 ≤ 2)).mul_right
      (96 * levyEnergy f / (1 + Real.log (A : ℝ))))
    (fun pk => abs_higherEulerTerm_head_error_le pk f hv hc hA)
  rw [tsum_mul_right] at h
  exact h

/-- The same bound is uniform over every finite prime-power selection and every source horizon. -/
theorem abs_wholeLineHigherEulerTruncation_head_error_le (S : Finset PP) (f : ℝ → ℝ)
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) {A : ℕ} (hA : 1 ≤ A) :
    |wholeLineHigherEulerTruncation S (realSourceLp f hv hc) -
      wholeLineHigherEulerTruncation S
        (realSourceLp f hv hc - wholeLineGeneratorTail A (realSourceLp f hv hc))| ≤
      higherEulerCoefficientTotal * (96 * levyEnergy f / (1 + Real.log (A : ℝ))) := by
  have hK : 0 ≤ 96 * levyEnergy f / (1 + Real.log (A : ℝ)) :=
    div_nonneg (mul_nonneg (by norm_num) (levyEnergy_nonneg_bv hv hc))
      (add_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast hA)))
  unfold wholeLineHigherEulerTruncation
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ pk ∈ S, w₃ pk * (96 * levyEnergy f / (1 + Real.log (A : ℝ))) :=
      Finset.sum_le_sum fun pk _ => abs_higherEulerTerm_head_error_le pk f hv hc hA
    _ = (∑ pk ∈ S, w₃ pk) * (96 * levyEnergy f / (1 + Real.log (A : ℝ))) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (sum_higherEulerWeight_le_total S) hK

/-- Every complete correlation term is the integral of the original real BV profile. -/
theorem wholeLineHigherEulerCorrelation_realSource (f : ℝ → ℝ)
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    wholeLineHigherEulerCorrelation (realSourceLp f hv hc) =
      ∑' pk : PP, w₃ pk * ∫ x, f x * f (x + Real.log (higherPrimePowerIndex pk)) := by
  unfold wholeLineHigherEulerCorrelation
  apply tsum_congr
  intro pk
  rw [wholeLineTranslationCorrelation_realSource]

theorem wholeLineHigherEulerTruncation_realSource (S : Finset PP) (f : ℝ → ℝ)
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    wholeLineHigherEulerTruncation S (realSourceLp f hv hc) =
      ∑ pk ∈ S, w₃ pk * ∫ x, f x * f (x + Real.log (higherPrimePowerIndex pk)) := by
  unfold wholeLineHigherEulerTruncation
  exact Finset.sum_congr rfl fun pk _ => congrArg (fun x => w₃ pk * x)
    (wholeLineTranslationCorrelation_realSource f hv hc _)

/-- The literal original-profile integral series is absolutely convergent over all higher powers. -/
theorem summable_norm_original_higherEuler_integrals (f : ℝ → ℝ)
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    Summable (fun pk : PP => ‖w₃ pk *
      ∫ x, f x * f (x + Real.log (higherPrimePowerIndex pk))‖) := by
  simpa only [wholeLineTranslationCorrelation_realSource] using
    summable_norm_wholeLineHigherEuler (realSourceLp f hv hc)

/-- On finite original cell sources, the retained vector is the actual finite-generator head. -/
theorem abs_wholeCell_higherEuler_head_error_le (c : ℕ → ℝ) (X : ℕ)
    {A : ℕ} (hA : 1 ≤ A) :
    |(∑' pk : PP, w₃ pk * ∫ x, wholeCellProfile c X x *
        wholeCellProfile c X (x + Real.log (higherPrimePowerIndex pk))) -
      wholeLineHigherEulerCorrelation
        (U (logCellGeneratorHead A (logCellEmbedding.adjoint (cellSection c 1 X))))| ≤
      higherEulerCoefficientTotal *
        (96 * levyEnergy (wholeCellProfile c X) / (1 + Real.log (A : ℝ))) := by
  have h := abs_wholeLineHigherEuler_head_error_le (wholeCellProfile c X)
    (wholeCellProfile_regular c X).1 (wholeCellProfile_regular c X).2 hA
  rw [wholeLineHigherEulerCorrelation_realSource, realSourceLp_sub_generatorTail_wholeCell] at h
  exact h

theorem abs_wholeCell_higherEulerTruncation_head_error_le (S : Finset PP) (c : ℕ → ℝ) (X : ℕ)
    {A : ℕ} (hA : 1 ≤ A) :
    |(∑ pk ∈ S, w₃ pk * ∫ x, wholeCellProfile c X x *
        wholeCellProfile c X (x + Real.log (higherPrimePowerIndex pk))) -
      wholeLineHigherEulerTruncation S
        (U (logCellGeneratorHead A (logCellEmbedding.adjoint (cellSection c 1 X))))| ≤
      higherEulerCoefficientTotal *
        (96 * levyEnergy (wholeCellProfile c X) / (1 + Real.log (A : ℝ))) := by
  have h := abs_wholeLineHigherEulerTruncation_head_error_le S (wholeCellProfile c X)
    (wholeCellProfile_regular c X).1 (wholeCellProfile_regular c X).2 hA
  rw [wholeLineHigherEulerTruncation_realSource, realSourceLp_sub_generatorTail_wholeCell] at h
  exact h

/-- One generator cutoff pays the whole infinite-prime source and every finite exhaustion stage. -/
theorem exists_allPrimeHigherEuler_allLevel_generator_approximation {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (c : ℕ → ℝ) (X : ℕ),
      (|(∑' pk : PP, w₃ pk * ∫ x, wholeCellProfile c X x *
          wholeCellProfile c X (x + Real.log (higherPrimePowerIndex pk))) -
        wholeLineHigherEulerCorrelation
          (U (logCellGeneratorHead A (logCellEmbedding.adjoint (cellSection c 1 X))))| ≤
        δ * levyEnergy (wholeCellProfile c X)) ∧
      (∀ S : Finset PP,
        |(∑ pk ∈ S, w₃ pk * ∫ x, wholeCellProfile c X x *
            wholeCellProfile c X (x + Real.log (higherPrimePowerIndex pk))) -
          wholeLineHigherEulerTruncation S
            (U (logCellGeneratorHead A (logCellEmbedding.adjoint (cellSection c 1 X))))| ≤
          δ * levyEnergy (wholeCellProfile c X)) := by
  obtain ⟨A, hA⟩ := exists_nat_gt (Real.exp (higherEulerCoefficientTotal * 96 / δ))
  have hA1 : 1 ≤ A := by
    have hp : (0 : ℝ) < A := (Real.exp_pos _).trans hA
    exact Nat.one_le_iff_ne_zero.mpr (Nat.cast_ne_zero.mp hp.ne')
  have hlog : higherEulerCoefficientTotal * 96 / δ < Real.log (A : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos _) hA
    rwa [Real.log_exp] at h
  have hden : 0 < 1 + Real.log (A : ℝ) := by
    have h := Real.log_nonneg (by exact_mod_cast hA1 : (1 : ℝ) ≤ A)
    linarith only [h]
  have hcoef : higherEulerCoefficientTotal * 96 / (1 + Real.log (A : ℝ)) ≤ δ := by
    apply (div_le_iff₀ hden).mpr
    have h := (div_le_iff₀ hδ).mp hlog.le
    nlinarith only [h, hδ]
  refine ⟨A, hA1, fun c X => ?_⟩
  have hE := levyEnergy_nonneg_bv (wholeCellProfile_regular c X).1 (wholeCellProfile_regular c X).2
  have hpay : higherEulerCoefficientTotal *
      (96 * levyEnergy (wholeCellProfile c X) / (1 + Real.log (A : ℝ))) ≤
      δ * levyEnergy (wholeCellProfile c X) := by
    calc
      _ = (higherEulerCoefficientTotal * 96 / (1 + Real.log (A : ℝ))) *
          levyEnergy (wholeCellProfile c X) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hE
  exact ⟨(abs_wholeCell_higherEuler_head_error_le c X hA1).trans hpay,
    fun S => (abs_wholeCell_higherEulerTruncation_head_error_le S c X hA1).trans hpay⟩

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.higherEulerWeight_eq
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.summable_norm_wholeLineHigherEuler
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.hasSum_wholeLineHigherEuler
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.abs_wholeLineHigherEulerTruncation_head_error_le
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.summable_norm_original_higherEuler_integrals
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.abs_wholeCell_higherEuler_head_error_le
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.exists_allPrimeHigherEuler_allLevel_generator_approximation
