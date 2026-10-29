import GaloisForLFunctions.SignedArithmeticHodgeTheory.EveryTranslationHasAnAllLevelGammaTailBound
import GaloisForLFunctions.ArithmeticIndexDescent.EveryFixedEulerMixedSourceIsGammaSmall

/-!
# All-level generator approximation for complete finite Euler families

The original-source Gamma tail bound is uniform in the real translation
lag. Each prime's literal critical Euler weights are summable, so every
fixed finite prime family has one generator cutoff at every source horizon.
All powers and every dyadic level remain present. The cost is the sum of
the exact Euler coefficient masses; no all-prime summability is asserted.
-/

noncomputable section
open MeasureTheory Set RHTower
open scoped InnerProductSpace

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory
open HTGeometry ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry
open ArithmeticIndexDescent

local notation "LineH" => Lp ℂ 2 (volume : Measure ℝ)
local notation "U" => wholeLineLogCellEmbedding

/-- The complete critical Euler correlation of one prime in physical whole-line L². -/
def wholeLinePrimeEulerCorrelation (p : Nat.Primes) (F : LineH) : ℝ :=
  ∑' k : ℕ, primePowerMixedWeight p k *
    wholeLineTranslationCorrelation (Real.log (((p : ℕ) ^ (k + 1) : ℕ) : ℝ)) F

private theorem abs_wholeLinePrimeEulerTerm_le (p : Nat.Primes) (k : ℕ) (F : LineH) :
    |primePowerMixedWeight p k *
      wholeLineTranslationCorrelation (Real.log (((p : ℕ) ^ (k + 1) : ℕ) : ℝ)) F| ≤
      primePowerMixedWeight p k * ‖F‖ ^ 2 := by
  rw [abs_mul, abs_of_nonneg (primePowerMixedWeight_nonneg p k)]
  exact mul_le_mul_of_nonneg_left (abs_wholeLineTranslationCorrelation_le _ F)
    (primePowerMixedWeight_nonneg p k)

/-- Every physical Euler series is absolutely convergent before any head subtraction. -/
theorem summable_norm_wholeLinePrimeEuler (p : Nat.Primes) (F : LineH) :
    Summable (fun k : ℕ => ‖primePowerMixedWeight p k *
      wholeLineTranslationCorrelation (Real.log (((p : ℕ) ^ (k + 1) : ℕ) : ℝ)) F‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    ((hasSum_primePowerMixedWeight p).summable.mul_right (‖F‖ ^ 2))
  simpa only [Real.norm_eq_abs] using abs_wholeLinePrimeEulerTerm_le p k F

theorem summable_wholeLinePrimeEuler (p : Nat.Primes) (F : LineH) :
    Summable (fun k : ℕ => primePowerMixedWeight p k *
      wholeLineTranslationCorrelation (Real.log (((p : ℕ) ^ (k + 1) : ℕ) : ℝ)) F) :=
  (summable_norm_wholeLinePrimeEuler p F).of_norm

/-- The exact geometric coefficient mass bounds the full physical Euler correlation. -/
theorem abs_wholeLinePrimeEulerCorrelation_le (p : Nat.Primes) (F : LineH) :
    |wholeLinePrimeEulerCorrelation p F| ≤ primeEulerMixedWeightTotal p * ‖F‖ ^ 2 := by
  have h := RHTower.abs_tsum_le_tsum_of_abs_le
    ((hasSum_primePowerMixedWeight p).summable.mul_right (‖F‖ ^ 2))
    (fun k => abs_wholeLinePrimeEulerTerm_le p k F)
  rw [tsum_mul_right, (hasSum_primePowerMixedWeight p).tsum_eq] at h
  exact h

/-- All powers of one prime share the original profile's all-level Gamma budget. -/
theorem abs_wholeLinePrimeEuler_head_error_le (p : Nat.Primes) (f : ℝ → ℝ)
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) {A : ℕ} (hA : 1 ≤ A) :
    |wholeLinePrimeEulerCorrelation p (realSourceLp f hv hc) -
      wholeLinePrimeEulerCorrelation p
        (realSourceLp f hv hc - wholeLineGeneratorTail A (realSourceLp f hv hc))| ≤
      primeEulerMixedWeightTotal p * (96 * levyEnergy f / (1 + Real.log (A : ℝ))) := by
  let F := realSourceLp f hv hc
  let G := F - wholeLineGeneratorTail A F
  let K := 96 * levyEnergy f / (1 + Real.log (A : ℝ))
  change |wholeLinePrimeEulerCorrelation p F - wholeLinePrimeEulerCorrelation p G| ≤ _
  unfold wholeLinePrimeEulerCorrelation
  rw [← (summable_wholeLinePrimeEuler p F).tsum_sub (summable_wholeLinePrimeEuler p G)]
  have ht (k : ℕ) : |primePowerMixedWeight p k *
      wholeLineTranslationCorrelation (Real.log (((p : ℕ) ^ (k + 1) : ℕ) : ℝ)) F -
      primePowerMixedWeight p k *
      wholeLineTranslationCorrelation (Real.log (((p : ℕ) ^ (k + 1) : ℕ) : ℝ)) G| ≤
      primePowerMixedWeight p k * K := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (primePowerMixedWeight_nonneg p k)]
    exact mul_le_mul_of_nonneg_left (abs_allLevel_translation_head_error_le f hv hc _ hA)
      (primePowerMixedWeight_nonneg p k)
  have h := RHTower.abs_tsum_le_tsum_of_abs_le
    ((hasSum_primePowerMixedWeight p).summable.mul_right K) ht
  rw [tsum_mul_right, (hasSum_primePowerMixedWeight p).tsum_eq] at h
  exact h

/-- The physical Euler functional reads the literal integral of the original BV profile. -/
theorem wholeLinePrimeEulerCorrelation_realSource (p : Nat.Primes) (f : ℝ → ℝ)
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    wholeLinePrimeEulerCorrelation p (realSourceLp f hv hc) =
      ∑' k : ℕ, primePowerMixedWeight p k *
        ∫ x, f x * f (x + Real.log (((p : ℕ) ^ (k + 1) : ℕ) : ℝ)) := by
  unfold wholeLinePrimeEulerCorrelation
  apply tsum_congr
  intro k
  rw [wholeLineTranslationCorrelation_realSource]

/-- Absolute convergence also holds for the original literal profile-integral series. -/
theorem summable_norm_original_primeEuler_integrals (p : Nat.Primes) (f : ℝ → ℝ)
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    Summable (fun k : ℕ => ‖primePowerMixedWeight p k *
      ∫ x, f x * f (x + Real.log (((p : ℕ) ^ (k + 1) : ℕ) : ℝ))‖) := by
  simpa only [wholeLineTranslationCorrelation_realSource] using
    summable_norm_wholeLinePrimeEuler p (realSourceLp f hv hc)

/-- Complete Euler correlations for a fixed finite set of primes. -/
def wholeLineFiniteEulerCorrelation (P : Finset Nat.Primes) (F : LineH) : ℝ :=
  ∑ p ∈ P, wholeLinePrimeEulerCorrelation p F

/-- The exact sum of all critical coefficient masses in a finite prime family. -/
def finiteEulerCorrelationWeightTotal (P : Finset Nat.Primes) : ℝ :=
  ∑ p ∈ P, primeEulerMixedWeightTotal p

theorem finiteEulerCorrelationWeightTotal_nonneg (P : Finset Nat.Primes) :
    0 ≤ finiteEulerCorrelationWeightTotal P :=
  Finset.sum_nonneg fun p _ => primeEulerMixedWeightTotal_nonneg p

/-- One all-level high-tail payment controls every complete Euler factor in a finite family. -/
theorem abs_wholeLineFiniteEuler_head_error_le (P : Finset Nat.Primes) (f : ℝ → ℝ)
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) {A : ℕ} (hA : 1 ≤ A) :
    |wholeLineFiniteEulerCorrelation P (realSourceLp f hv hc) -
      wholeLineFiniteEulerCorrelation P
        (realSourceLp f hv hc - wholeLineGeneratorTail A (realSourceLp f hv hc))| ≤
      finiteEulerCorrelationWeightTotal P * (96 * levyEnergy f / (1 + Real.log (A : ℝ))) := by
  unfold wholeLineFiniteEulerCorrelation
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ p ∈ P, primeEulerMixedWeightTotal p *
        (96 * levyEnergy f / (1 + Real.log (A : ℝ))) :=
      Finset.sum_le_sum fun p _ => abs_wholeLinePrimeEuler_head_error_le p f hv hc hA
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- The finite Euler family is exactly the sum of its original profile-integral series. -/
theorem wholeLineFiniteEulerCorrelation_realSource (P : Finset Nat.Primes) (f : ℝ → ℝ)
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    wholeLineFiniteEulerCorrelation P (realSourceLp f hv hc) =
      ∑ p ∈ P, ∑' k : ℕ, primePowerMixedWeight p k *
        ∫ x, f x * f (x + Real.log (((p : ℕ) ^ (k + 1) : ℕ) : ℝ)) := by
  exact Finset.sum_congr rfl fun p _ => wholeLinePrimeEulerCorrelation_realSource p f hv hc

/-- On finite cell profiles the retained vector consists of finitely many entire generator orbits. -/
theorem abs_wholeCell_finiteEuler_head_error_le (P : Finset Nat.Primes) (c : ℕ → ℝ) (X : ℕ)
    {A : ℕ} (hA : 1 ≤ A) :
    |(∑ p ∈ P, ∑' k : ℕ, primePowerMixedWeight p k *
        ∫ x, wholeCellProfile c X x *
          wholeCellProfile c X (x + Real.log (((p : ℕ) ^ (k + 1) : ℕ) : ℝ))) -
      wholeLineFiniteEulerCorrelation P
        (U (logCellGeneratorHead A (logCellEmbedding.adjoint (cellSection c 1 X))))| ≤
      finiteEulerCorrelationWeightTotal P *
        (96 * levyEnergy (wholeCellProfile c X) / (1 + Real.log (A : ℝ))) := by
  have h := abs_wholeLineFiniteEuler_head_error_le P (wholeCellProfile c X)
    (wholeCellProfile_regular c X).1 (wholeCellProfile_regular c X).2 hA
  rw [wholeLineFiniteEulerCorrelation_realSource, realSourceLp_sub_generatorTail_wholeCell] at h
  exact h

/-- One generator cutoff makes a fixed finite Euler family Gamma-small, uniformly in the original source. -/
theorem exists_finiteEuler_allLevel_generator_approximation (P : Finset Nat.Primes)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (c : ℕ → ℝ) (X : ℕ),
      |(∑ p ∈ P, ∑' k : ℕ, primePowerMixedWeight p k *
          ∫ x, wholeCellProfile c X x *
            wholeCellProfile c X (x + Real.log (((p : ℕ) ^ (k + 1) : ℕ) : ℝ))) -
        wholeLineFiniteEulerCorrelation P
          (U (logCellGeneratorHead A (logCellEmbedding.adjoint (cellSection c 1 X))))| ≤
        δ * levyEnergy (wholeCellProfile c X) := by
  obtain ⟨A, hA⟩ := exists_nat_gt (Real.exp (finiteEulerCorrelationWeightTotal P * 96 / δ))
  have hA1 : 1 ≤ A := by
    have hp : (0 : ℝ) < A := (Real.exp_pos _).trans hA
    exact Nat.one_le_iff_ne_zero.mpr (Nat.cast_ne_zero.mp hp.ne')
  have hlog : finiteEulerCorrelationWeightTotal P * 96 / δ < Real.log (A : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos _) hA
    rwa [Real.log_exp] at h
  have hden : 0 < 1 + Real.log (A : ℝ) := by
    have h := Real.log_nonneg (by exact_mod_cast hA1 : (1 : ℝ) ≤ A)
    linarith only [h]
  have hcoef : finiteEulerCorrelationWeightTotal P * 96 / (1 + Real.log (A : ℝ)) ≤ δ := by
    apply (div_le_iff₀ hden).mpr
    have h := (div_le_iff₀ hδ).mp hlog.le
    nlinarith only [h, hδ]
  refine ⟨A, hA1, fun c X => ?_⟩
  have hE := levyEnergy_nonneg_bv (wholeCellProfile_regular c X).1 (wholeCellProfile_regular c X).2
  calc
    _ ≤ _ := abs_wholeCell_finiteEuler_head_error_le P c X hA1
    _ = (finiteEulerCorrelationWeightTotal P * 96 / (1 + Real.log (A : ℝ))) *
        levyEnergy (wholeCellProfile c X) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hE

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.summable_norm_wholeLinePrimeEuler
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.abs_wholeLinePrimeEuler_head_error_le
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.wholeLineFiniteEulerCorrelation_realSource
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.summable_norm_original_primeEuler_integrals
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.abs_wholeCell_finiteEuler_head_error_le
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.exists_finiteEuler_allLevel_generator_approximation
