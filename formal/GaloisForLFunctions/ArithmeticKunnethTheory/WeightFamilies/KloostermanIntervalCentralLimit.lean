import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.KloostermanArithmeticCentralLimit
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.PrimeResiduePhaseCompletion

/-!
# Arithmetic Kloosterman laws on incomplete intervals

The characteristic function on an interval of length `N+1` differs from its
complete-period law by at most `2P/(N+1)`, uniformly in the starting point.
For the first `n` primes of any enumeration, windows of length
`(n+1)P + R + 1` therefore retain the Gaussian limit for arbitrary translations
and arbitrary nonnegative additional lengths `R`.
-/

open Finset MeasureTheory ProbabilityTheory Filter Complex
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticHarmonicAnalysis
open scoped ENNReal Topology

namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
noncomputable section

/-- The empirical law on the integer interval from `A` through `A+N`. -/
def arithmeticKloostermanIntervalLaw (S : Finset Nat.Primes) (A N : ℕ) : Measure ℝ :=
  ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ •
    ∑ a : Fin (N + 1), Measure.dirac (arithmeticKloostermanSum S (A + a))

instance (S : Finset Nat.Primes) (A N : ℕ) :
    IsProbabilityMeasure (arithmeticKloostermanIntervalLaw S A N) := by
  constructor
  simpa [arithmeticKloostermanIntervalLaw, Measure.coe_finsetSum] using
    (ENNReal.inv_mul_cancel (a := ((N + 1 : ℕ) : ℝ≥0∞)) (by simp) (by simp))

/-- Finite interval sampling makes every test function integrable. -/
theorem integrable_arithmeticKloostermanIntervalLaw (S : Finset Nat.Primes) (A N : ℕ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) :
    Integrable f (arithmeticKloostermanIntervalLaw S A N) := by
  apply Integrable.smul_measure _ (by simp : ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ ≠ ⊤)
  exact integrable_finsetSum_measure.mpr fun _ _ => integrable_dirac (by simp)

/-- Interval averaging retains every atom with its parameter multiplicity. -/
theorem integral_arithmeticKloostermanIntervalLaw (S : Finset Nat.Primes) (A N : ℕ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E) :
    ∫ x, f x ∂arithmeticKloostermanIntervalLaw S A N = ((N + 1 : ℕ) : ℝ)⁻¹ •
      ∑ a : Fin (N + 1), f (arithmeticKloostermanSum S (A + a)) := by
  rw [arithmeticKloostermanIntervalLaw, integral_smul_measure,
    integral_finsetSum_measure (fun _ _ => integrable_dirac (by simp))]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- The exponential of the normalized sum is a product of local unit phases. -/
theorem exp_arithmeticKloostermanSum_eq_phase (S : Finset Nat.Primes) (t : ℝ) (a : ℕ) :
    cexp ((t : ℂ) * (arithmeticKloostermanSum S a : ℂ) * I) =
      primeResiduePhase S
        (fun p r => ((Real.sqrt S.card)⁻¹ * t) * standardizedKloostermanTrace p r) a := by
  rw [primeResiduePhase, ← Complex.exp_sum]
  congr 1
  simp only [arithmeticKloostermanSum, Complex.ofReal_mul, Complex.ofReal_sum,
    Finset.mul_sum, Finset.sum_mul]
  apply sum_congr rfl
  intro p _
  ring

theorem primeResiduePhaseMean_kloosterman (S : Finset Nat.Primes) (t : ℝ) :
    primeResiduePhaseMean S
      (fun p r => ((Real.sqrt S.card)⁻¹ * t) * standardizedKloostermanTrace p r) =
        charFun (arithmeticKloostermanLaw S) t := by
  rw [charFun_arithmeticKloostermanLaw, primeResiduePhaseMean]
  apply prod_congr rfl
  intro p _
  rw [charFun_apply_real, integral_primeKloostermanLaw]
  simp [Algebra.smul_def, inv_mul_eq_div]

theorem charFun_arithmeticKloostermanIntervalLaw (S : Finset Nat.Primes)
    (A N : ℕ) (t : ℝ) :
    charFun (arithmeticKloostermanIntervalLaw S A N) t =
      (∑ n ∈ Ico A (A + (N + 1)), primeResiduePhase S
        (fun p r => ((Real.sqrt S.card)⁻¹ * t) * standardizedKloostermanTrace p r) n) /
          ((N + 1 : ℕ) : ℂ) := by
  rw [charFun_apply_real, integral_arithmeticKloostermanIntervalLaw]
  simp only [exp_arithmeticKloostermanSum_eq_phase, Fin.sum_univ_eq_sum_range,
    sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  simp [Algebra.smul_def, inv_mul_eq_div]

/-- The sampling-window error is uniform in frequency and interval location. -/
theorem norm_charFun_arithmeticKloostermanIntervalLaw_sub
    (S : Finset Nat.Primes) (A N : ℕ) (t : ℝ) :
    ‖charFun (arithmeticKloostermanIntervalLaw S A N) t -
      charFun (arithmeticKloostermanLaw S) t‖ ≤
        2 * (primeSetProduct S : ℝ) / (N + 1) := by
  rw [charFun_arithmeticKloostermanIntervalLaw, ← primeResiduePhaseMean_kloosterman]
  exact norm_average_primeResiduePhase_sub_mean S _ A N

/-- Windows containing an increasing number of complete periods have Gaussian characteristic limits. -/
theorem tendsto_charFun_arithmeticKloostermanIntervalLaw
    (e : ℕ ≃ Nat.Primes) (A R : ℕ → ℕ) (t : ℝ) :
    Tendsto (fun n : ℕ => charFun
      (arithmeticKloostermanIntervalLaw (HTGeometry.sievePrefix e n) (A n)
        ((n + 1) * primeSetProduct (HTGeometry.sievePrefix e n) + R n)) t)
      atTop (𝓝 (cexp (-(t : ℂ) ^ 2 / 2))) := by
  have hrate : Tendsto (fun n : ℕ => (2 : ℝ) / n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, div_eq_mul_inv] using
      (tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (2 : ℝ)
  have hdiff : Tendsto (fun n : ℕ => charFun
      (arithmeticKloostermanIntervalLaw (HTGeometry.sievePrefix e n) (A n)
        ((n + 1) * primeSetProduct (HTGeometry.sievePrefix e n) + R n)) t -
      charFun (arithmeticKloostermanLaw (HTGeometry.sievePrefix e n)) t)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hrate
    filter_upwards [eventually_ge_atTop 1] with n hn
    refine (norm_charFun_arithmeticKloostermanIntervalLaw_sub
      (HTGeometry.sievePrefix e n) (A n) _ t).trans ?_
    have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hP : (0 : ℝ) < primeSetProduct (HTGeometry.sievePrefix e n) := by
      exact_mod_cast primeSetProduct_pos (HTGeometry.sievePrefix e n)
    apply (div_le_div_iff₀ (by positivity) hnR).mpr
    push_cast
    nlinarith only [hP, Nat.cast_nonneg (R n)]
  have href : Tendsto (fun n : ℕ =>
      charFun (arithmeticKloostermanLaw (HTGeometry.sievePrefix e n)) t)
      atTop (𝓝 (cexp (-(t : ℂ) ^ 2 / 2))) := by
    simpa only [charFun_arithmeticKloostermanLaw_prefix] using
      tendsto_charFun_kloosterman_normalized_sum e t
  simpa only [sub_add_cancel, zero_add] using hdiff.add href

/-- Gaussian convergence survives arbitrary interval translations and additional samples. -/
theorem tendstoInDistribution_arithmeticKloostermanIntervalLaw
    (e : ℕ ≃ Nat.Primes) (A R : ℕ → ℕ) :
    TendstoInDistribution (fun _ : ℕ => (id : ℝ → ℝ)) atTop (id : ℝ → ℝ)
      (fun n => arithmeticKloostermanIntervalLaw (HTGeometry.sievePrefix e n) (A n)
        ((n + 1) * primeSetProduct (HTGeometry.sievePrefix e n) + R n))
      (gaussianReal 0 1) where
  forall_aemeasurable _ := aemeasurable_id
  tendsto := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
    simpa [Measure.map_id, charFun_gaussianReal, neg_div] using
      tendsto_charFun_arithmeticKloostermanIntervalLaw e A R t

#print axioms norm_charFun_arithmeticKloostermanIntervalLaw_sub
#print axioms tendstoInDistribution_arithmeticKloostermanIntervalLaw

end
end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
