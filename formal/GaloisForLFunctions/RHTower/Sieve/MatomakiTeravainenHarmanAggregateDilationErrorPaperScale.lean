import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanAggregateIteration
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenGridFreeDilation

/-!
# Paper-scale aggregate iteration error at an independent summation endpoint

The aggregate Harman error is a signed sum of three accumulated source errors.  Its recursion depth
and mean-square summation endpoint need not coincide; this form is used to measure the final error
on its full coarse support while retaining the identity's literal terminal depth.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction

noncomputable section

/-- Aggregate iteration error with independent depth and summation endpoint. -/
theorem eventually_sum_normSq_mtHarmanAggregateIterationErrorAF_dilation_le_paper
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ {t outerDepth : ℕ} (endpoint : ℕ → ℕ) (z Q D : ℕ) (E : ℝ)
        (data : MTFiniteIterationSourceData t)
        (_cert : MTGridFreeDilationCertificate data A X)
        (J : ℕ) (j : Fin (t + 1)) (Y : ℕ),
      (∀ i, 1 ≤ endpoint i) → Monotone endpoint →
      1 ≤ Y → (Y : ℝ) ≤ 4 * X → (J : ℝ) ≤ Real.log X →
      ∑ n ∈ Finset.Icc 1 Y,
          ‖mtHarmanAggregateIterationErrorAF (outerDepth := outerDepth)
            endpoint z Q D E data J j n‖ ^ 2 ≤
        225 * (Y : ℝ) *
          (Real.log X) ^ (-((2 * A : ℕ) : ℝ)) := by
  filter_upwards [eventually_sum_norm_sq_mtAccumulatedSourceErrorAF_dilation_final A hA]
      with X hfinal
  intro t outerDepth endpoint z Q D E data _cert J j Y hendpoint hmono hY hYX hJ
  have hbaseCoeff : ∀ {m : ℕ}, 0 < m →
      ‖mtCoefficientAF (mtHarmanBaseOneCoefficient (primesIco z Q)) m‖ ≤ 1 := by
    intro m hm
    rw [mtCoefficientAF_apply_of_pos _ hm]
    exact norm_mtHarmanBaseOneCoefficient_le_one (one_not_mem_primesIco z Q) m
  have hpairCoeff : ∀ {m : ℕ}, 0 < m →
      ‖mtCoefficientAF
        (mtHarmanPairFamilyCoefficient (t := outerDepth)
          endpoint (primesIco z D) E) m‖ ≤ 1 := by
    intro m hm
    rw [mtCoefficientAF_apply_of_pos _ hm]
    exact norm_mtHarmanPairFamilyCoefficient_le_one
      hendpoint hmono (primesIco z D) E m
  have htripleCoeff : ∀ {m : ℕ}, 0 < m →
      ‖mtCoefficientAF
        (mtHarmanTripleFamilyCoefficient (t := outerDepth)
          endpoint (primesIco z D) E) m‖ ≤ 1 := by
    intro m hm
    rw [mtCoefficientAF_apply_of_pos _ hm]
    exact norm_mtHarmanTripleFamilyCoefficient_le_one
      hendpoint hmono (primesIco z D) E m
  have hbase := hfinal t data _cert
    (mtCoefficientAF (mtHarmanBaseOneCoefficient (primesIco z Q))) J j Y 1
    hY hYX hJ (by norm_num) hbaseCoeff
  have hpair := hfinal t data _cert
    (mtCoefficientAF (mtHarmanPairFamilyCoefficient (t := outerDepth)
      endpoint (primesIco z D) E)) J j Y 1
    hY hYX hJ (by norm_num) hpairCoeff
  have htriple := hfinal t data _cert
    (mtCoefficientAF (mtHarmanTripleFamilyCoefficient (t := outerDepth)
      endpoint (primesIco z D) E)) J j Y 1
    hY hYX hJ (by norm_num) htripleCoeff
  have haggregate := sum_normSq_mtHarmanAggregateIterationErrorAF_le
    (outerDepth := outerDepth) (Finset.Icc 1 Y)
    endpoint z Q D E data J j
  calc
    ∑ n ∈ Finset.Icc 1 Y,
        ‖mtHarmanAggregateIterationErrorAF (outerDepth := outerDepth)
          endpoint z Q D E data J j n‖ ^ 2 ≤
      3 * ∑ n ∈ Finset.Icc 1 Y,
          ‖mtAccumulatedSourceErrorAF data
            (mtCoefficientAF (mtHarmanBaseOneCoefficient (primesIco z Q)))
            J j n‖ ^ 2 +
      3 * ∑ n ∈ Finset.Icc 1 Y,
          ‖mtAccumulatedSourceErrorAF data
            (mtCoefficientAF (mtHarmanPairFamilyCoefficient (t := outerDepth)
              endpoint (primesIco z D) E)) J j n‖ ^ 2 +
      3 * ∑ n ∈ Finset.Icc 1 Y,
          ‖mtAccumulatedSourceErrorAF data
            (mtCoefficientAF (mtHarmanTripleFamilyCoefficient (t := outerDepth)
              endpoint (primesIco z D) E)) J j n‖ ^ 2 := haggregate
    _ ≤ 225 * (Y : ℝ) *
        (Real.log X) ^ (-((2 * A : ℕ) : ℝ)) := by
      norm_num at hbase hpair htriple
      push_cast at hbase hpair htriple ⊢
      nlinarith

end

end RHTower.Sieve
