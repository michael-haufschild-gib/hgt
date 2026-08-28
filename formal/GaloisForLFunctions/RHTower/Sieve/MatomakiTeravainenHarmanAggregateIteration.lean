import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanSourceCoefficients
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenMinimalGeometricDilationCertificate
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanRectangularMinorant

/-!
# One repaired iteration per aggregate Harman source

Base/one-prime, complete good-pair, and complete good-triple sources each enter the repaired
iteration once.  This preserves the source's exact signs while avoiding any cell-cardinality loss
in accumulated errors.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction

noncomputable section

def mtHarmanAggregateIterationMainAF {outerDepth recDepth : ℕ}
    (endpoint : ℕ → ℕ) (z Q D : ℕ) (E : ℝ)
    (data : MTFiniteIterationSourceData recDepth) (depth : ℕ)
    (j : Fin (recDepth + 1)) : ArithmeticFunction ℂ :=
  (mtCoefficientAF (mtHarmanBaseOneCoefficient (primesIco z Q)) *
      mtFiniteIterationMain data.truncation data.block data.cutoff depth j) +
    (mtCoefficientAF
        (mtHarmanPairFamilyCoefficient (t := outerDepth)
          endpoint (primesIco z D) E) *
      mtFiniteIterationMain data.truncation data.block data.cutoff depth j) -
    (mtCoefficientAF
        (mtHarmanTripleFamilyCoefficient (t := outerDepth)
          endpoint (primesIco z D) E) *
      mtFiniteIterationMain data.truncation data.block data.cutoff depth j)

def mtHarmanAggregateIterationErrorAF {outerDepth recDepth : ℕ}
    (endpoint : ℕ → ℕ) (z Q D : ℕ) (E : ℝ)
    (data : MTFiniteIterationSourceData recDepth) (depth : ℕ)
    (j : Fin (recDepth + 1)) : ArithmeticFunction ℂ :=
  mtAccumulatedSourceErrorAF data
      (mtCoefficientAF (mtHarmanBaseOneCoefficient (primesIco z Q))) depth j +
    mtAccumulatedSourceErrorAF data
      (mtCoefficientAF
        (mtHarmanPairFamilyCoefficient (t := outerDepth)
          endpoint (primesIco z D) E)) depth j -
    mtAccumulatedSourceErrorAF data
      (mtCoefficientAF
        (mtHarmanTripleFamilyCoefficient (t := outerDepth)
          endpoint (primesIco z D) E)) depth j

/-- Exact simultaneous repaired iteration of all four rectangularized Harman terms. -/
theorem mtHarmanRectangularMinorantMain_eq_aggregateIteration
    {outerDepth recDepth : ℕ} (endpoint : ℕ → ℕ)
    (z Q D E : ℕ) (data : MTFiniteIterationSourceData recDepth)
    (depth : ℕ) (j : Fin (recDepth + 1)) {n N : ℕ}
    (hcutoff : data.cutoff j = z) (hn : 0 < n)
    (hz₀ : 1 < data.z₀) (hnN : n ≤ N)
    (hdepth : depth = Nat.floor (Real.log (N : ℝ) / Real.log (data.z₀ : ℝ))) :
    mtHarmanRectangularMinorantMain (t := outerDepth) endpoint z Q D E n =
      (mtHarmanAggregateIterationMainAF (outerDepth := outerDepth)
          endpoint z Q D (E : ℝ) data depth j +
        mtHarmanAggregateIterationErrorAF (outerDepth := outerDepth)
          endpoint z Q D (E : ℝ) data depth j) n := by
  have hbase := matomakiTeravainen_lemma23ii_terminal_exact data
    (mtHarmanBaseOneCoefficient (primesIco z Q)) j hn hz₀ hnN
  have hpair := matomakiTeravainen_lemma23ii_terminal_exact data
    (mtHarmanPairFamilyCoefficient (t := outerDepth)
      endpoint (primesIco z D) (E : ℝ)) j hn hz₀ hnN
  have htriple := matomakiTeravainen_lemma23ii_terminal_exact data
    (mtHarmanTripleFamilyCoefficient (t := outerDepth)
      endpoint (primesIco z D) (E : ℝ)) j hn hz₀ hnN
  dsimp only at hbase hpair htriple
  rw [hcutoff, ← hdepth] at hbase hpair htriple
  unfold mtHarmanRectangularMinorantMain
  rw [← mtDivisorSiftSum_baseOneCoefficient_eq z Q hn,
    mtHarmanPairCellFamilySiftSum_eq_divisorSiftSum_familyCoefficient
      endpoint (primesIco z D) (E : ℝ) z hn,
    mtHarmanTripleCellFamilySiftSum_eq_divisorSiftSum_familyCoefficient
      endpoint (primesIco z D) (E : ℝ) z hn,
    hbase, hpair, htriple]
  unfold mtHarmanAggregateIterationMainAF mtHarmanAggregateIterationErrorAF
  change (((_ : ℂ) + _) + ((_ : ℂ) + _) - ((_ : ℂ) + _)) =
    (((_ : ℂ) + _ - _) + ((_ : ℂ) + _ - _))
  ring

/-- Squaring the sum of three aggregate iteration errors costs exactly the finite factor three. -/
theorem sum_normSq_mtHarmanAggregateIterationErrorAF_le
    {outerDepth recDepth : ℕ} (A : Finset ℕ) (endpoint : ℕ → ℕ)
    (z Q D : ℕ) (E : ℝ) (data : MTFiniteIterationSourceData recDepth)
    (depth : ℕ) (j : Fin (recDepth + 1)) :
    ∑ n ∈ A, ‖mtHarmanAggregateIterationErrorAF (outerDepth := outerDepth)
        endpoint z Q D E data depth j n‖ ^ 2 ≤
      3 * ∑ n ∈ A, ‖mtAccumulatedSourceErrorAF data
          (mtCoefficientAF (mtHarmanBaseOneCoefficient (primesIco z Q))) depth j n‖ ^ 2 +
      3 * ∑ n ∈ A, ‖mtAccumulatedSourceErrorAF data
          (mtCoefficientAF
            (mtHarmanPairFamilyCoefficient (t := outerDepth)
              endpoint (primesIco z D) E)) depth j n‖ ^ 2 +
      3 * ∑ n ∈ A, ‖mtAccumulatedSourceErrorAF data
          (mtCoefficientAF
            (mtHarmanTripleFamilyCoefficient (t := outerDepth)
              endpoint (primesIco z D) E)) depth j n‖ ^ 2 := by
  let e₀ := mtAccumulatedSourceErrorAF data
    (mtCoefficientAF (mtHarmanBaseOneCoefficient (primesIco z Q))) depth j
  let e₂ := mtAccumulatedSourceErrorAF data
    (mtCoefficientAF
      (mtHarmanPairFamilyCoefficient (t := outerDepth)
        endpoint (primesIco z D) E)) depth j
  let e₃ := mtAccumulatedSourceErrorAF data
    (mtCoefficientAF
      (mtHarmanTripleFamilyCoefficient (t := outerDepth)
        endpoint (primesIco z D) E)) depth j
  calc
    ∑ n ∈ A, ‖mtHarmanAggregateIterationErrorAF (outerDepth := outerDepth)
        endpoint z Q D E data depth j n‖ ^ 2 ≤
      ∑ n ∈ A, (3 * ‖e₀ n‖ ^ 2 + 3 * ‖e₂ n‖ ^ 2 + 3 * ‖e₃ n‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnorm : ‖e₀ n + e₂ n - e₃ n‖ ≤
          ‖e₀ n‖ + ‖e₂ n‖ + ‖e₃ n‖ := by
        calc
          ‖e₀ n + e₂ n - e₃ n‖ ≤
              ‖e₀ n + e₂ n‖ + ‖e₃ n‖ := by
            simpa only [sub_eq_add_neg, norm_neg] using
              norm_add_le (e₀ n + e₂ n) (-e₃ n)
          _ ≤ ‖e₀ n‖ + ‖e₂ n‖ + ‖e₃ n‖ := by
            gcongr
            exact norm_add_le (e₀ n) (e₂ n)
      have hsq : ‖e₀ n + e₂ n - e₃ n‖ ^ 2 ≤
          (‖e₀ n‖ + ‖e₂ n‖ + ‖e₃ n‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      have hthree : (‖e₀ n‖ + ‖e₂ n‖ + ‖e₃ n‖) ^ 2 ≤
          3 * ‖e₀ n‖ ^ 2 + 3 * ‖e₂ n‖ ^ 2 + 3 * ‖e₃ n‖ ^ 2 := by
        nlinarith [sq_nonneg (‖e₀ n‖ - ‖e₂ n‖),
          sq_nonneg (‖e₀ n‖ - ‖e₃ n‖),
          sq_nonneg (‖e₂ n‖ - ‖e₃ n‖)]
      change ‖e₀ n + e₂ n - e₃ n‖ ^ 2 ≤ _
      exact hsq.trans hthree
    _ = 3 * ∑ n ∈ A, ‖e₀ n‖ ^ 2 +
        3 * ∑ n ∈ A, ‖e₂ n‖ ^ 2 +
        3 * ∑ n ∈ A, ‖e₃ n‖ ^ 2 := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ = 3 * ∑ n ∈ A, ‖mtAccumulatedSourceErrorAF data
          (mtCoefficientAF (mtHarmanBaseOneCoefficient (primesIco z Q))) depth j n‖ ^ 2 +
        3 * ∑ n ∈ A, ‖mtAccumulatedSourceErrorAF data
          (mtCoefficientAF
            (mtHarmanPairFamilyCoefficient (t := outerDepth)
              endpoint (primesIco z D) E)) depth j n‖ ^ 2 +
        3 * ∑ n ∈ A, ‖mtAccumulatedSourceErrorAF data
          (mtCoefficientAF
            (mtHarmanTripleFamilyCoefficient (t := outerDepth)
              endpoint (primesIco z D) E)) depth j n‖ ^ 2 := by rfl

end

end RHTower.Sieve
