import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenAlignedOuterBoxFamily
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenSeparatedBoxBoundaryMoment

/-!
# Complete literal box families in product-index form

The post-iteration base, one-prime, pair, and triple mains are reindexed by the same finite product
types consumed by product-scale restriction, collar estimates, and piece classification.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

theorem mtHarmanBaseBoxFamilyAF_eq_sum_outerSeparatedBoxes
    {t : ℕ} (data : MTFiniteIterationSourceData t) (depth : ℕ)
    (j : Fin (t + 1)) (delta : ℝ) (N : ℕ) :
    mtHarmanBaseBoxFamilyAF data depth j delta N =
      ∑ idx ∈ mtOuterSeparatedBoxIndexSet (Finset.univ : Finset (Fin 1))
          data depth j (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N),
        mtOuterSeparatedBoxAF mtBaseOuterAlpha data data.z₀ data.D delta idx := by
  symm
  simpa [mtHarmanBaseBoxFamilyAF, mtBaseOuterAlpha] using
    sum_mtOuterSeparatedBoxAF_eq_sum_mtFiniteMainBoxFamilyAF
      (Finset.univ : Finset (Fin 1)) mtBaseOuterAlpha data depth j delta N

theorem mtHarmanOnePrimeBoxFamilyAF_eq_sum_outerSeparatedBoxes
    {u t : ℕ} (endpoint : ℕ → ℕ) (P : Finset ℕ)
    (data : MTFiniteIterationSourceData t) (depth : ℕ)
    (j : Fin (t + 1)) (delta : ℝ) (N : ℕ) :
    mtHarmanOnePrimeBoxFamilyAF (outerDepth := u)
        endpoint P data depth j delta N =
      ∑ idx ∈ mtOuterSeparatedBoxIndexSet (Finset.univ : Finset (Fin u))
          data depth j (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N),
        mtOuterSeparatedBoxAF (mtOnePrimeOuterAlpha endpoint P)
          data data.z₀ data.D delta idx := by
  symm
  simpa [mtHarmanOnePrimeBoxFamilyAF, mtOnePrimeOuterAlpha] using
    sum_mtOuterSeparatedBoxAF_eq_sum_mtFiniteMainBoxFamilyAF
      (Finset.univ : Finset (Fin u)) (mtOnePrimeOuterAlpha endpoint P)
      data depth j delta N

theorem mtHarmanPairBoxFamilyAF_eq_sum_separatedBoxes
    {u t : ℕ} (endpoint : ℕ → ℕ) (P : Finset ℕ) (E : ℝ)
    (data : MTFiniteIterationSourceData t) (depth : ℕ)
    (j : Fin (t + 1)) (delta : ℝ) (N : ℕ) :
    mtHarmanPairBoxFamilyAF (outerDepth := u)
        endpoint P E data depth j delta N =
      ∑ idx ∈ mtSeparatedPairBoxIndexSet (u := u) endpoint E data depth j
          (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N),
        mtSeparatedPairBoxAF (u := u) endpoint P data data.z₀ data.D delta idx := by
  symm
  simpa [mtHarmanPairBoxFamilyAF, mtSeparatedPairBoxIndexSet,
    mtSeparatedPairBoxAF, mtOuterSeparatedBoxIndexSet, mtOuterSeparatedBoxAF] using
    sum_mtOuterSeparatedBoxAF_eq_sum_mtFiniteMainBoxFamilyAF
      (mtHarmanActiveGoodPairCells (t := u) endpoint E)
      (fun cell => mtHarmanPairCellCoefficient
        (mtHarmanSourceBlock endpoint P cell.1)
        (mtHarmanSourceBlock endpoint P cell.2))
      data depth j delta N

theorem mtHarmanTripleBoxFamilyAF_eq_sum_separatedBoxes
    {u t : ℕ} (endpoint : ℕ → ℕ) (P : Finset ℕ) (E : ℝ)
    (data : MTFiniteIterationSourceData t) (depth : ℕ)
    (j : Fin (t + 1)) (delta : ℝ) (N : ℕ) :
    mtHarmanTripleBoxFamilyAF (outerDepth := u)
        endpoint P E data depth j delta N =
      ∑ idx ∈ mtSeparatedTripleBoxIndexSet (u := u) endpoint E data depth j
          (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N),
        mtSeparatedTripleBoxAF (u := u) endpoint P data data.z₀ data.D delta idx := by
  symm
  simpa [mtHarmanTripleBoxFamilyAF, mtSeparatedTripleBoxIndexSet,
    mtSeparatedTripleBoxAF, mtOuterSeparatedBoxIndexSet, mtOuterSeparatedBoxAF] using
    sum_mtOuterSeparatedBoxAF_eq_sum_mtFiniteMainBoxFamilyAF
      (mtHarmanActiveGoodTripleCells (t := u) endpoint E)
      (fun cell => mtHarmanTripleCellCoefficient
        (mtHarmanSourceBlock endpoint P cell.1.1)
        (mtHarmanSourceBlock endpoint P cell.1.2)
        (mtHarmanSourceBlock endpoint P cell.2))
      data depth j delta N

end

end RHTower.Sieve
