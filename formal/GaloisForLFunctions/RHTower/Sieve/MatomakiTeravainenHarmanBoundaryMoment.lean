import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenRetainedBoxDecomposition
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenAlignedOuterBoxFamily
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenSeparatedBoxBoundaryMomentGeneric

/-!
# Mean square of the complete Harman product boundary

The four signed families are controlled before summation by generalized-divisor orders
`4,4,5,6`.  Squaring their signed sum costs only the fixed factor four.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

noncomputable section

local instance instDecidableEqMTTripleSeparatedBoxIndexHarmanBoundary (u t : ℕ) :
    DecidableEq (MTTripleSeparatedBoxIndex u t) := Classical.decEq _

theorem sum_normSq_sub_add_sub_le_four
    (A : Finset ℕ) (e₀ e₁ e₂ e₃ : ArithmeticFunction ℂ) :
    ∑ n ∈ A, ‖(e₀ - e₁ + e₂ - e₃) n‖ ^ (2 : ℕ) ≤
      4 * (∑ n ∈ A, ‖e₀ n‖ ^ (2 : ℕ)) +
      4 * (∑ n ∈ A, ‖e₁ n‖ ^ (2 : ℕ)) +
      4 * (∑ n ∈ A, ‖e₂ n‖ ^ (2 : ℕ)) +
      4 * (∑ n ∈ A, ‖e₃ n‖ ^ (2 : ℕ)) := by
  calc
    ∑ n ∈ A, ‖(e₀ - e₁ + e₂ - e₃) n‖ ^ (2 : ℕ) ≤
        ∑ n ∈ A, (4 * ‖e₀ n‖ ^ (2 : ℕ) + 4 * ‖e₁ n‖ ^ (2 : ℕ) +
          4 * ‖e₂ n‖ ^ (2 : ℕ) + 4 * ‖e₃ n‖ ^ (2 : ℕ)) := by
      apply Finset.sum_le_sum
      intro n hn
      change ‖e₀ n - e₁ n + e₂ n - e₃ n‖ ^ (2 : ℕ) ≤ _
      have hnorm : ‖e₀ n - e₁ n + e₂ n - e₃ n‖ ≤
          ‖e₀ n‖ + ‖e₁ n‖ + ‖e₂ n‖ + ‖e₃ n‖ := by
        calc
          ‖e₀ n - e₁ n + e₂ n - e₃ n‖ ≤
              ‖e₀ n - e₁ n + e₂ n‖ + ‖e₃ n‖ := by
            simpa only [sub_eq_add_neg, norm_neg] using
              norm_add_le (e₀ n - e₁ n + e₂ n) (-e₃ n)
          _ ≤ ‖e₀ n - e₁ n‖ + ‖e₂ n‖ + ‖e₃ n‖ := by
            gcongr
            exact norm_add_le (e₀ n - e₁ n) (e₂ n)
          _ ≤ ‖e₀ n‖ + ‖e₁ n‖ + ‖e₂ n‖ + ‖e₃ n‖ := by
            gcongr
            simpa only [sub_eq_add_neg, norm_neg] using norm_add_le (e₀ n) (-e₁ n)
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      calc
        ‖e₀ n - e₁ n + e₂ n - e₃ n‖ ^ (2 : ℕ) ≤
            (‖e₀ n‖ + ‖e₁ n‖ + ‖e₂ n‖ + ‖e₃ n‖) ^ (2 : ℕ) := hsq
        _ ≤ 4 * ‖e₀ n‖ ^ (2 : ℕ) + 4 * ‖e₁ n‖ ^ (2 : ℕ) +
            4 * ‖e₂ n‖ ^ (2 : ℕ) + 4 * ‖e₃ n‖ ^ (2 : ℕ) := by
          nlinarith [sq_nonneg (‖e₀ n‖ - ‖e₁ n‖),
            sq_nonneg (‖e₀ n‖ - ‖e₂ n‖), sq_nonneg (‖e₀ n‖ - ‖e₃ n‖),
            sq_nonneg (‖e₁ n‖ - ‖e₂ n‖), sq_nonneg (‖e₁ n‖ - ‖e₃ n‖),
            sq_nonneg (‖e₂ n‖ - ‖e₃ n‖)]
    _ = 4 * (∑ n ∈ A, ‖e₀ n‖ ^ (2 : ℕ)) +
        4 * (∑ n ∈ A, ‖e₁ n‖ ^ (2 : ℕ)) +
        4 * (∑ n ∈ A, ‖e₂ n‖ ^ (2 : ℕ)) +
        4 * (∑ n ∈ A, ‖e₃ n‖ ^ (2 : ℕ)) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]

set_option maxHeartbeats 600000 in
/-- Complete Harman product-boundary moment in terms of its eight local divisor collars. -/
theorem sum_normSq_mtHarmanProductBoundaryErrorAF_le_collar_zeta_sq
    {outerQ outerD : ℕ} {delta : ℝ} (A : Finset ℕ)
    (endpointQ endpointD : ℕ → ℕ) (z Q D : ℕ) (E : ℝ)
    (hendpointQ : ∀ i, 2 ≤ endpointQ i) (hmonoQ : Monotone endpointQ)
    (hbandQ : ∀ i, mtAdjacentBlockUpperScale endpointQ i ≤
      (1 + delta) * mtAdjacentBlockLowerScale endpointQ i)
    (hsourceQ : primesIco z Q ⊆ primesIco (endpointQ 0) (endpointQ outerQ))
    (hendpointD : ∀ i, 2 ≤ endpointD i) (hmonoD : Monotone endpointD)
    (hbandD : ∀ i, mtAdjacentBlockUpperScale endpointD i ≤
      (1 + delta) * mtAdjacentBlockLowerScale endpointD i)
    (z0 Dtrunc recStart : ℕ) {recRoot : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta recStart 0)
    (hroot : mtGeometricLevel delta recStart 0 < recRoot)
    (data : MTFiniteIterationSourceData
      (mtMinimalGeometricDepth delta recStart recRoot hdelta))
    (hblocks : data.block =
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 Dtrunc recStart delta recRoot hdelta hz0 hroot).block)
    (hz0Data : data.z₀ = z0) (hDData : data.D = Dtrunc)
    (maxDepth : ℕ)
    (j : Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta + 1))
    (N : ℕ) (Y eta : ℝ) (hY : 0 < Y) (heta : 0 ≤ eta)
    (hdilation : (1 + delta) ^ (maxDepth + 5) ≤ 1 + eta) :
    ∑ n ∈ A, ‖mtHarmanProductBoundaryErrorAF
      (outerQ := outerQ) (outerD := outerD) endpointQ endpointD z Q D E
      data maxDepth j delta N recStart Y n‖ ^ (2 : ℕ) ≤
      4 * ((∑ n ∈ mtLowerProductScaleCollar Y eta,
          ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (4 : ℕ)) n : ℝ) ^ (2 : ℕ))) +
        ∑ n ∈ mtUpperProductScaleCollar Y eta,
          ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (4 : ℕ)) n : ℝ) ^ (2 : ℕ))) +
      4 * ((∑ n ∈ mtLowerProductScaleCollar Y eta,
          ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (4 : ℕ)) n : ℝ) ^ (2 : ℕ))) +
        ∑ n ∈ mtUpperProductScaleCollar Y eta,
          ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (4 : ℕ)) n : ℝ) ^ (2 : ℕ))) +
      4 * ((∑ n ∈ mtLowerProductScaleCollar Y eta,
          ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (5 : ℕ)) n : ℝ) ^ (2 : ℕ))) +
        ∑ n ∈ mtUpperProductScaleCollar Y eta,
          ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (5 : ℕ)) n : ℝ) ^ (2 : ℕ))) +
      4 * ((∑ n ∈ mtLowerProductScaleCollar Y eta,
          ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (6 : ℕ)) n : ℝ) ^ (2 : ℕ))) +
        ∑ n ∈ mtUpperProductScaleCollar Y eta,
          ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (6 : ℕ)) n : ℝ) ^ (2 : ℕ))) := by
  unfold mtHarmanProductBoundaryErrorAF
  rw [hz0Data, hDData]
  let e₀ := mtProductScaleBoundaryErrorAF
    (mtOuterSeparatedBoxIndexSet (Finset.univ : Finset (Fin 1))
      data maxDepth j (mtUpperAdicIndex delta Dtrunc) (mtUpperAdicIndex delta N))
    (mtOuterSeparatedBoxAF mtBaseOuterAlpha data z0 Dtrunc delta)
    (mtOuterSeparatedBoxScale (mtBaseOuterScale delta) delta recStart) Y
  let e₁ := mtProductScaleBoundaryErrorAF
    (mtOuterSeparatedBoxIndexSet (Finset.univ : Finset (Fin outerQ))
      data maxDepth j (mtUpperAdicIndex delta Dtrunc) (mtUpperAdicIndex delta N))
    (mtOuterSeparatedBoxAF (mtOnePrimeOuterAlpha endpointQ (primesIco z Q))
      data z0 Dtrunc delta)
    (mtOuterSeparatedBoxScale (mtOnePrimeOuterScale endpointQ) delta recStart) Y
  let e₂ := mtProductScaleBoundaryErrorAF
    (mtSeparatedPairBoxIndexSet (u := outerD) endpointD E data maxDepth j
      (mtUpperAdicIndex delta Dtrunc) (mtUpperAdicIndex delta N))
    (mtSeparatedPairBoxAF endpointD (primesIco z D) data z0 Dtrunc delta)
    (mtSeparatedPairBoxScale endpointD delta recStart) Y
  let e₃ := mtProductScaleBoundaryErrorAF
    (mtSeparatedTripleBoxIndexSet (u := outerD) endpointD E data maxDepth j
      (mtUpperAdicIndex delta Dtrunc) (mtUpperAdicIndex delta N))
    (mtSeparatedTripleBoxAF endpointD (primesIco z D) data z0 Dtrunc delta)
    (mtSeparatedTripleBoxScale endpointD delta recStart) Y
  have hsum := sum_normSq_sub_add_sub_le_four A e₀ e₁ e₂ e₃
  have hdilation3 : (1 + delta) ^ (maxDepth + 3) ≤ 1 + eta :=
    (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + delta)
      (by omega : maxDepth + 3 ≤ maxDepth + 5)).trans hdilation
  have h₀ := sum_normSq_mtBaseBoxFamily_productBoundary_le_collar_zeta_sq
    A z0 Dtrunc recStart hdelta hz0 hroot data hblocks maxDepth j
    (mtUpperAdicIndex delta Dtrunc) (mtUpperAdicIndex delta N)
    Y eta hY heta hdilation3
  have h₁ := sum_normSq_mtOnePrimeBoxFamily_productBoundary_le_collar_zeta_sq
    A endpointQ (primesIco z Q) hendpointQ hmonoQ hbandQ hsourceQ
    z0 Dtrunc recStart hdelta hz0 hroot data hblocks maxDepth j
    (mtUpperAdicIndex delta Dtrunc) (mtUpperAdicIndex delta N)
    Y eta hY heta hdilation3
  have h₂ := sum_normSq_mtSeparatedPairBoxFamily_productBoundary_le_collar_zeta_sq
    (u := outerD) A endpointD (primesIco z D) hendpointD hmonoD hbandD E
    z0 Dtrunc recStart hdelta hz0 hroot data hblocks maxDepth
    (mtUpperAdicIndex delta Dtrunc) (mtUpperAdicIndex delta N) j
    Y eta hY heta hdilation
  have h₃ := sum_normSq_mtSeparatedTripleBoxFamily_productBoundary_le_collar_zeta_sq
    (u := outerD) A endpointD (primesIco z D) hendpointD hmonoD hbandD E
    z0 Dtrunc recStart hdelta hz0 hroot data hblocks maxDepth
    (mtUpperAdicIndex delta Dtrunc) (mtUpperAdicIndex delta N) j
    Y eta hY heta hdilation
  change ∑ n ∈ A, ‖(e₀ - e₁ + e₂ - e₃) n‖ ^ (2 : ℕ) ≤ _
  exact hsum.trans (add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left h₀ (by norm_num))
    (mul_le_mul_of_nonneg_left h₁ (by norm_num)))
    (mul_le_mul_of_nonneg_left h₂ (by norm_num)))
    (mul_le_mul_of_nonneg_left h₃ (by norm_num)))

end

end RHTower.Sieve
