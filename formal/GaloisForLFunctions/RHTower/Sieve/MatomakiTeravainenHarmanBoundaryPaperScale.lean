import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanBoundaryMoment
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenProductScaleBoundaryPaperScale

/-!
# Paper-scale mean square for the complete Harman product boundary

The four signed boundary families have generalized-divisor orders `4,4,5,6`.  The uniform collar
bound absorbs all eight endpoint collars with one fixed Hilbert-space constant.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

noncomputable section

/-- Complete Harman boundary error has the Proposition 2.2 logarithmic mean-square saving. -/
theorem eventually_sum_normSq_mtHarmanProductBoundaryErrorAF_le_paper
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ {outerQ outerD : ℕ} (S : Finset ℕ)
        (endpointQ endpointD : ℕ → ℕ) (z Q D : ℕ) (E : ℝ),
      (∀ i, 2 ≤ endpointQ i) → Monotone endpointQ →
      (∀ i, mtAdjacentBlockUpperScale endpointQ i ≤
        (1 + mtPaperWidth A X) * mtAdjacentBlockLowerScale endpointQ i) →
      primesIco z Q ⊆ primesIco (endpointQ 0) (endpointQ outerQ) →
      (∀ i, 2 ≤ endpointD i) → Monotone endpointD →
      (∀ i, mtAdjacentBlockUpperScale endpointD i ≤
        (1 + mtPaperWidth A X) * mtAdjacentBlockLowerScale endpointD i) →
      ∀ (z0 Dtrunc recStart : ℕ) (recRoot : ℝ)
        (hdelta : 0 < mtPaperWidth A X)
        (hz0 : (z0 : ℝ) ≤ mtGeometricLevel (mtPaperWidth A X) recStart 0)
        (hroot : mtGeometricLevel (mtPaperWidth A X) recStart 0 < recRoot),
      ∀ (data : MTFiniteIterationSourceData
          (mtMinimalGeometricDepth (mtPaperWidth A X) recStart recRoot
            hdelta)),
      data.block =
        (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 Dtrunc recStart (mtPaperWidth A X) recRoot
          hdelta hz0 hroot).block →
      data.z₀ = z0 → data.D = Dtrunc →
      ∀ (maxDepth : ℕ)
        (j : Fin (mtMinimalGeometricDepth (mtPaperWidth A X) recStart recRoot
          hdelta + 1))
        (N : ℕ) (Y : ℝ),
      X ^ (1 / 2 : ℝ) ≤ Y → Y ≤ X →
      (1 + mtPaperWidth A X) ^ (maxDepth + 5) ≤
        1 + mtPaperWidth (A - 1) X →
      ∑ n ∈ S, ‖mtHarmanProductBoundaryErrorAF
        (outerQ := outerQ) (outerD := outerD) endpointQ endpointD z Q D E
        data maxDepth j (mtPaperWidth A X) N recStart Y n‖ ^ 2 ≤
        (23056 * (5 : ℝ) ^ 35) * Y *
          (Real.log X) ^ (-((A : ℕ) : ℝ)) := by
  filter_upwards [eventually_sum_mtProductScaleCollars_zeta_sq_le_paper A hA,
    Filter.eventually_ge_atTop (Real.exp 2)] with X hcollar hX
  intro outerQ outerD S endpointQ endpointD z Q D E
    hendpointQ hmonoQ hbandQ hsourceQ hendpointD hmonoD hbandD
    z0 Dtrunc recStart recRoot hdelta hz0 hroot data hblocks hz0Data hDData
    maxDepth j N Y hXY hYX hdilation
  have hXpos : 0 < X := (Real.exp_pos 2).trans_le hX
  have hY : 0 < Y := (Real.rpow_pos_of_pos hXpos _).trans_le hXY
  have hlog0 : 0 ≤ Real.log X := Real.log_nonneg
    ((by norm_num : (1 : ℝ) ≤ Real.exp 2).trans hX)
  have heta : 0 ≤ mtPaperWidth (A - 1) X := by
    rw [mtPaperWidth]
    exact Real.rpow_nonneg hlog0 _
  have hraw := sum_normSq_mtHarmanProductBoundaryErrorAF_le_collar_zeta_sq
    (outerQ := outerQ) (outerD := outerD) S endpointQ endpointD z Q D E
    hendpointQ hmonoQ hbandQ hsourceQ hendpointD hmonoD hbandD
    z0 Dtrunc recStart hdelta hz0 hroot data hblocks hz0Data hDData maxDepth j N Y
    (mtPaperWidth (A - 1) X) hY heta hdilation
  have h4 := hcollar Y 4 hXY hYX (by norm_num) (by norm_num)
  have h5 := hcollar Y 5 hXY hYX (by norm_num) (by norm_num)
  have h6 := hcollar Y 6 hXY hYX (by norm_num) (by norm_num)
  nlinarith

end

end RHTower.Sieve
