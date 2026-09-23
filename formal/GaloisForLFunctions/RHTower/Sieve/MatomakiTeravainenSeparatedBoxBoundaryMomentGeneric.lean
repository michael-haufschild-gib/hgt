import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenSeparatedBoxBoundaryMoment

/-!
# Product-boundary moments for arbitrary minimal geometric source data

These are the data-parametric forms of the pair and triple collar estimates.  In particular they
apply to the real-rooted, ceiling-cutoff schedule used by the literal Proposition 2.2 parameters.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

noncomputable section

local instance instDecidableEqMTTripleSeparatedBoxIndexGenericBoundary (u t : ℕ) :
    DecidableEq (MTTripleSeparatedBoxIndex u t) := Classical.decEq _

set_option maxHeartbeats 600000

theorem sum_normSq_mtSeparatedPairBoxFamily_productBoundary_le_collar_zeta_sq
    (A : Finset ℕ) {u : ℕ} {delta : ℝ} (endpoint : ℕ → ℕ) (P : Finset ℕ)
    (hendpoint : ∀ i, 2 ≤ endpoint i) (hmono : Monotone endpoint)
    (hband : ∀ i, mtAdjacentBlockUpperScale endpoint i ≤
      (1 + delta) * mtAdjacentBlockLowerScale endpoint i)
    (E : ℝ) (z0 D recStart : ℕ) {recRoot : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta recStart 0)
    (hroot : mtGeometricLevel delta recStart 0 < recRoot)
    (data : MTFiniteIterationSourceData
      (mtMinimalGeometricDepth delta recStart recRoot hdelta))
    (hblocks : data.block =
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D recStart delta recRoot hdelta hz0 hroot).block)
    (maxDepth eMax kMax : ℕ)
    (j : Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta + 1))
    (Y eta : ℝ) (hY : 0 < Y) (heta : 0 ≤ eta)
    (hdilation : (1 + delta) ^ (maxDepth + 5) ≤ 1 + eta) :
    ∑ n ∈ A, ‖mtProductScaleBoundaryErrorAF
      (mtSeparatedPairBoxIndexSet (u := u) endpoint E data maxDepth j eMax kMax)
      (mtSeparatedPairBoxAF endpoint P data z0 D delta)
      (mtSeparatedPairBoxScale endpoint delta recStart) Y n‖ ^ (2 : ℕ) ≤
      (∑ n ∈ mtLowerProductScaleCollar Y eta,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (5 : ℕ)) n : ℝ) ^ (2 : ℕ))) +
      ∑ n ∈ mtUpperProductScaleCollar Y eta,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (5 : ℕ)) n : ℝ) ^ (2 : ℕ)) := by
  apply sum_normSq_mtProductScaleBoundaryErrorAF_le_collar_zeta_sq
    A (mtSeparatedPairBoxIndexSet (u := u) endpoint E data maxDepth j eMax kMax)
      (mtSeparatedPairBoxAF endpoint P data z0 D delta)
      (mtSeparatedPairBoxScale endpoint delta recStart) Y eta 5 hY heta
  · intro idx hidx
    rw [mtSeparatedPairBoxIndexSet] at hidx
    have hidxK := Finset.mem_product.mp hidx
    have hidxE := Finset.mem_product.mp hidxK.1
    have hidxCH := Finset.mem_product.mp hidxE.1
    have hdc := mem_mtAllActiveBlockChains.mp hidxCH.2
    have hchain := hdc.2
    have hlen := length_eq_of_mem_mtActiveBlockChains hchain
    apply mtSignedSeparatedPairBox_scaleSupported_commonProductCollar
      hendpoint hband P z0 D recStart hdelta hz0 hroot data hblocks
      idx.1.1.1.1 idx.1.1.1.2 (activeBlockChain_nodup hchain)
      maxDepth idx.1.2 idx.2
    · rw [hlen]
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hdc.1)
    · exact (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + delta)
        (by omega : maxDepth + 4 ≤ maxDepth + 5)).trans hdilation
  · intro n
    simpa [mtSeparatedPairBoxIndexSet, mtSeparatedPairBoxAF] using
      sum_norm_mtSignedSeparatedPairBoxFamily_le_zeta_pow_five
        hmono P E data maxDepth j hdelta z0 D eMax kMax n

theorem sum_normSq_mtSeparatedTripleBoxFamily_productBoundary_le_collar_zeta_sq
    (A : Finset ℕ) {u : ℕ} {delta : ℝ} (endpoint : ℕ → ℕ) (P : Finset ℕ)
    (hendpoint : ∀ i, 2 ≤ endpoint i) (hmono : Monotone endpoint)
    (hband : ∀ i, mtAdjacentBlockUpperScale endpoint i ≤
      (1 + delta) * mtAdjacentBlockLowerScale endpoint i)
    (E : ℝ) (z0 D recStart : ℕ) {recRoot : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta recStart 0)
    (hroot : mtGeometricLevel delta recStart 0 < recRoot)
    (data : MTFiniteIterationSourceData
      (mtMinimalGeometricDepth delta recStart recRoot hdelta))
    (hblocks : data.block =
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D recStart delta recRoot hdelta hz0 hroot).block)
    (maxDepth eMax kMax : ℕ)
    (j : Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta + 1))
    (Y eta : ℝ) (hY : 0 < Y) (heta : 0 ≤ eta)
    (hdilation : (1 + delta) ^ (maxDepth + 5) ≤ 1 + eta) :
    ∑ n ∈ A, ‖mtProductScaleBoundaryErrorAF
      (mtSeparatedTripleBoxIndexSet (u := u) endpoint E data maxDepth j eMax kMax)
      (mtSeparatedTripleBoxAF endpoint P data z0 D delta)
      (mtSeparatedTripleBoxScale endpoint delta recStart) Y n‖ ^ (2 : ℕ) ≤
      (∑ n ∈ mtLowerProductScaleCollar Y eta,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (6 : ℕ)) n : ℝ) ^ (2 : ℕ))) +
      ∑ n ∈ mtUpperProductScaleCollar Y eta,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (6 : ℕ)) n : ℝ) ^ (2 : ℕ)) := by
  apply sum_normSq_mtProductScaleBoundaryErrorAF_le_collar_zeta_sq
    A (mtSeparatedTripleBoxIndexSet (u := u) endpoint E data maxDepth j eMax kMax)
      (mtSeparatedTripleBoxAF endpoint P data z0 D delta)
      (mtSeparatedTripleBoxScale endpoint delta recStart) Y eta 6 hY heta
  · intro idx hidx
    rw [mtSeparatedTripleBoxIndexSet] at hidx
    have hidxK := Finset.mem_product.mp hidx
    have hidxE := Finset.mem_product.mp hidxK.1
    have hidxCH := Finset.mem_product.mp hidxE.1
    have hdc := mem_mtAllActiveBlockChains.mp hidxCH.2
    have hchain := hdc.2
    have hlen := length_eq_of_mem_mtActiveBlockChains hchain
    apply mtSignedSeparatedTripleBox_scaleSupported_commonProductCollar
      hendpoint hband P z0 D recStart hdelta hz0 hroot data hblocks
      idx.1.1.1.1.1 idx.1.1.1.1.2 idx.1.1.1.2
      (activeBlockChain_nodup hchain) maxDepth idx.1.2 idx.2
    · rw [hlen]
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hdc.1)
    · exact hdilation
  · intro n
    simpa [mtSeparatedTripleBoxIndexSet, mtSeparatedTripleBoxAF] using
      sum_norm_mtSignedSeparatedTripleBoxFamily_le_zeta_pow_six
        hmono P E data maxDepth j hdelta z0 D eMax kMax n

end

end RHTower.Sieve
