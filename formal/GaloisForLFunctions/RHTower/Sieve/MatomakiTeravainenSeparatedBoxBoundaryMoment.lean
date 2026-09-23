import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenAlignedBoxSupport
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenAlignedSchedule

/-!
# Product-scale boundary moments for literal separated Harman schedules

Outer Harman cells use the paper-aligned partition of `[z₀,D)`, intersected with the source
prime window `[z,D)`.  Recursive Buchstab chains use the independent canonical rooted minimal
geometric partition of `[z₀,z)`.  Complete pair and triple box families retain the sharp joint
`ζ⁵` and `ζ⁶` collar envelopes.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

noncomputable section

local instance instDecidableEqMTTripleSeparatedBoxIndex (u t : ℕ) :
    DecidableEq (MTTripleSeparatedBoxIndex u t) := Classical.decEq _

def mtSeparatedPairBoxIndexSet {u t : ℕ} (endpoint : ℕ → ℕ) (E : ℝ)
    (data : MTFiniteIterationSourceData t) (maxDepth : ℕ) (j : Fin (t + 1))
    (eMax kMax : ℕ) : Finset (MTPairSeparatedBoxIndex u t) :=
  (((mtHarmanActiveGoodPairCells (t := u) endpoint E).product
      (mtAllActiveBlockChains data maxDepth j)).product
      (Finset.range (eMax + 1))).product (Finset.range (kMax + 1))

def mtSeparatedPairBoxAF {u t : ℕ} (endpoint : ℕ → ℕ) (P : Finset ℕ)
    (data : MTFiniteIterationSourceData t) (z0 D : ℕ) (delta : ℝ)
    (idx : MTPairSeparatedBoxIndex u t) : ArithmeticFunction ℂ :=
  mtSignedBlockChainAdicBoxAF
    (mtHarmanPairCellCoefficient
      (mtHarmanSourceBlock endpoint P idx.1.1.1.1)
      (mtHarmanSourceBlock endpoint P idx.1.1.1.2))
    data.block idx.1.1.2.2 z0 D delta idx.1.2 idx.2

def mtSeparatedPairBoxScale {u t : ℕ} (endpoint : ℕ → ℕ)
    (delta : ℝ) (recStart : ℕ) (idx : MTPairSeparatedBoxIndex u t) : ℝ :=
  mtSeparatedPairBoxProductScale endpoint delta recStart
    idx.1.1.1.1 idx.1.1.1.2 idx.1.1.2.2 idx.1.2 idx.2

def mtSeparatedTripleBoxIndexSet {u t : ℕ} (endpoint : ℕ → ℕ) (E : ℝ)
    (data : MTFiniteIterationSourceData t) (maxDepth : ℕ) (j : Fin (t + 1))
    (eMax kMax : ℕ) : Finset (MTTripleSeparatedBoxIndex u t) :=
  (((mtHarmanActiveGoodTripleCells (t := u) endpoint E).product
      (mtAllActiveBlockChains data maxDepth j)).product
      (Finset.range (eMax + 1))).product (Finset.range (kMax + 1))

def mtSeparatedTripleBoxAF {u t : ℕ} (endpoint : ℕ → ℕ) (P : Finset ℕ)
    (data : MTFiniteIterationSourceData t) (z0 D : ℕ) (delta : ℝ)
    (idx : MTTripleSeparatedBoxIndex u t) : ArithmeticFunction ℂ :=
  mtSignedBlockChainAdicBoxAF
    (mtHarmanTripleCellCoefficient
      (mtHarmanSourceBlock endpoint P idx.1.1.1.1.1)
      (mtHarmanSourceBlock endpoint P idx.1.1.1.1.2)
      (mtHarmanSourceBlock endpoint P idx.1.1.1.2))
    data.block idx.1.1.2.2 z0 D delta idx.1.2 idx.2

def mtSeparatedTripleBoxScale {u t : ℕ} (endpoint : ℕ → ℕ)
    (delta : ℝ) (recStart : ℕ) (idx : MTTripleSeparatedBoxIndex u t) : ℝ :=
  mtSeparatedTripleBoxProductScale endpoint delta recStart
    idx.1.1.1.1.1 idx.1.1.1.1.2 idx.1.1.1.2
      idx.1.1.2.2 idx.1.2 idx.2

/-- Literal pair-family product boundary for independent outer and recursive schedules. -/
theorem sum_normSq_mtRootedAlignedSeparatedPairBoxFamily_productBoundary_le_collar_zeta_sq
    (A : Finset ℕ) (z0 outerStart z Douter Dtrunc recStart : ℕ)
    {delta : ℝ} (hdelta : 0 < delta)
    (houterStart : 2 ≤ outerStart) (houterD : outerStart ≤ Douter)
    (hprogress : 1 ≤ delta * ((outerStart - 1 : ℕ) : ℝ))
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta recStart 0)
    (hroot : mtGeometricLevel delta recStart 0 < (z : ℝ))
    (E : ℝ) (maxDepth eMax kMax : ℕ)
    (j : Fin (mtMinimalGeometricDepth delta recStart (z : ℝ) hdelta + 1))
    (Y eta : ℝ) (hY : 0 < Y) (heta : 0 ≤ eta)
    (hdilation : (1 + delta) ^ (maxDepth + 5) ≤ 1 + eta) :
    let data := MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule
      z0 Dtrunc recStart z delta hdelta hz0 hroot
    let endpoint := mtPaperAlignedEndpoint outerStart Douter delta
    let P := primesIco z Douter
    ∑ n ∈ A, ‖mtProductScaleBoundaryErrorAF
      (mtSeparatedPairBoxIndexSet (u := Douter - outerStart)
        endpoint E data maxDepth j eMax kMax)
      (mtSeparatedPairBoxAF endpoint P data z0 Dtrunc delta)
      (mtSeparatedPairBoxScale endpoint delta recStart) Y n‖ ^ (2 : ℕ) ≤
      (∑ n ∈ mtLowerProductScaleCollar Y eta,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (5 : ℕ)) n : ℝ) ^ (2 : ℕ))) +
      ∑ n ∈ mtUpperProductScaleCollar Y eta,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (5 : ℕ)) n : ℝ) ^ (2 : ℕ)) := by
  classical
  dsimp only
  let data := MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule
    z0 Dtrunc recStart z delta hdelta hz0 hroot
  let endpoint := mtPaperAlignedEndpoint outerStart Douter delta
  let P := primesIco z Douter
  have hendpoint : ∀ i, 2 ≤ endpoint i := fun i =>
    houterStart.trans
      (mtPaperAlignedEndpoint_mem_Icc (by omega) houterD hdelta.le hprogress i).1
  apply sum_normSq_mtProductScaleBoundaryErrorAF_le_collar_zeta_sq
    A (mtSeparatedPairBoxIndexSet (u := Douter - outerStart)
      endpoint E data maxDepth j eMax kMax)
      (mtSeparatedPairBoxAF endpoint P data z0 Dtrunc delta)
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
      hendpoint (mtPaperAlignedEndpoint_band hdelta.le) P z0 Dtrunc recStart
      hdelta hz0 hroot data
      (ofMinimalGeometricRootedSchedule_block_eq_ofMinimalGeometricSchedule_block
        z0 Dtrunc recStart z hdelta hz0 hroot)
      idx.1.1.1.1 idx.1.1.1.2 (activeBlockChain_nodup hchain)
      maxDepth idx.1.2 idx.2
    · rw [hlen]
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hdc.1)
    · exact (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + delta)
        (by omega : maxDepth + 4 ≤ maxDepth + 5)).trans hdilation
  · intro n
    simpa [mtSeparatedPairBoxIndexSet, mtSeparatedPairBoxAF, endpoint, P, data] using
      sum_norm_mtSignedSeparatedPairBoxFamily_le_zeta_pow_five
        (mtPaperAlignedEndpoint_monotone (by omega) houterD hdelta.le hprogress)
        P E data maxDepth j hdelta z0 Dtrunc eMax kMax n

/-- Literal triple-family product boundary for independent outer and recursive schedules. -/
theorem sum_normSq_mtRootedAlignedSeparatedTripleBoxFamily_productBoundary_le_collar_zeta_sq
    (A : Finset ℕ) (z0 outerStart z Douter Dtrunc recStart : ℕ)
    {delta : ℝ} (hdelta : 0 < delta)
    (houterStart : 2 ≤ outerStart) (houterD : outerStart ≤ Douter)
    (hprogress : 1 ≤ delta * ((outerStart - 1 : ℕ) : ℝ))
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta recStart 0)
    (hroot : mtGeometricLevel delta recStart 0 < (z : ℝ))
    (E : ℝ) (maxDepth eMax kMax : ℕ)
    (j : Fin (mtMinimalGeometricDepth delta recStart (z : ℝ) hdelta + 1))
    (Y eta : ℝ) (hY : 0 < Y) (heta : 0 ≤ eta)
    (hdilation : (1 + delta) ^ (maxDepth + 5) ≤ 1 + eta) :
    let data := MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule
      z0 Dtrunc recStart z delta hdelta hz0 hroot
    let endpoint := mtPaperAlignedEndpoint outerStart Douter delta
    let P := primesIco z Douter
    ∑ n ∈ A, ‖mtProductScaleBoundaryErrorAF
      (mtSeparatedTripleBoxIndexSet (u := Douter - outerStart)
        endpoint E data maxDepth j eMax kMax)
      (mtSeparatedTripleBoxAF endpoint P data z0 Dtrunc delta)
      (mtSeparatedTripleBoxScale endpoint delta recStart) Y n‖ ^ (2 : ℕ) ≤
      (∑ n ∈ mtLowerProductScaleCollar Y eta,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (6 : ℕ)) n : ℝ) ^ (2 : ℕ))) +
      ∑ n ∈ mtUpperProductScaleCollar Y eta,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (6 : ℕ)) n : ℝ) ^ (2 : ℕ)) := by
  classical
  dsimp only
  let data := MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule
    z0 Dtrunc recStart z delta hdelta hz0 hroot
  let endpoint := mtPaperAlignedEndpoint outerStart Douter delta
  let P := primesIco z Douter
  have hendpoint : ∀ i, 2 ≤ endpoint i := fun i =>
    houterStart.trans
      (mtPaperAlignedEndpoint_mem_Icc (by omega) houterD hdelta.le hprogress i).1
  apply sum_normSq_mtProductScaleBoundaryErrorAF_le_collar_zeta_sq
    A (mtSeparatedTripleBoxIndexSet (u := Douter - outerStart)
      endpoint E data maxDepth j eMax kMax)
      (mtSeparatedTripleBoxAF endpoint P data z0 Dtrunc delta)
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
      hendpoint (mtPaperAlignedEndpoint_band hdelta.le) P z0 Dtrunc recStart
      hdelta hz0 hroot data
      (ofMinimalGeometricRootedSchedule_block_eq_ofMinimalGeometricSchedule_block
        z0 Dtrunc recStart z hdelta hz0 hroot)
      idx.1.1.1.1.1 idx.1.1.1.1.2 idx.1.1.1.2
      (activeBlockChain_nodup hchain) maxDepth idx.1.2 idx.2
    · rw [hlen]
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hdc.1)
    · exact hdilation
  · intro n
    simpa [mtSeparatedTripleBoxIndexSet, mtSeparatedTripleBoxAF, endpoint, P, data] using
      sum_norm_mtSignedSeparatedTripleBoxFamily_le_zeta_pow_six
        (mtPaperAlignedEndpoint_monotone (by omega) houterD hdelta.le hprogress)
        P E data maxDepth j hdelta z0 Dtrunc eMax kMax n

end

end RHTower.Sieve
