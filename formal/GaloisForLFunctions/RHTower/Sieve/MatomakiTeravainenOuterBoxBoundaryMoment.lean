import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenOuterBoxClassification
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanAggregateMainExpansion
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenProductScaleBoundaryMoment

/-!
# Product-scale boundary for base and one-prime boxes

This is the outer-coefficient analogue of the separated pair/triple collar theorem.  One narrow
outer coefficient, a recursive chain, and the two adic factors cost three dilation powers beyond
chain length.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

noncomputable section

abbrev MTOuterSeparatedBoxIndex (ι : Type*) (t : ℕ) :=
  (((ι × (ℕ × List (Fin t))) × ℕ) × ℕ)

def mtOuterSeparatedBoxIndexSet {ι : Type*} [DecidableEq ι] {t : ℕ}
    (S : Finset ι) (data : MTFiniteIterationSourceData t)
    (maxDepth : ℕ) (j : Fin (t + 1)) (eMax kMax : ℕ) :
    Finset (MTOuterSeparatedBoxIndex ι t) :=
  (((S.product (mtAllActiveBlockChains data maxDepth j)).product
      (Finset.range (eMax + 1))).product (Finset.range (kMax + 1)))

def mtOuterSeparatedBoxAF {ι : Type*} {t : ℕ}
    (alpha : ι → ℕ → ℂ) (data : MTFiniteIterationSourceData t)
    (z₀ D : ℕ) (delta : ℝ) (idx : MTOuterSeparatedBoxIndex ι t) :
    ArithmeticFunction ℂ :=
  mtSignedBlockChainAdicBoxAF (alpha idx.1.1.1) data.block idx.1.1.2.2
    z₀ D delta idx.1.2 idx.2

def mtOuterSeparatedBoxScale {ι : Type*} {t : ℕ}
    (L : ι → ℝ) (delta : ℝ) (recStart : ℕ)
    (idx : MTOuterSeparatedBoxIndex ι t) : ℝ :=
  mtOuterBlockChainProductScale (L idx.1.1.1) delta recStart
    idx.1.1.2.2 idx.1.2 idx.2

theorem sum_mtOuterSeparatedBoxAF_eq_sum_mtFiniteMainBoxFamilyAF
    {ι : Type*} [DecidableEq ι] {t : ℕ}
    (S : Finset ι) (alpha : ι → ℕ → ℂ)
    (data : MTFiniteIterationSourceData t) (maxDepth : ℕ)
    (j : Fin (t + 1)) (delta : ℝ) (N : ℕ) :
    ∑ idx ∈ mtOuterSeparatedBoxIndexSet S data maxDepth j
        (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N),
      mtOuterSeparatedBoxAF alpha data data.z₀ data.D delta idx =
      ∑ i ∈ S, mtFiniteMainBoxFamilyAF data (alpha i)
        maxDepth j delta N := by
  classical
  let H := mtAllActiveBlockChains data maxDepth j
  let ES := Finset.range (mtUpperAdicIndex delta data.D + 1)
  let KS := Finset.range (mtUpperAdicIndex delta N + 1)
  let F : MTOuterSeparatedBoxIndex ι t → ArithmeticFunction ℂ := fun idx =>
    mtOuterSeparatedBoxAF alpha data data.z₀ data.D delta idx
  change ∑ idx ∈ (((S.product H).product ES).product KS), F idx = _
  calc
    (∑ idx ∈ (((S.product H).product ES).product KS), F idx) =
        ∑ ice ∈ ((S.product H).product ES),
          ∑ k ∈ KS, F (ice, k) := Finset.sum_product _ _ _
    _ = ∑ ic ∈ S.product H, ∑ e ∈ ES, ∑ k ∈ KS, F ((ic, e), k) := by
      exact Finset.sum_product _ _ _
    _ = ∑ i ∈ S, ∑ dc ∈ H, ∑ e ∈ ES, ∑ k ∈ KS,
        F (((i, dc), e), k) := Finset.sum_product _ _ _
    _ = ∑ i ∈ S, mtFiniteMainBoxFamilyAF data (alpha i)
        maxDepth j delta N := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [mtFiniteMainBoxFamilyAF_eq_sum_allActiveBlockChains]
      rfl

theorem sum_norm_mtOuterSeparatedBoxFamily_le_zeta_pow
    {ι : Type*} [DecidableEq ι] {t : ℕ}
    (S : Finset ι) (alpha : ι → ℕ → ℂ)
    (data : MTFiniteIterationSourceData t) (maxDepth : ℕ)
    (j : Fin (t + 1)) {delta : ℝ} (hdelta : 0 < delta)
    (z₀ D eMax kMax r : ℕ)
    (houter : ∀ n, ∑ i ∈ S, ‖mtCoefficientAF (alpha i) n‖ ≤
      ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n : ℕ) : ℝ))
    (n : ℕ) :
    ∑ idx ∈ mtOuterSeparatedBoxIndexSet S data maxDepth j eMax kMax,
        ‖mtOuterSeparatedBoxAF alpha data z₀ D delta idx n‖ ≤
      ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (r + 3)) n : ℕ) : ℝ) := by
  simpa [mtOuterSeparatedBoxIndexSet, mtOuterSeparatedBoxAF,
    mtSignedBlockChainAdicBoxAF, mtBlockChainAdicBoxAF] using
    sum_norm_outer_active_adic_boxFamily_le_zeta_pow
      S (fun i => mtCoefficientAF (alpha i)) data maxDepth j hdelta
      z₀ D eMax kMax r houter n

theorem mtSignedOuterBlockChainAdicBox_scaleSupported_commonProductCollar
    {t : ℕ} {alpha : ℕ → ℂ} {L delta : ℝ}
    (halpha : MTRealScaleSupported (mtCoefficientAF alpha) L ((1 + delta) * L))
    (hL : 0 < L) (z₀ D recStart : ℕ) {recRoot eta : ℝ}
    (hdelta : 0 < delta)
    (hz₀ : (z₀ : ℝ) ≤ mtGeometricLevel delta recStart 0)
    (hroot : mtGeometricLevel delta recStart 0 < recRoot)
    (data : MTFiniteIterationSourceData
      (mtMinimalGeometricDepth delta recStart recRoot hdelta))
    (hblocks : data.block =
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z₀ D recStart delta recRoot hdelta hz₀ hroot).block)
    {chain : List (Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta))}
    (hchain : chain.Nodup) (maxDepth eIndex kIndex : ℕ)
    (hlength : chain.length ≤ maxDepth)
    (hdilation : (1 + delta) ^ (maxDepth + 3) ≤ 1 + eta) :
    MTRealScaleSupported
      (mtSignedBlockChainAdicBoxAF alpha data.block chain
        z₀ D delta eIndex kIndex)
      (mtOuterBlockChainProductScale L delta recStart chain eIndex kIndex)
      ((1 + eta) *
        mtOuterBlockChainProductScale L delta recStart chain eIndex kIndex) := by
  let Mlong := mtOuterBlockChainLongScale L delta recStart chain eIndex
  let K := mtUpperAdicScale delta kIndex
  let F := mtBlockChainLongAF alpha data.block chain z₀ D delta eIndex
  have hlong : MTRealScaleSupported F Mlong
      ((1 + delta) ^ (chain.length + 2) * Mlong) := by
    exact mtOuterBlockChainLongAF_scaleSupported_dilation
      (t := mtMinimalGeometricDepth delta recStart recRoot hdelta)
      halpha hL z₀ D recStart hdelta hz₀ hroot data hblocks hchain eIndex
  have hmul : MTRealScaleSupported (F * mtUpperAdicOneAF delta kIndex)
      (Mlong * K)
      (((1 + delta) ^ (chain.length + 2) * Mlong) * ((1 + delta) * K)) := by
    exact MTRealScaleSupported.mul hlong (mtRealIntervalAF_scaleSupported _ _ _)
      (mtOuterBlockChainLongScale_pos hL hdelta recStart chain eIndex).le
      (mtUpperAdicScale_pos hdelta kIndex).le
  have hexact : MTRealScaleSupported (F * mtUpperAdicOneAF delta kIndex)
      (Mlong * K) ((1 + delta) ^ (chain.length + 3) * (Mlong * K)) := by
    intro n hn
    have hs := hmul hn
    refine ⟨hs.1, hs.2.1, hs.2.2.trans_eq ?_⟩
    rw [show chain.length + 3 = chain.length + 2 + 1 by omega, pow_succ]
    ring
  have hpower : (1 + delta) ^ (chain.length + 3) ≤ 1 + eta :=
    (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + delta) (by omega)).trans
      hdilation
  have hscale : 0 ≤ Mlong * K :=
    mul_nonneg (mtOuterBlockChainLongScale_pos hL hdelta recStart chain eIndex).le
      (mtUpperAdicScale_pos hdelta kIndex).le
  have hcommon : MTRealScaleSupported (F * mtUpperAdicOneAF delta kIndex)
      (Mlong * K) ((1 + eta) * (Mlong * K)) := by
    intro n hn
    have hs := hexact hn
    exact ⟨hs.1, hs.2.1,
      hs.2.2.trans (mul_le_mul_of_nonneg_right hpower hscale)⟩
  have hcommon' : MTRealScaleSupported
      (mtBlockChainAdicBoxAF alpha data.block chain z₀ D delta eIndex kIndex)
      (Mlong * K) ((1 + eta) * (Mlong * K)) := by
    intro n hn
    change (F * mtUpperAdicOneAF delta kIndex) n ≠ 0 at hn
    exact hcommon hn
  change MTRealScaleSupported
    (((-1 : ℂ) ^ chain.length) •
      mtBlockChainAdicBoxAF alpha data.block chain z₀ D delta eIndex kIndex)
    (Mlong * K) ((1 + eta) * (Mlong * K))
  exact MTRealScaleSupported.smul hcommon' ((-1 : ℂ) ^ chain.length)

/-- Common collar moment for any finite family of narrow outer coefficients. -/
theorem sum_normSq_mtOuterSeparatedBoxFamily_productBoundary_le_collar_zeta_sq
    {ι : Type*} [DecidableEq ι]
    (A : Finset ℕ) (S : Finset ι) (alpha : ι → ℕ → ℂ) (L : ι → ℝ)
    (z₀ D recStart : ℕ) {recRoot delta : ℝ} (hdelta : 0 < delta)
    (hz₀ : (z₀ : ℝ) ≤ mtGeometricLevel delta recStart 0)
    (hroot : mtGeometricLevel delta recStart 0 < recRoot)
    (data : MTFiniteIterationSourceData
      (mtMinimalGeometricDepth delta recStart recRoot hdelta))
    (hblocks : data.block =
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z₀ D recStart delta recRoot hdelta hz₀ hroot).block)
    (halpha : ∀ i ∈ S,
      MTRealScaleSupported (mtCoefficientAF (alpha i)) (L i) ((1 + delta) * L i))
    (hL : ∀ i ∈ S, 0 < L i)
    (maxDepth : ℕ)
    (j : Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta + 1))
    (eMax kMax : ℕ) (Y eta : ℝ) (r : ℕ)
    (hY : 0 < Y) (heta : 0 ≤ eta)
    (hdilation : (1 + delta) ^ (maxDepth + 3) ≤ 1 + eta)
    (houter : ∀ n, ∑ i ∈ S, ‖mtCoefficientAF (alpha i) n‖ ≤
      ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n : ℕ) : ℝ)) :
    ∑ n ∈ A, ‖mtProductScaleBoundaryErrorAF
      (mtOuterSeparatedBoxIndexSet S data maxDepth j eMax kMax)
      (mtOuterSeparatedBoxAF alpha data z₀ D delta)
      (mtOuterSeparatedBoxScale L delta recStart) Y n‖ ^ 2 ≤
      (∑ n ∈ mtLowerProductScaleCollar Y eta,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (r + 3)) n : ℝ) ^ 2)) +
      ∑ n ∈ mtUpperProductScaleCollar Y eta,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (r + 3)) n : ℝ) ^ 2) := by
  apply sum_normSq_mtProductScaleBoundaryErrorAF_le_collar_zeta_sq
    A (mtOuterSeparatedBoxIndexSet S data maxDepth j eMax kMax)
      (mtOuterSeparatedBoxAF alpha data z₀ D delta)
      (mtOuterSeparatedBoxScale L delta recStart) Y eta (r + 3) hY heta
  · intro idx hidx
    rw [mtOuterSeparatedBoxIndexSet] at hidx
    have hidxK := Finset.mem_product.mp hidx
    have hidxE := Finset.mem_product.mp hidxK.1
    have hidxID := Finset.mem_product.mp hidxE.1
    have hiS := hidxID.1
    have hdc := mem_mtAllActiveBlockChains.mp hidxID.2
    have hchain := hdc.2
    apply mtSignedOuterBlockChainAdicBox_scaleSupported_commonProductCollar
      (t := mtMinimalGeometricDepth delta recStart recRoot hdelta)
      (halpha idx.1.1.1 hiS) (hL idx.1.1.1 hiS)
      z₀ D recStart hdelta hz₀ hroot data hblocks
      (activeBlockChain_nodup hchain) maxDepth idx.1.2 idx.2
    · rw [length_eq_of_mem_mtActiveBlockChains hchain]
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hdc.1)
    · exact hdilation
  · intro n
    exact sum_norm_mtOuterSeparatedBoxFamily_le_zeta_pow
      S alpha data maxDepth j hdelta z₀ D eMax kMax r houter n

end

end RHTower.Sieve
