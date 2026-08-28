import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanGeometricCells

/-!
# Exact support of geometric Harman block-chain boxes

Each pair long factor has dilation `(1+delta)^(R+3)` from two Harman primes, `R` recursive
blocks, and the truncated-Moebius block.  Triple factors have exponent `R+4`.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

theorem mtUpperAdicScale_pos {delta : ℝ} (hdelta : 0 < delta) (i : ℕ) :
    0 < mtUpperAdicScale delta i := by
  rw [mtUpperAdicScale]
  split_ifs with hi
  · exact inv_pos.mpr (by linarith)
  · exact pow_pos (by linarith) _

theorem prod_mul_constant_chain_toFinset
    {t : ℕ} (Q : Fin t → ℝ) (b : ℝ)
    {chain : List (Fin t)} (hchain : chain.Nodup) :
    (∏ i ∈ chain.toFinset, Q i * b) =
      b ^ chain.length * ∏ i ∈ chain.toFinset, Q i := by
  rw [Finset.prod_mul_distrib]
  have hcard : chain.toFinset.card = chain.length := List.toFinset_card_of_nodup hchain
  simp only [Finset.prod_const, hcard]
  ring

theorem MTRealScaleSupported.dyadic_of_dilation
    {F : ArithmeticFunction ℂ} {M dilation : ℝ}
    (hF : MTRealScaleSupported F M (dilation * M))
    (hM : 0 ≤ M) (hdilation : dilation ≤ 2) :
    MTRealScaleSupported F M (2 * M) := by
  intro n hn
  have hs := hF hn
  exact ⟨hs.1, hs.2.1,
    hs.2.2.trans (mul_le_mul_of_nonneg_right hdilation hM)⟩

theorem mtBlockChainAdicBoxAF_eq_long_mul_upperAdicOne
    {t : ℕ} (alpha : ℕ → ℂ) (block : Fin t → Finset ℕ)
    (chain : List (Fin t)) (z D : ℕ) (delta : ℝ) (i j : ℕ) :
    mtBlockChainAdicBoxAF alpha block chain z D delta i j =
      mtBlockChainLongAF alpha block chain z D delta i * mtUpperAdicOneAF delta j := by
  rfl

theorem mtMinimalGeometricPairLongAF_scaleSupported
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i1 i2 : Fin (mtMinimalGeometricDepth delta start z hdelta))
    {chain : List (Fin (mtMinimalGeometricDepth delta start z hdelta))}
    (hchain : chain.Nodup) (eIndex : ℕ) :
    MTRealScaleSupported
      (mtBlockChainLongAF
        (mtHarmanPairCellCoefficient
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i1)
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i2))
        (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 D start delta z hdelta hz0 hroot).block chain z0 D delta eIndex)
      (((mtGeometricLevel delta start i1.1 * mtGeometricLevel delta start i2.1) *
          ∏ j ∈ chain.toFinset, mtGeometricLevel delta start j.1) *
        mtUpperAdicScale delta eIndex)
      ((1 + delta) ^ (chain.length + 3) *
        (((mtGeometricLevel delta start i1.1 * mtGeometricLevel delta start i2.1) *
            ∏ j ∈ chain.toFinset, mtGeometricLevel delta start j.1) *
          mtUpperAdicScale delta eIndex)) := by
  let source := MTFiniteIterationSourceData.ofMinimalGeometricSchedule
    z0 D start delta z hdelta hz0 hroot
  let Q : Fin (mtMinimalGeometricDepth delta start z hdelta) → ℝ :=
    fun i => mtGeometricLevel delta start i.1
  let b : ℝ := 1 + delta
  let E : ℝ := mtUpperAdicScale delta eIndex
  have hraw : MTRealScaleSupported
      (mtBlockChainLongAF
        (mtHarmanPairCellCoefficient (source.block i1) (source.block i2))
        source.block chain z0 D delta eIndex)
      (((Q i1 * Q i2) * ∏ j ∈ chain.toFinset, Q j) * E)
      ((((Q i1 * b) * (Q i2 * b)) *
          ∏ j ∈ chain.toFinset, Q j * b) * (b * E)) :=
    mtBlockChainLongAF_scaleSupported
      (mtMinimalGeometricPairCell_scaleSupported z0 D start hdelta hz0 hroot i1 i2)
      (fun i => mtMinimalGeometricBlock_scaleSupported z0 D start hdelta hz0 hroot i)
      (fun i => (mtGeometricLevel_pos hdelta start i.1).le)
      (mul_nonneg (mtGeometricLevel_pos hdelta start i1.1).le
        (mtGeometricLevel_pos hdelta start i2.1).le)
      hchain z0 D eIndex (mtUpperAdicScale_pos hdelta eIndex).le
  intro n hn
  have hs := hraw hn
  refine ⟨hs.1, hs.2.1, hs.2.2.trans_eq ?_⟩
  change
    (((Q i1 * b) * (Q i2 * b)) *
      (∏ j ∈ chain.toFinset, Q j * b)) * (b * E) =
      b ^ (chain.length + 3) * (((Q i1 * Q i2) *
        ∏ j ∈ chain.toFinset, Q j) * E)
  rw [prod_mul_constant_chain_toFinset Q b hchain, pow_add]
  ring

theorem mtMinimalGeometricPairLongAF_scaleSupported_dyadic
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i1 i2 : Fin (mtMinimalGeometricDepth delta start z hdelta))
    {chain : List (Fin (mtMinimalGeometricDepth delta start z hdelta))}
    (hchain : chain.Nodup) (eIndex : ℕ)
    (hdilation : (1 + delta) ^ (chain.length + 3) ≤ 2) :
    MTRealScaleSupported
      (mtBlockChainLongAF
        (mtHarmanPairCellCoefficient
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i1)
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i2))
        (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 D start delta z hdelta hz0 hroot).block chain z0 D delta eIndex)
      (((mtGeometricLevel delta start i1.1 * mtGeometricLevel delta start i2.1) *
          ∏ j ∈ chain.toFinset, mtGeometricLevel delta start j.1) *
        mtUpperAdicScale delta eIndex)
      (2 * (((mtGeometricLevel delta start i1.1 * mtGeometricLevel delta start i2.1) *
          ∏ j ∈ chain.toFinset, mtGeometricLevel delta start j.1) *
        mtUpperAdicScale delta eIndex)) := by
  apply MTRealScaleSupported.dyadic_of_dilation
    (mtMinimalGeometricPairLongAF_scaleSupported
      z0 D start hdelta hz0 hroot i1 i2 hchain eIndex)
  · exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mtGeometricLevel_pos hdelta start i1.1).le
          (mtGeometricLevel_pos hdelta start i2.1).le)
        (Finset.prod_nonneg fun j hj =>
          (mtGeometricLevel_pos hdelta start j.1).le))
      (mtUpperAdicScale_pos hdelta eIndex).le
  · exact hdilation

theorem mtMinimalGeometricTripleLongAF_scaleSupported
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i1 i2 i3 : Fin (mtMinimalGeometricDepth delta start z hdelta))
    {chain : List (Fin (mtMinimalGeometricDepth delta start z hdelta))}
    (hchain : chain.Nodup) (eIndex : ℕ) :
    MTRealScaleSupported
      (mtBlockChainLongAF
        (mtHarmanTripleCellCoefficient
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i1)
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i2)
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i3))
        (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 D start delta z hdelta hz0 hroot).block chain z0 D delta eIndex)
      (((mtGeometricLevel delta start i1.1 * mtGeometricLevel delta start i2.1 *
          mtGeometricLevel delta start i3.1) *
          ∏ j ∈ chain.toFinset, mtGeometricLevel delta start j.1) *
        mtUpperAdicScale delta eIndex)
      ((1 + delta) ^ (chain.length + 4) *
        (((mtGeometricLevel delta start i1.1 * mtGeometricLevel delta start i2.1 *
            mtGeometricLevel delta start i3.1) *
            ∏ j ∈ chain.toFinset, mtGeometricLevel delta start j.1) *
          mtUpperAdicScale delta eIndex)) := by
  let Q : Fin (mtMinimalGeometricDepth delta start z hdelta) → ℝ :=
    fun i => mtGeometricLevel delta start i.1
  let b : ℝ := 1 + delta
  let E : ℝ := mtUpperAdicScale delta eIndex
  let source := MTFiniteIterationSourceData.ofMinimalGeometricSchedule
    z0 D start delta z hdelta hz0 hroot
  have hraw : MTRealScaleSupported
      (mtBlockChainLongAF
        (mtHarmanTripleCellCoefficient
          (source.block i1) (source.block i2) (source.block i3))
        source.block chain z0 D delta eIndex)
      ((((Q i1 * Q i2) * Q i3) * ∏ j ∈ chain.toFinset, Q j) * E)
      (((((Q i1 * b) * (Q i2 * b)) * (Q i3 * b)) *
          ∏ j ∈ chain.toFinset, Q j * b) * (b * E)) :=
    mtBlockChainLongAF_scaleSupported
      (mtMinimalGeometricTripleCell_scaleSupported
        z0 D start hdelta hz0 hroot i1 i2 i3)
      (fun i => mtMinimalGeometricBlock_scaleSupported z0 D start hdelta hz0 hroot i)
      (fun i => (mtGeometricLevel_pos hdelta start i.1).le)
      (mul_nonneg (mul_nonneg (mtGeometricLevel_pos hdelta start i1.1).le
        (mtGeometricLevel_pos hdelta start i2.1).le)
        (mtGeometricLevel_pos hdelta start i3.1).le)
      hchain z0 D eIndex (mtUpperAdicScale_pos hdelta eIndex).le
  intro n hn
  have hs := hraw hn
  refine ⟨hs.1, hs.2.1, hs.2.2.trans_eq ?_⟩
  change
    ((((Q i1 * b) * (Q i2 * b)) * (Q i3 * b)) *
      (∏ j ∈ chain.toFinset, Q j * b)) * (b * E) =
      b ^ (chain.length + 4) * ((((Q i1 * Q i2) * Q i3) *
        ∏ j ∈ chain.toFinset, Q j) * E)
  rw [prod_mul_constant_chain_toFinset Q b hchain, pow_add]
  ring

end

end RHTower.Sieve
