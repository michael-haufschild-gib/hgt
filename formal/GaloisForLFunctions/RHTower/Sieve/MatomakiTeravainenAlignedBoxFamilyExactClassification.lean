import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenAlignedBoxFamilyClassification

/-!
# Exact-threshold classification of aligned Harman boxes

Natural source cutoffs are ceilings of the paper's real powers.  Nonempty aligned cells recover
the strict real bounds, so the resulting Proposition 2.2 pieces use the literal real thresholds
rather than their rounded natural cutoffs.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

theorem mtPaperAlignedEndpoint_lowerScale_lt_realTarget_of_nonempty
    {outerStart Douter : ℕ} {DReal delta : ℝ}
    (houterStart : 1 ≤ outerStart) (houterD : outerStart ≤ Douter)
    (hdelta : 0 ≤ delta) (hprogress : 1 ≤ delta * ((outerStart - 1 : ℕ) : ℝ))
    (hDouter : Douter = Nat.ceil DReal)
    (i : Fin (Douter - outerStart))
    (hactive : (mtAdjacentPrimeBlock
      (mtPaperAlignedEndpoint outerStart Douter delta) i).Nonempty) :
    mtAdjacentBlockLowerScale (mtPaperAlignedEndpoint outerStart Douter delta) i.1 <
      DReal := by
  obtain ⟨q, hq⟩ := hactive
  have hqData := mem_primesIco.mp hq
  have hendpointCap :=
    (mtPaperAlignedEndpoint_mem_Icc houterStart houterD hdelta hprogress (i.1 + 1)).2
  have hqD : q < Douter := hqData.2.1.trans_le hendpointCap
  have hqDReal : (q : ℝ) < DReal := by
    rw [hDouter] at hqD
    exact (Nat.lt_ceil).mp hqD
  have hlowerQ : mtAdjacentBlockLowerScale
      (mtPaperAlignedEndpoint outerStart Douter delta) i.1 ≤ (q : ℝ) := by
    unfold mtAdjacentBlockLowerScale
    have hnat : mtPaperAlignedEndpoint outerStart Douter delta i.1 - 1 ≤ q := by
      omega
    exact_mod_cast hnat
  exact hlowerQ.trans_lt hqDReal

theorem mtAdjacentUpperProduct_lt_realThreshold_of_ceil
    {t : ℕ} {endpoint : ℕ → ℕ} {EReal : ℝ} {i₁ i₂ : Fin t}
    (hproduct : mtAdjacentBlockUpperScale endpoint i₁ *
      mtAdjacentBlockUpperScale endpoint i₂ ^ (4 : ℕ) < (Nat.ceil EReal : ℝ)) :
    mtAdjacentBlockUpperScale endpoint i₁ *
      mtAdjacentBlockUpperScale endpoint i₂ ^ (4 : ℕ) < EReal := by
  let m : ℕ := (endpoint (i₁.1 + 1) - 1) * (endpoint (i₂.1 + 1) - 1) ^ (4 : ℕ)
  have hmCast : (m : ℝ) = mtAdjacentBlockUpperScale endpoint i₁ *
      mtAdjacentBlockUpperScale endpoint i₂ ^ (4 : ℕ) := by
    simp [m, mtAdjacentBlockUpperScale]
  have hm : m < Nat.ceil EReal := by
    exact_mod_cast (show (m : ℝ) < (Nat.ceil EReal : ℝ) by simpa [hmCast] using hproduct)
  rw [← hmCast]
  exact (Nat.lt_ceil).mp hm

/-- A nonempty aligned pair box with ceiling source cutoff has an exact Proposition 2.2 form. -/
theorem mtPaperAlignedSeparatedPairBox_isProposition22Piece_exactThreshold
    {X Y z0Real epsilon DReal EReal : ℝ}
    (z0 outerStart z Douter Dtrunc recStart : ℕ)
    {delta recRoot : ℝ} (hdelta : 0 < delta)
    (houterStart : 2 ≤ outerStart) (houterD : outerStart ≤ Douter)
    (hprogress : 1 ≤ delta * ((outerStart - 1 : ℕ) : ℝ))
    (hDouter : Douter = Nat.ceil DReal)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta recStart 0)
    (hroot : mtGeometricLevel delta recStart 0 < recRoot)
    (data : MTFiniteIterationSourceData
      (mtMinimalGeometricDepth delta recStart recRoot hdelta))
    (hblocks : data.block =
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 Dtrunc recStart delta recRoot hdelta hz0 hroot).block)
    (i1 i2 : Fin (Douter - outerStart))
    (hcell : (i1, i2) ∈ mtHarmanActiveGoodPairCells
      (mtPaperAlignedEndpoint outerStart Douter delta) (Nat.ceil EReal : ℝ))
    (chain : List (Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta)))
    (hchain : chain.Nodup) (eIndex kIndex : ℕ)
    (hX : 1 < X) (hepsilon0 : 0 < epsilon) (hepsilon : epsilon ≤ 2 / 11)
    (hrecRoot : recRoot = X ^ (2 / 11 : ℝ))
    (hrootOne : 1 ≤ mtGeometricLevel delta recStart 0)
    (hDRealCap : DReal ≤ X ^ (1 / 4 - 2 * epsilon))
    (hE : mtUpperAdicScale delta eIndex ≤ X ^ (epsilon / 4))
    (hz0RealPos : 0 < z0Real)
    (hz0RealLevel : z0Real ≤ mtGeometricLevel delta recStart 0)
    (hchainBound : 1 < z0Real ∨ chain.toFinset.card ≤
      Nat.floor (Real.log recRoot / Real.log z0Real))
    (hdilation : ∀ R : ℕ, R ≤ chain.length + 5 → (1 + delta) ^ R ≤ 2)
    (hproduct : Y / 2 <
        mtSeparatedPairBoxProductScale (mtPaperAlignedEndpoint outerStart Douter delta)
          delta recStart i1 i2 chain eIndex kIndex ∧
      mtSeparatedPairBoxProductScale (mtPaperAlignedEndpoint outerStart Douter delta)
          delta recStart i1 i2 chain eIndex kIndex ≤ 4 * Y) :
    MTUniformProposition22Piece 5 X Y z0Real recRoot delta epsilon
      (mtSignedBlockChainAdicBoxAF
        (mtHarmanPairCellCoefficient
          (mtHarmanSourceBlock (mtPaperAlignedEndpoint outerStart Douter delta)
            (primesIco z Douter) i1)
          (mtHarmanSourceBlock (mtPaperAlignedEndpoint outerStart Douter delta)
            (primesIco z Douter) i2))
        data.block chain z0 Dtrunc delta eIndex kIndex) := by
  let endpoint := mtPaperAlignedEndpoint outerStart Douter delta
  have hendpoint : ∀ i, 2 ≤ endpoint i := fun i =>
    houterStart.trans
      (mtPaperAlignedEndpoint_mem_Icc
        (by omega) houterD hdelta.le hprogress i).1
  have hactive := (mem_mtHarmanActiveGoodPairCells.mp hcell).2
  apply mtSeparatedPairBox_isProposition22Piece
    hendpoint (mtPaperAlignedEndpoint_band hdelta.le) (primesIco z Douter)
    z0 Dtrunc recStart hdelta hz0 hroot data hblocks i1 i2 chain hchain eIndex kIndex
    hX hepsilon0 hepsilon hrecRoot hrootOne hE
  · exact (mtPaperAlignedEndpoint_lowerScale_lt_realTarget_of_nonempty
      (by omega) houterD hdelta.le hprogress hDouter i1 hactive.1).le.trans hDRealCap
  · exact (mtPaperAlignedEndpoint_lowerScale_lt_realTarget_of_nonempty
      (by omega) houterD hdelta.le hprogress hDouter i2 hactive.2).le.trans hDRealCap
  · exact hz0RealPos
  · exact hz0RealLevel
  · exact hchainBound
  · exact hdilation
  · exact hproduct

/-- A nonempty aligned triple box with ceiling cutoffs has exact real paper thresholds. -/
theorem mtPaperAlignedSeparatedTripleBox_isProposition22Piece_exactThreshold
    {X Y z0Real epsilon DReal EReal : ℝ}
    (z0 outerStart z Douter Dtrunc recStart : ℕ)
    {delta recRoot : ℝ} (hdelta : 0 < delta)
    (houterStart : 2 ≤ outerStart) (houterD : outerStart ≤ Douter)
    (hprogress : 1 ≤ delta * ((outerStart - 1 : ℕ) : ℝ))
    (hDouter : Douter = Nat.ceil DReal)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta recStart 0)
    (hroot : mtGeometricLevel delta recStart 0 < recRoot)
    (data : MTFiniteIterationSourceData
      (mtMinimalGeometricDepth delta recStart recRoot hdelta))
    (hblocks : data.block =
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 Dtrunc recStart delta recRoot hdelta hz0 hroot).block)
    (i1 i2 i3 : Fin (Douter - outerStart))
    (hcell : ((i1, i2), i3) ∈ mtHarmanActiveGoodTripleCells
      (mtPaperAlignedEndpoint outerStart Douter delta) (Nat.ceil EReal : ℝ))
    (chain : List (Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta)))
    (hchain : chain.Nodup) (eIndex kIndex : ℕ)
    (hX : 1 < X) (hepsilon0 : 0 < epsilon) (hepsilon : epsilon ≤ 2 / 11)
    (hrecRoot : recRoot = X ^ (2 / 11 : ℝ))
    (hrootOne : 1 ≤ mtGeometricLevel delta recStart 0)
    (hDRealCap : DReal ≤ X ^ (1 / 4 - 2 * epsilon))
    (hERealCap : EReal ≤ X ^ (1 - 2 * epsilon))
    (hE : mtUpperAdicScale delta eIndex ≤ X ^ (epsilon / 4))
    (hz0RealPos : 0 < z0Real)
    (hz0RealLevel : z0Real ≤ mtGeometricLevel delta recStart 0)
    (hchainBound : 1 < z0Real ∨ chain.toFinset.card ≤
      Nat.floor (Real.log recRoot / Real.log z0Real))
    (hdilation : ∀ R : ℕ, R ≤ chain.length + 5 → (1 + delta) ^ R ≤ 2)
    (hproduct : Y / 2 <
        mtSeparatedTripleBoxProductScale (mtPaperAlignedEndpoint outerStart Douter delta)
          delta recStart i1 i2 i3 chain eIndex kIndex ∧
      mtSeparatedTripleBoxProductScale (mtPaperAlignedEndpoint outerStart Douter delta)
          delta recStart i1 i2 i3 chain eIndex kIndex ≤ 4 * Y) :
    MTUniformProposition22Piece 5 X Y z0Real recRoot delta epsilon
      (mtSignedBlockChainAdicBoxAF
        (mtHarmanTripleCellCoefficient
          (mtHarmanSourceBlock (mtPaperAlignedEndpoint outerStart Douter delta)
            (primesIco z Douter) i1)
          (mtHarmanSourceBlock (mtPaperAlignedEndpoint outerStart Douter delta)
            (primesIco z Douter) i2)
          (mtHarmanSourceBlock (mtPaperAlignedEndpoint outerStart Douter delta)
            (primesIco z Douter) i3))
        data.block chain z0 Dtrunc delta eIndex kIndex) := by
  let endpoint := mtPaperAlignedEndpoint outerStart Douter delta
  have hmono : Monotone endpoint :=
    mtPaperAlignedEndpoint_monotone (by omega) houterD hdelta.le hprogress
  have hendpoint : ∀ i, 2 ≤ endpoint i := fun i =>
    houterStart.trans
      (mtPaperAlignedEndpoint_mem_Icc
        (by omega) houterD hdelta.le hprogress i).1
  have hcellActive := (mem_mtHarmanActiveGoodTripleCells.mp hcell).2
  have hcellGood := (mem_mtHarmanActiveGoodTripleCells.mp hcell).1
  have hcellData := mem_mtHarmanGoodTripleCells.mp hcellGood
  have hQ3Q2 : mtAdjacentBlockLowerScale endpoint i3.1 ≤
      mtAdjacentBlockLowerScale endpoint i2.1 := by
    unfold mtAdjacentBlockLowerScale
    have he := hmono (Nat.le_of_lt hcellData.1)
    exact_mod_cast (by omega : endpoint i3.1 - 1 ≤ endpoint i2.1 - 1)
  have hL1U1 := mtAdjacentBlockLowerScale_le_upperScale_of_monotone hmono i1.1
  have hL2U2 := mtAdjacentBlockLowerScale_le_upperScale_of_monotone hmono i2.1
  have hU1 : 0 ≤ mtAdjacentBlockUpperScale endpoint i1.1 := Nat.cast_nonneg _
  have hL2 : 0 ≤ mtAdjacentBlockLowerScale endpoint i2.1 := Nat.cast_nonneg _
  have hgeometry : mtAdjacentBlockLowerScale endpoint i1.1 *
      mtAdjacentBlockLowerScale endpoint i2.1 ^ (4 : ℕ) ≤ X ^ (1 - 2 * epsilon) := by
    have hgeometryLt : mtAdjacentBlockLowerScale endpoint i1.1 *
        mtAdjacentBlockLowerScale endpoint i2.1 ^ (4 : ℕ) < X ^ (1 - 2 * epsilon) := by
      calc
      mtAdjacentBlockLowerScale endpoint i1.1 *
          mtAdjacentBlockLowerScale endpoint i2.1 ^ (4 : ℕ) ≤
        mtAdjacentBlockUpperScale endpoint i1.1 *
          mtAdjacentBlockUpperScale endpoint i2.1 ^ (4 : ℕ) := by
        exact mul_le_mul hL1U1
          (pow_le_pow_left₀ hL2 hL2U2 4) (pow_nonneg (Nat.cast_nonneg _) _) hU1
      _ < EReal := mtAdjacentUpperProduct_lt_realThreshold_of_ceil hcellData.2.2
      _ ≤ X ^ (1 - 2 * epsilon) := hERealCap
    exact hgeometryLt.le
  apply mtSeparatedTripleBox_isProposition22Piece
    hendpoint (mtPaperAlignedEndpoint_band hdelta.le) (primesIco z Douter)
    z0 Dtrunc recStart hdelta hz0 hroot data hblocks i1 i2 i3 chain hchain
    eIndex kIndex hX hepsilon0 hepsilon hrecRoot hrootOne hE
  · exact (mtPaperAlignedEndpoint_lowerScale_lt_realTarget_of_nonempty
      (by omega) houterD hdelta.le hprogress hDouter i1 hcellActive.1).le.trans hDRealCap
  · exact hQ3Q2
  · exact hgeometry
  · exact hz0RealPos
  · exact hz0RealLevel
  · exact hchainBound
  · exact hdilation
  · exact hproduct

end

end RHTower.Sieve
