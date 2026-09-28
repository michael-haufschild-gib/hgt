import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenSeparatedTripleBoxClassification

/-!
# Classification of literal paper-aligned Harman boxes

Aligned outer endpoint bounds and active-cell predicates discharge the scalar hypotheses of the
independent-schedule pair and triple classification theorems.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

theorem mtPaperAlignedEndpoint_lowerScale_le_target
    {z D : ℕ} {delta : ℝ} (hz : 1 ≤ z) (hzD : z ≤ D)
    (hdelta : 0 ≤ delta) (hprogress : 1 ≤ delta * ((z - 1 : ℕ) : ℝ))
    (i : ℕ) :
    mtAdjacentBlockLowerScale (mtPaperAlignedEndpoint z D delta) i ≤ (D : ℝ) := by
  have hi := (mtPaperAlignedEndpoint_mem_Icc hz hzD hdelta hprogress i).2
  unfold mtAdjacentBlockLowerScale
  exact_mod_cast (by omega : mtPaperAlignedEndpoint z D delta i - 1 ≤ D)

theorem mtAdjacentBlockLowerScale_le_upperScale_of_monotone
    {endpoint : ℕ → ℕ} (hmono : Monotone endpoint) (i : ℕ) :
    mtAdjacentBlockLowerScale endpoint i ≤ mtAdjacentBlockUpperScale endpoint i := by
  unfold mtAdjacentBlockLowerScale mtAdjacentBlockUpperScale
  have he : endpoint i ≤ endpoint (i + 1) := hmono (by omega)
  exact_mod_cast Nat.sub_le_sub_right he 1

/-- A literal aligned pair box in the retained product range has one exact proposition form. -/
theorem mtPaperAlignedSeparatedPairBox_isProposition22Piece
    {X Y z0Real epsilon : ℝ}
    (z0 outerStart z Douter Dtrunc recStart : ℕ)
    {delta recRoot : ℝ} (hdelta : 0 < delta)
    (houterStart : 2 ≤ outerStart) (houterD : outerStart ≤ Douter)
    (hprogress : 1 ≤ delta * ((outerStart - 1 : ℕ) : ℝ))
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta recStart 0)
    (hroot : mtGeometricLevel delta recStart 0 < recRoot)
    (data : MTFiniteIterationSourceData
      (mtMinimalGeometricDepth delta recStart recRoot hdelta))
    (hblocks : data.block =
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 Dtrunc recStart delta recRoot hdelta hz0 hroot).block)
    (i1 i2 : Fin (Douter - outerStart))
    (chain : List (Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta)))
    (hchain : chain.Nodup) (eIndex kIndex : ℕ)
    (hX : 1 < X) (hepsilon0 : 0 < epsilon) (hepsilon : epsilon ≤ 2 / 11)
    (hrecRoot : recRoot = X ^ (2 / 11 : ℝ))
    (hrootOne : 1 ≤ mtGeometricLevel delta recStart 0)
    (hDcap : (Douter : ℝ) ≤ X ^ (1 / 4 - 2 * epsilon))
    (hE : mtUpperAdicScale delta eIndex ≤ X ^ (epsilon / 4))
    (hz0RealPos : 0 < z0Real)
    (hz0RealLevel : z0Real ≤ mtGeometricLevel delta recStart 0)
    (hchainCard : chain.toFinset.card ≤
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
  have hendpoint : ∀ i, 2 ≤ mtPaperAlignedEndpoint outerStart Douter delta i :=
    fun i => houterStart.trans
      (mtPaperAlignedEndpoint_mem_Icc
        (by omega) houterD hdelta.le hprogress i).1
  apply mtSeparatedPairBox_isProposition22Piece
    hendpoint (mtPaperAlignedEndpoint_band hdelta.le) (primesIco z Douter)
    z0 Dtrunc recStart hdelta hz0 hroot data hblocks i1 i2 chain hchain eIndex kIndex
    hX hepsilon0 hepsilon hrecRoot hrootOne hE
  · exact (mtPaperAlignedEndpoint_lowerScale_le_target
      (by omega) houterD hdelta.le hprogress i1.1).trans hDcap
  · exact (mtPaperAlignedEndpoint_lowerScale_le_target
      (by omega) houterD hdelta.le hprogress i2.1).trans hDcap
  · exact hz0RealPos
  · exact hz0RealLevel
  · exact Or.inr hchainCard
  · exact hdilation
  · exact hproduct

/-- A literal active aligned triple box in the retained range has one exact proposition form. -/
theorem mtPaperAlignedSeparatedTripleBox_isProposition22Piece
    {X Y z0Real epsilon E : ℝ}
    (z0 outerStart z Douter Dtrunc recStart : ℕ)
    {delta recRoot : ℝ} (hdelta : 0 < delta)
    (houterStart : 2 ≤ outerStart) (houterD : outerStart ≤ Douter)
    (hprogress : 1 ≤ delta * ((outerStart - 1 : ℕ) : ℝ))
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta recStart 0)
    (hroot : mtGeometricLevel delta recStart 0 < recRoot)
    (data : MTFiniteIterationSourceData
      (mtMinimalGeometricDepth delta recStart recRoot hdelta))
    (hblocks : data.block =
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 Dtrunc recStart delta recRoot hdelta hz0 hroot).block)
    (i1 i2 i3 : Fin (Douter - outerStart))
    (hcell : ((i1, i2), i3) ∈ mtHarmanActiveGoodTripleCells
      (mtPaperAlignedEndpoint outerStart Douter delta) E)
    (chain : List (Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta)))
    (hchain : chain.Nodup) (eIndex kIndex : ℕ)
    (hX : 1 < X) (hepsilon0 : 0 < epsilon) (hepsilon : epsilon ≤ 2 / 11)
    (hrecRoot : recRoot = X ^ (2 / 11 : ℝ))
    (hrootOne : 1 ≤ mtGeometricLevel delta recStart 0)
    (hDcap : (Douter : ℝ) ≤ X ^ (1 / 4 - 2 * epsilon))
    (hEthreshold : E ≤ X ^ (1 - 2 * epsilon))
    (hE : mtUpperAdicScale delta eIndex ≤ X ^ (epsilon / 4))
    (hz0RealPos : 0 < z0Real)
    (hz0RealLevel : z0Real ≤ mtGeometricLevel delta recStart 0)
    (hchainCard : chain.toFinset.card ≤
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
    calc
      mtAdjacentBlockLowerScale endpoint i1.1 *
          mtAdjacentBlockLowerScale endpoint i2.1 ^ (4 : ℕ) ≤
        mtAdjacentBlockUpperScale endpoint i1.1 *
          mtAdjacentBlockUpperScale endpoint i2.1 ^ (4 : ℕ) := by
        exact mul_le_mul hL1U1
          (pow_le_pow_left₀ hL2 hL2U2 4) (pow_nonneg (Nat.cast_nonneg _) _ ) hU1
      _ ≤ E := hcellData.2.2.le
      _ ≤ X ^ (1 - 2 * epsilon) := hEthreshold
  apply mtSeparatedTripleBox_isProposition22Piece
    hendpoint (mtPaperAlignedEndpoint_band hdelta.le) (primesIco z Douter)
    z0 Dtrunc recStart hdelta hz0 hroot data hblocks i1 i2 i3 chain hchain
    eIndex kIndex hX hepsilon0 hepsilon hrecRoot hrootOne hE
  · exact (mtPaperAlignedEndpoint_lowerScale_le_target
      (by omega) houterD hdelta.le hprogress i1.1).trans hDcap
  · exact hQ3Q2
  · exact hgeometry
  · exact hz0RealPos
  · exact hz0RealLevel
  · exact Or.inr hchainCard
  · exact hdilation
  · exact hproduct

end

end RHTower.Sieve
