import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenRetainedBoxFamily
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenAlignedBoxFamilyClassification

/-!
# Classification of every retained tagged box

One shared set of paper-scale hypotheses is threaded through all four tagged families.  Membership
supplies the active recursive chain, adic ranges, active Harman cell, and exact product interval.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

local instance instDecidableEqMTTripleSeparatedBoxIndexRetainedClassification
    (u t : ℕ) : DecidableEq (MTTripleSeparatedBoxIndex u t) := Classical.decEq _

set_option maxHeartbeats 600000 in
/-- Every retained base, one-prime, pair, or triple box has one literal Proposition 2.2 form. -/
theorem mtHarmanRetainedBox_isProposition22Piece
    {X Y z0Real epsilon : ℝ}
    (z0 outerStart z Qouter Douter Dtrunc recStart : ℕ)
    {delta recRoot E : ℝ} (hdelta : 0 < delta)
    (houterStart : 2 ≤ outerStart)
    (houterQ : outerStart ≤ Qouter) (houterD : outerStart ≤ Douter)
    (hprogress : 1 ≤ delta * ((outerStart - 1 : ℕ) : ℝ))
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
    (N : ℕ)
    (hX : 1 < X) (hepsilon0 : 0 < epsilon) (hepsilon : epsilon ≤ 2 / 11)
    (hrecRoot : recRoot = X ^ (2 / 11 : ℝ))
    (hrootOne : 1 ≤ mtGeometricLevel delta recStart 0)
    (hDcap : (Douter : ℝ) ≤ X ^ (1 / 4 - 2 * epsilon))
    (hEthreshold : E ≤ X ^ (1 - 2 * epsilon))
    (hz0RealPos : 0 < z0Real)
    (hz0RealLevel : z0Real ≤ mtGeometricLevel delta recStart 0)
    (hmaxDepth : maxDepth ≤ Nat.floor (Real.log recRoot / Real.log z0Real))
    (hdilation : ∀ R : ℕ, R ≤ maxDepth + 5 → (1 + delta) ^ R ≤ 2)
    (heScale : ∀ e : ℕ, e ≤ mtUpperAdicIndex delta data.D →
      mtUpperAdicScale delta e ≤ X ^ (epsilon / 4))
    (hbaseSmall : ∀ e : ℕ, e ≤ mtUpperAdicIndex delta data.D →
      mtUpperAdicScale delta e * mtBaseOuterScale delta (0 : Fin 1) *
        X ^ (epsilon / 2) ≤ X ^ (1 / 2 + epsilon))
    (honeSmall : ∀ (i : Fin (Qouter - outerStart)) (e : ℕ),
      e ≤ mtUpperAdicIndex delta data.D →
      mtUpperAdicScale delta e *
        mtOnePrimeOuterScale (mtPaperAlignedEndpoint outerStart Qouter delta) i *
        X ^ (epsilon / 2) ≤ X ^ (1 / 2 + epsilon))
    (idx : MTHarmanRetainedBoxIndex
      (Qouter - outerStart) (Douter - outerStart)
      (mtMinimalGeometricDepth delta recStart recRoot hdelta))
    (hidx : idx ∈ mtHarmanRetainedBoxIndexSet
      (outerQ := Qouter - outerStart) (outerD := Douter - outerStart)
      (mtPaperAlignedEndpoint outerStart Qouter delta)
      (mtPaperAlignedEndpoint outerStart Douter delta) E data maxDepth j delta
      N recStart Y) :
    MTUniformProposition22Piece 5 X Y z0Real recRoot delta epsilon
      (mtHarmanRetainedBoxAF
        (mtPaperAlignedEndpoint outerStart Qouter delta)
        (mtPaperAlignedEndpoint outerStart Douter delta)
        z Qouter Douter data delta idx) := by
  let endpointQ := mtPaperAlignedEndpoint outerStart Qouter delta
  let endpointD := mtPaperAlignedEndpoint outerStart Douter delta
  let Pq := primesIco z Qouter
  let Pd := primesIco z Douter
  have hendpointQ : ∀ i, 2 ≤ endpointQ i := fun i =>
    houterStart.trans
      (mtPaperAlignedEndpoint_mem_Icc (by omega) houterQ hdelta.le hprogress i).1
  cases idx with
  | inl idx =>
      have hmem : idx ∈ mtProductScaleIndices
          (mtOuterSeparatedBoxIndexSet (Finset.univ : Finset (Fin 1))
            data maxDepth j (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N))
          (mtOuterSeparatedBoxScale (mtBaseOuterScale delta) delta recStart) Y := by
        simpa [mtHarmanRetainedBoxIndexSet] using hidx
      have hproduct := (Finset.mem_filter.mp hmem).2
      have hset := (Finset.mem_filter.mp hmem).1
      rw [mtOuterSeparatedBoxIndexSet] at hset
      have hk := Finset.mem_product.mp hset
      have he := Finset.mem_product.mp hk.1
      have hidc := Finset.mem_product.mp he.1
      have hdc := mem_mtAllActiveBlockChains.mp hidc.2
      have hchain := hdc.2
      have hlength : idx.1.1.2.2.length ≤ maxDepth := by
        rw [length_eq_of_mem_mtActiveBlockChains hchain]
        exact Nat.le_of_lt_succ (Finset.mem_range.mp hdc.1)
      have heIndex : idx.1.2 ≤ mtUpperAdicIndex delta data.D := by
        have := Finset.mem_range.mp he.2
        omega
      simp only [mtHarmanRetainedBoxAF, mtOuterSeparatedBoxAF, mtBaseOuterAlpha]
      rw [hz0Data, hDData]
      change MTUniformProposition22Piece 5 X Y z0Real recRoot delta epsilon
        (mtSignedBlockChainAdicBoxAF mtUnitCoefficient data.block idx.1.1.2.2
          z0 Dtrunc delta idx.1.2 idx.2)
      apply mtOuterBlockChainBox_isProposition22Piece
        (mtUnitCoefficientAF_scaleSupported hdelta)
        mtUnitCoefficient_polynomialDivisorBounded
        mtUnitCoefficient_uniformDivisorBounded
        (mtBaseOuterScale_pos hdelta (0 : Fin 1))
        z0 Dtrunc recStart hdelta hz0 hroot data hblocks
        idx.1.1.2.2 (activeBlockChain_nodup hchain) idx.1.2 idx.2
        hX hepsilon0 hepsilon hrecRoot hrootOne hz0RealPos hz0RealLevel
      · exact Or.inr ((List.toFinset_card_le _).trans (hlength.trans hmaxDepth))
      · intro R hR
        exact hdilation R (by omega)
      · exact hbaseSmall idx.1.2 heIndex
      · simpa [mtOuterSeparatedBoxScale, mtBaseOuterScale] using hproduct
  | inr rest =>
      cases rest with
      | inl idx =>
          have hmem : idx ∈ mtProductScaleIndices
              (mtOuterSeparatedBoxIndexSet
                (Finset.univ : Finset (Fin (Qouter - outerStart)))
                data maxDepth j (mtUpperAdicIndex delta data.D)
                  (mtUpperAdicIndex delta N))
              (mtOuterSeparatedBoxScale (mtOnePrimeOuterScale endpointQ)
                delta recStart) Y := by
            simpa [mtHarmanRetainedBoxIndexSet, endpointQ, endpointD] using hidx
          have hproduct := (Finset.mem_filter.mp hmem).2
          have hset := (Finset.mem_filter.mp hmem).1
          rw [mtOuterSeparatedBoxIndexSet] at hset
          have hk := Finset.mem_product.mp hset
          have he := Finset.mem_product.mp hk.1
          have hidc := Finset.mem_product.mp he.1
          have hdc := mem_mtAllActiveBlockChains.mp hidc.2
          have hchain := hdc.2
          have hlength : idx.1.1.2.2.length ≤ maxDepth := by
            rw [length_eq_of_mem_mtActiveBlockChains hchain]
            exact Nat.le_of_lt_succ (Finset.mem_range.mp hdc.1)
          have heIndex : idx.1.2 ≤ mtUpperAdicIndex delta data.D := by
            have := Finset.mem_range.mp he.2
            omega
          simp only [mtHarmanRetainedBoxAF, mtOuterSeparatedBoxAF]
          rw [hz0Data, hDData]
          change MTUniformProposition22Piece 5 X Y z0Real recRoot delta epsilon
            (-mtSignedBlockChainAdicBoxAF
              (mtOnePrimeOuterAlpha endpointQ Pq idx.1.1.1)
              data.block idx.1.1.2.2 z0 Dtrunc delta idx.1.2 idx.2)
          apply MTUniformProposition22Piece.neg
          apply mtOuterBlockChainBox_isProposition22Piece
            (mtOnePrimeOuterAlpha_scaleSupported
              (fun i => (hendpointQ i).trans' one_le_two)
              (mtPaperAlignedEndpoint_band hdelta.le) Pq idx.1.1.1)
            (mtFinsetIndicatorCoefficient_polynomialDivisorBounded _)
            (mtFinsetIndicatorCoefficient_uniformDivisorBounded _)
            (mtOnePrimeOuterScale_pos hendpointQ idx.1.1.1)
            z0 Dtrunc recStart hdelta hz0 hroot data hblocks
            idx.1.1.2.2 (activeBlockChain_nodup hchain) idx.1.2 idx.2
            hX hepsilon0 hepsilon hrecRoot hrootOne hz0RealPos hz0RealLevel
          · exact Or.inr ((List.toFinset_card_le _).trans (hlength.trans hmaxDepth))
          · intro R hR
            exact hdilation R (by omega)
          · exact honeSmall idx.1.1.1 idx.1.2 heIndex
          · simpa [mtOuterSeparatedBoxScale, endpointQ] using hproduct
      | inr tail =>
          cases tail with
          | inl idx =>
              have hmem : idx ∈ mtProductScaleIndices
                  (mtSeparatedPairBoxIndexSet (u := Douter - outerStart)
                    endpointD E data maxDepth j (mtUpperAdicIndex delta data.D)
                      (mtUpperAdicIndex delta N))
                  (mtSeparatedPairBoxScale endpointD delta recStart) Y := by
                simpa [mtHarmanRetainedBoxIndexSet, endpointQ, endpointD] using hidx
              have hproduct := (Finset.mem_filter.mp hmem).2
              have hset := (Finset.mem_filter.mp hmem).1
              rw [mtSeparatedPairBoxIndexSet] at hset
              have hk := Finset.mem_product.mp hset
              have he := Finset.mem_product.mp hk.1
              have hcellChain := Finset.mem_product.mp he.1
              have hdc := mem_mtAllActiveBlockChains.mp hcellChain.2
              have hchain := hdc.2
              have hlength : idx.1.1.2.2.length ≤ maxDepth := by
                rw [length_eq_of_mem_mtActiveBlockChains hchain]
                exact Nat.le_of_lt_succ (Finset.mem_range.mp hdc.1)
              have heIndex : idx.1.2 ≤ mtUpperAdicIndex delta data.D := by
                have := Finset.mem_range.mp he.2
                omega
              simp only [mtHarmanRetainedBoxAF, mtSeparatedPairBoxAF]
              rw [hz0Data, hDData]
              change MTUniformProposition22Piece 5 X Y z0Real recRoot delta epsilon
                (mtSignedBlockChainAdicBoxAF
                  (mtHarmanPairCellCoefficient
                    (mtHarmanSourceBlock endpointD Pd idx.1.1.1.1)
                    (mtHarmanSourceBlock endpointD Pd idx.1.1.1.2))
                  data.block idx.1.1.2.2 z0 Dtrunc delta idx.1.2 idx.2)
              apply mtPaperAlignedSeparatedPairBox_isProposition22Piece
                z0 outerStart z Douter Dtrunc recStart hdelta houterStart houterD
                hprogress hz0 hroot data hblocks idx.1.1.1.1 idx.1.1.1.2
                idx.1.1.2.2 (activeBlockChain_nodup hchain) idx.1.2 idx.2
                hX hepsilon0 hepsilon hrecRoot hrootOne hDcap
                (heScale idx.1.2 heIndex) hz0RealPos hz0RealLevel
              · exact (List.toFinset_card_le _).trans (hlength.trans hmaxDepth)
              · intro R hR
                exact hdilation R (by omega)
              · simpa [mtSeparatedPairBoxScale, endpointD] using hproduct
          | inr idx =>
              have hmem : idx ∈ mtProductScaleIndices
                  (mtSeparatedTripleBoxIndexSet (u := Douter - outerStart)
                    endpointD E data maxDepth j (mtUpperAdicIndex delta data.D)
                      (mtUpperAdicIndex delta N))
                  (mtSeparatedTripleBoxScale endpointD delta recStart) Y := by
                simpa [mtHarmanRetainedBoxIndexSet, endpointQ, endpointD] using hidx
              have hproduct := (Finset.mem_filter.mp hmem).2
              have hset := (Finset.mem_filter.mp hmem).1
              rw [mtSeparatedTripleBoxIndexSet] at hset
              have hk := Finset.mem_product.mp hset
              have he := Finset.mem_product.mp hk.1
              have hcellChain := Finset.mem_product.mp he.1
              have hdc := mem_mtAllActiveBlockChains.mp hcellChain.2
              have hchain := hdc.2
              have hlength : idx.1.1.2.2.length ≤ maxDepth := by
                rw [length_eq_of_mem_mtActiveBlockChains hchain]
                exact Nat.le_of_lt_succ (Finset.mem_range.mp hdc.1)
              have heIndex : idx.1.2 ≤ mtUpperAdicIndex delta data.D := by
                have := Finset.mem_range.mp he.2
                omega
              simp only [mtHarmanRetainedBoxAF, mtSeparatedTripleBoxAF]
              rw [hz0Data, hDData]
              change MTUniformProposition22Piece 5 X Y z0Real recRoot delta epsilon
                (-mtSignedBlockChainAdicBoxAF
                  (mtHarmanTripleCellCoefficient
                    (mtHarmanSourceBlock endpointD Pd idx.1.1.1.1.1)
                    (mtHarmanSourceBlock endpointD Pd idx.1.1.1.1.2)
                    (mtHarmanSourceBlock endpointD Pd idx.1.1.1.2))
                  data.block idx.1.1.2.2 z0 Dtrunc delta idx.1.2 idx.2)
              apply MTUniformProposition22Piece.neg
              apply mtPaperAlignedSeparatedTripleBox_isProposition22Piece
                z0 outerStart z Douter Dtrunc recStart hdelta houterStart houterD
                hprogress hz0 hroot data hblocks idx.1.1.1.1.1 idx.1.1.1.1.2
                idx.1.1.1.2 hcellChain.1 idx.1.1.2.2
                (activeBlockChain_nodup hchain) idx.1.2 idx.2
                hX hepsilon0 hepsilon hrecRoot hrootOne hDcap hEthreshold
                (heScale idx.1.2 heIndex) hz0RealPos hz0RealLevel
              · exact (List.toFinset_card_le _).trans (hlength.trans hmaxDepth)
              · intro R hR
                exact hdilation R (by omega)
              · simpa [mtSeparatedTripleBoxScale, endpointD] using hproduct

end

end RHTower.Sieve
