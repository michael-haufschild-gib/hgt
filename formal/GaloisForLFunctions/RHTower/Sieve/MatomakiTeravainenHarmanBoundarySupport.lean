import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanBoundaryMoment
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenProductScaleBoundarySupport

/-!
# Support of the complete Harman product boundary

Each of the four box families has the same product-scale dilation collar.  Their signed sum is
therefore supported in the paper's coarse error interval `(Y/4,8Y]`.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

local instance instDecidableEqMTTripleSeparatedBoxIndexHarmanBoundarySupport (u t : ℕ) :
    DecidableEq (MTTripleSeparatedBoxIndex u t) := Classical.decEq _

theorem mtOuterSeparatedBoxFamily_productBoundary_support_four_eight
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (alpha : ι → ℕ → ℂ) (L : ι → ℝ)
    (z0 D recStart : ℕ) {recRoot delta : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta recStart 0)
    (hroot : mtGeometricLevel delta recStart 0 < recRoot)
    (data : MTFiniteIterationSourceData
      (mtMinimalGeometricDepth delta recStart recRoot hdelta))
    (hblocks : data.block =
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D recStart delta recRoot hdelta hz0 hroot).block)
    (halpha : ∀ i ∈ S,
      MTRealScaleSupported (mtCoefficientAF (alpha i)) (L i) ((1 + delta) * L i))
    (hL : ∀ i ∈ S, 0 < L i)
    (maxDepth : ℕ)
    (j : Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta + 1))
    (eMax kMax : ℕ) {Y eta : ℝ} (hY : 0 < Y) (heta : 0 ≤ eta)
    (hetaOne : eta ≤ 1)
    (hdilation : (1 + delta) ^ (maxDepth + 3) ≤ 1 + eta)
    {n : ℕ}
    (hn : mtProductScaleBoundaryErrorAF
      (mtOuterSeparatedBoxIndexSet S data maxDepth j eMax kMax)
      (mtOuterSeparatedBoxAF alpha data z0 D delta)
      (mtOuterSeparatedBoxScale L delta recStart) Y n ≠ 0) :
    Y / 4 < (n : ℝ) ∧ (n : ℝ) ≤ 8 * Y := by
  apply mtProductScaleBoundaryErrorAF_support_four_eight
    (mtOuterSeparatedBoxIndexSet S data maxDepth j eMax kMax)
    (mtOuterSeparatedBoxAF alpha data z0 D delta)
    (mtOuterSeparatedBoxScale L delta recStart) hY heta hetaOne
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
      z0 D recStart hdelta hz0 hroot data hblocks
      (activeBlockChain_nodup hchain) maxDepth idx.1.2 idx.2
    · rw [length_eq_of_mem_mtActiveBlockChains hchain]
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hdc.1)
    · exact hdilation
  · exact hn

theorem mtSeparatedPairBoxFamily_productBoundary_support_four_eight
    {u : ℕ} {delta : ℝ} (endpoint : ℕ → ℕ) (P : Finset ℕ)
    (hendpoint : ∀ i, 2 ≤ endpoint i)
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
    {Y eta : ℝ} (hY : 0 < Y) (heta : 0 ≤ eta) (hetaOne : eta ≤ 1)
    (hdilation : (1 + delta) ^ (maxDepth + 5) ≤ 1 + eta)
    {n : ℕ}
    (hn : mtProductScaleBoundaryErrorAF
      (mtSeparatedPairBoxIndexSet (u := u) endpoint E data maxDepth j eMax kMax)
      (mtSeparatedPairBoxAF endpoint P data z0 D delta)
      (mtSeparatedPairBoxScale endpoint delta recStart) Y n ≠ 0) :
    Y / 4 < (n : ℝ) ∧ (n : ℝ) ≤ 8 * Y := by
  apply mtProductScaleBoundaryErrorAF_support_four_eight
    (mtSeparatedPairBoxIndexSet (u := u) endpoint E data maxDepth j eMax kMax)
    (mtSeparatedPairBoxAF endpoint P data z0 D delta)
    (mtSeparatedPairBoxScale endpoint delta recStart) hY heta hetaOne
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
  · exact hn

theorem mtSeparatedTripleBoxFamily_productBoundary_support_four_eight
    {u : ℕ} {delta : ℝ} (endpoint : ℕ → ℕ) (P : Finset ℕ)
    (hendpoint : ∀ i, 2 ≤ endpoint i)
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
    {Y eta : ℝ} (hY : 0 < Y) (heta : 0 ≤ eta) (hetaOne : eta ≤ 1)
    (hdilation : (1 + delta) ^ (maxDepth + 5) ≤ 1 + eta)
    {n : ℕ}
    (hn : mtProductScaleBoundaryErrorAF
      (mtSeparatedTripleBoxIndexSet (u := u) endpoint E data maxDepth j eMax kMax)
      (mtSeparatedTripleBoxAF endpoint P data z0 D delta)
      (mtSeparatedTripleBoxScale endpoint delta recStart) Y n ≠ 0) :
    Y / 4 < (n : ℝ) ∧ (n : ℝ) ≤ 8 * Y := by
  apply mtProductScaleBoundaryErrorAF_support_four_eight
    (mtSeparatedTripleBoxIndexSet (u := u) endpoint E data maxDepth j eMax kMax)
    (mtSeparatedTripleBoxAF endpoint P data z0 D delta)
    (mtSeparatedTripleBoxScale endpoint delta recStart) hY heta hetaOne
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
  · exact hn

set_option maxHeartbeats 600000 in
/-- Complete signed Harman product boundary is supported in `(Y/4,8Y]`. -/
theorem mtHarmanProductBoundaryErrorAF_support_four_eight
    {outerQ outerD : ℕ} {delta : ℝ}
    (endpointQ endpointD : ℕ → ℕ) (z Q D : ℕ) (E : ℝ)
    (hendpointQ : ∀ i, 2 ≤ endpointQ i)
    (hbandQ : ∀ i, mtAdjacentBlockUpperScale endpointQ i ≤
      (1 + delta) * mtAdjacentBlockLowerScale endpointQ i)
    (hendpointD : ∀ i, 2 ≤ endpointD i)
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
    (N : ℕ) {Y eta : ℝ} (hY : 0 < Y) (heta : 0 ≤ eta) (hetaOne : eta ≤ 1)
    (hdilation : (1 + delta) ^ (maxDepth + 5) ≤ 1 + eta)
    {n : ℕ}
    (hn : mtHarmanProductBoundaryErrorAF
      (outerQ := outerQ) (outerD := outerD) endpointQ endpointD z Q D E
      data maxDepth j delta N recStart Y n ≠ 0) :
    Y / 4 < (n : ℝ) ∧ (n : ℝ) ≤ 8 * Y := by
  let e0 := mtProductScaleBoundaryErrorAF
    (mtOuterSeparatedBoxIndexSet (Finset.univ : Finset (Fin 1))
      data maxDepth j (mtUpperAdicIndex delta Dtrunc) (mtUpperAdicIndex delta N))
    (mtOuterSeparatedBoxAF mtBaseOuterAlpha data z0 Dtrunc delta)
    (mtOuterSeparatedBoxScale (mtBaseOuterScale delta) delta recStart) Y
  let e1 := mtProductScaleBoundaryErrorAF
    (mtOuterSeparatedBoxIndexSet (Finset.univ : Finset (Fin outerQ))
      data maxDepth j (mtUpperAdicIndex delta Dtrunc) (mtUpperAdicIndex delta N))
    (mtOuterSeparatedBoxAF (mtOnePrimeOuterAlpha endpointQ (primesIco z Q))
      data z0 Dtrunc delta)
    (mtOuterSeparatedBoxScale (mtOnePrimeOuterScale endpointQ) delta recStart) Y
  let e2 := mtProductScaleBoundaryErrorAF
    (mtSeparatedPairBoxIndexSet (u := outerD) endpointD E data maxDepth j
      (mtUpperAdicIndex delta Dtrunc) (mtUpperAdicIndex delta N))
    (mtSeparatedPairBoxAF endpointD (primesIco z D) data z0 Dtrunc delta)
    (mtSeparatedPairBoxScale endpointD delta recStart) Y
  let e3 := mtProductScaleBoundaryErrorAF
    (mtSeparatedTripleBoxIndexSet (u := outerD) endpointD E data maxDepth j
      (mtUpperAdicIndex delta Dtrunc) (mtUpperAdicIndex delta N))
    (mtSeparatedTripleBoxAF endpointD (primesIco z D) data z0 Dtrunc delta)
    (mtSeparatedTripleBoxScale endpointD delta recStart) Y
  have hdilation3 : (1 + delta) ^ (maxDepth + 3) ≤ 1 + eta :=
    (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + delta)
      (by omega : maxDepth + 3 ≤ maxDepth + 5)).trans hdilation
  have h0 : ∀ {n : ℕ}, e0 n ≠ 0 → Y / 4 < (n : ℝ) ∧ (n : ℝ) ≤ 8 * Y := by
    intro m hm
    exact mtOuterSeparatedBoxFamily_productBoundary_support_four_eight
      (Finset.univ : Finset (Fin 1)) mtBaseOuterAlpha (mtBaseOuterScale delta)
      z0 Dtrunc recStart hdelta hz0 hroot data hblocks
      (fun i hi => mtUnitCoefficientAF_scaleSupported hdelta)
      (fun i hi => mtBaseOuterScale_pos hdelta i)
      maxDepth j (mtUpperAdicIndex delta Dtrunc) (mtUpperAdicIndex delta N)
      hY heta hetaOne hdilation3 hm
  have h1 : ∀ {n : ℕ}, e1 n ≠ 0 → Y / 4 < (n : ℝ) ∧ (n : ℝ) ≤ 8 * Y := by
    intro m hm
    exact mtOuterSeparatedBoxFamily_productBoundary_support_four_eight
      (Finset.univ : Finset (Fin outerQ))
      (mtOnePrimeOuterAlpha endpointQ (primesIco z Q))
      (mtOnePrimeOuterScale endpointQ) z0 Dtrunc recStart hdelta hz0 hroot data hblocks
      (fun i hi => mtOnePrimeOuterAlpha_scaleSupported
        (fun k => (hendpointQ k).trans' one_le_two) hbandQ (primesIco z Q) i)
      (fun i hi => mtOnePrimeOuterScale_pos hendpointQ i)
      maxDepth j (mtUpperAdicIndex delta Dtrunc) (mtUpperAdicIndex delta N)
      hY heta hetaOne hdilation3 hm
  have h2 : ∀ {n : ℕ}, e2 n ≠ 0 → Y / 4 < (n : ℝ) ∧ (n : ℝ) ≤ 8 * Y := by
    intro m hm
    exact mtSeparatedPairBoxFamily_productBoundary_support_four_eight
      endpointD (primesIco z D) hendpointD hbandD E z0 Dtrunc recStart
      hdelta hz0 hroot data hblocks maxDepth
      (mtUpperAdicIndex delta Dtrunc) (mtUpperAdicIndex delta N) j
      hY heta hetaOne hdilation hm
  have h3 : ∀ {n : ℕ}, e3 n ≠ 0 → Y / 4 < (n : ℝ) ∧ (n : ℝ) ≤ 8 * Y := by
    intro m hm
    exact mtSeparatedTripleBoxFamily_productBoundary_support_four_eight
      endpointD (primesIco z D) hendpointD hbandD E z0 Dtrunc recStart
      hdelta hz0 hroot data hblocks maxDepth
      (mtUpperAdicIndex delta Dtrunc) (mtUpperAdicIndex delta N) j
      hY heta hetaOne hdilation hm
  apply sub_add_sub_support_four e0 e1 e2 e3 h0 h1 h2 h3
  unfold mtHarmanProductBoundaryErrorAF at hn
  rw [hz0Data, hDData] at hn
  exact hn

end

end RHTower.Sieve
