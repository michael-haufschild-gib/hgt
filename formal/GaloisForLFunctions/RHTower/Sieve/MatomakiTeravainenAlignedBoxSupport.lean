import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenFullBoxBoundaryMoment

/-!
# Scale support for independent outer and recursive schedules

Literal Harman cells use the aligned outer partition of `[z,D)`.  Recursive Buchstab chains use a
different geometric partition of `[z₀,z)`.  This module keeps those schedules separate and proves
the common product-collar support needed by Proposition 2.2.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- A source-restricted aligned prime block inherits its exact shifted-endpoint scale band. -/
theorem mtHarmanSourceBlock_scaleSupported
    {u : ℕ} {endpoint : ℕ → ℕ} (hendpoint : ∀ i, 1 ≤ endpoint i)
    (P : Finset ℕ) (i : Fin u) :
    MTRealScaleSupported
      (mtPrimeBlockAF (mtHarmanSourceBlock endpoint P i))
      (mtAdjacentBlockLowerScale endpoint i.1)
      (mtAdjacentBlockUpperScale endpoint i.1) := by
  apply mtPrimeBlockAF_scaleSupported
  intro q hq
  exact (mem_mtAdjacentPrimeBlock_scale_iff hendpoint i q).mp
    (Finset.mem_inter.mp hq).1 |>.2

/-- Pair-cell coefficient support for an arbitrary aligned outer schedule. -/
theorem mtHarmanPairSourceCell_scaleSupported
    {u : ℕ} {endpoint : ℕ → ℕ} (hendpoint : ∀ i, 2 ≤ endpoint i)
    (P : Finset ℕ) (i1 i2 : Fin u) :
    MTRealScaleSupported
      (mtCoefficientAF (mtHarmanPairCellCoefficient
        (mtHarmanSourceBlock endpoint P i1)
        (mtHarmanSourceBlock endpoint P i2)))
      (mtAdjacentBlockLowerScale endpoint i1.1 *
        mtAdjacentBlockLowerScale endpoint i2.1)
      (mtAdjacentBlockUpperScale endpoint i1.1 *
        mtAdjacentBlockUpperScale endpoint i2.1) := by
  apply mtCoefficientAF_scaleSupported
  apply mtHarmanPairCellCoefficient_realSupport
  · have h := hendpoint i1.1
    change 0 < ((endpoint i1.1 - 1 : ℕ) : ℝ)
    exact_mod_cast (by omega : 0 < endpoint i1.1 - 1)
  · have h := hendpoint i2.1
    change 0 < ((endpoint i2.1 - 1 : ℕ) : ℝ)
    exact_mod_cast (by omega : 0 < endpoint i2.1 - 1)
  · intro q hq
    exact (mem_mtAdjacentPrimeBlock_scale_iff (fun i => (hendpoint i).trans' one_le_two) i1 q).mp
      (Finset.mem_inter.mp hq).1 |>.2
  · intro q hq
    exact (mem_mtAdjacentPrimeBlock_scale_iff (fun i => (hendpoint i).trans' one_le_two) i2 q).mp
      (Finset.mem_inter.mp hq).1 |>.2

/-- Triple-cell coefficient support for an arbitrary aligned outer schedule. -/
theorem mtHarmanTripleSourceCell_scaleSupported
    {u : ℕ} {endpoint : ℕ → ℕ} (hendpoint : ∀ i, 2 ≤ endpoint i)
    (P : Finset ℕ) (i1 i2 i3 : Fin u) :
    MTRealScaleSupported
      (mtCoefficientAF (mtHarmanTripleCellCoefficient
        (mtHarmanSourceBlock endpoint P i1)
        (mtHarmanSourceBlock endpoint P i2)
        (mtHarmanSourceBlock endpoint P i3)))
      (mtAdjacentBlockLowerScale endpoint i1.1 *
        mtAdjacentBlockLowerScale endpoint i2.1 *
        mtAdjacentBlockLowerScale endpoint i3.1)
      (mtAdjacentBlockUpperScale endpoint i1.1 *
        mtAdjacentBlockUpperScale endpoint i2.1 *
        mtAdjacentBlockUpperScale endpoint i3.1) := by
  apply mtCoefficientAF_scaleSupported
  apply mtHarmanTripleCellCoefficient_realSupport
  · have h := hendpoint i1.1
    change 0 < ((endpoint i1.1 - 1 : ℕ) : ℝ)
    exact_mod_cast (by omega : 0 < endpoint i1.1 - 1)
  · have h := hendpoint i2.1
    change 0 < ((endpoint i2.1 - 1 : ℕ) : ℝ)
    exact_mod_cast (by omega : 0 < endpoint i2.1 - 1)
  · have h := hendpoint i3.1
    change 0 < ((endpoint i3.1 - 1 : ℕ) : ℝ)
    exact_mod_cast (by omega : 0 < endpoint i3.1 - 1)
  · intro q hq
    exact (mem_mtAdjacentPrimeBlock_scale_iff (fun i => (hendpoint i).trans' one_le_two) i1 q).mp
      (Finset.mem_inter.mp hq).1 |>.2
  · intro q hq
    exact (mem_mtAdjacentPrimeBlock_scale_iff (fun i => (hendpoint i).trans' one_le_two) i2 q).mp
      (Finset.mem_inter.mp hq).1 |>.2
  · intro q hq
    exact (mem_mtAdjacentPrimeBlock_scale_iff (fun i => (hendpoint i).trans' one_le_two) i3 q).mp
      (Finset.mem_inter.mp hq).1 |>.2

def mtSeparatedPairBoxProductScale {u t : ℕ}
    (endpoint : ℕ → ℕ) (delta : ℝ) (recStart : ℕ)
    (i1 i2 : Fin u) (chain : List (Fin t)) (eIndex kIndex : ℕ) : ℝ :=
  (((mtAdjacentBlockLowerScale endpoint i1.1 *
      mtAdjacentBlockLowerScale endpoint i2.1) *
      ∏ j ∈ chain.toFinset, mtGeometricLevel delta recStart j.1) *
      mtUpperAdicScale delta eIndex) * mtUpperAdicScale delta kIndex

def mtSeparatedTripleBoxProductScale {u t : ℕ}
    (endpoint : ℕ → ℕ) (delta : ℝ) (recStart : ℕ)
    (i1 i2 i3 : Fin u) (chain : List (Fin t)) (eIndex kIndex : ℕ) : ℝ :=
  ((((mtAdjacentBlockLowerScale endpoint i1.1 *
      mtAdjacentBlockLowerScale endpoint i2.1) *
      mtAdjacentBlockLowerScale endpoint i3.1) *
      ∏ j ∈ chain.toFinset, mtGeometricLevel delta recStart j.1) *
      mtUpperAdicScale delta eIndex) * mtUpperAdicScale delta kIndex

/-- Pair box with independent outer and recursive schedules fits one common product collar. -/
theorem mtSignedSeparatedPairBox_scaleSupported_commonProductCollar
    {u : ℕ} {endpoint : ℕ → ℕ} {delta : ℝ} (hendpoint : ∀ i, 2 ≤ endpoint i)
    (hband : ∀ i, mtAdjacentBlockUpperScale endpoint i ≤
      (1 + delta) * mtAdjacentBlockLowerScale endpoint i)
    (P : Finset ℕ) (z0 D recStart : ℕ) {recRoot eta : ℝ}
    (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta recStart 0)
    (hroot : mtGeometricLevel delta recStart 0 < recRoot)
    (data : MTFiniteIterationSourceData
      (mtMinimalGeometricDepth delta recStart recRoot hdelta))
    (hblocks : data.block =
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D recStart delta recRoot hdelta hz0 hroot).block)
    (i1 i2 : Fin u)
    {chain : List (Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta))}
    (hchain : chain.Nodup)
    (maxDepth eIndex kIndex : ℕ) (hlength : chain.length ≤ maxDepth)
    (hdilation : (1 + delta) ^ (maxDepth + 4) ≤ 1 + eta) :
    MTRealScaleSupported
      (mtSignedBlockChainAdicBoxAF
        (mtHarmanPairCellCoefficient
          (mtHarmanSourceBlock endpoint P i1)
          (mtHarmanSourceBlock endpoint P i2))
        data.block chain z0 D delta eIndex kIndex)
      (mtSeparatedPairBoxProductScale endpoint delta recStart
        i1 i2 chain eIndex kIndex)
      ((1 + eta) * mtSeparatedPairBoxProductScale endpoint delta recStart
        i1 i2 chain eIndex kIndex) := by
  have hrecBlock : ∀ i,
      MTRealScaleSupported (mtPrimeBlockAF (data.block i))
        (mtGeometricLevel delta recStart i.1)
        (mtGeometricLevel delta recStart i.1 * (1 + delta)) := by
    intro i
    rw [hblocks]
    exact mtMinimalGeometricBlock_scaleSupported
      z0 D recStart hdelta hz0 hroot i
  let Lout := mtAdjacentBlockLowerScale endpoint i1.1 *
    mtAdjacentBlockLowerScale endpoint i2.1
  let Mlong := (Lout * ∏ j ∈ chain.toFinset,
    mtGeometricLevel delta recStart j.1) * mtUpperAdicScale delta eIndex
  let K := mtUpperAdicScale delta kIndex
  let F := mtBlockChainLongAF
    (mtHarmanPairCellCoefficient
      (mtHarmanSourceBlock endpoint P i1)
      (mtHarmanSourceBlock endpoint P i2))
    data.block chain z0 D delta eIndex
  have hLout : 0 ≤ Lout := by
    dsimp [Lout]
    exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hlongRaw : MTRealScaleSupported F Mlong
      (((mtAdjacentBlockUpperScale endpoint i1.1 *
          mtAdjacentBlockUpperScale endpoint i2.1) *
          ∏ j ∈ chain.toFinset,
            (mtGeometricLevel delta recStart j.1 * (1 + delta))) *
          ((1 + delta) * mtUpperAdicScale delta eIndex)) := by
    intro n hn
    simpa only [F, Mlong, Lout] using
      (mtBlockChainLongAF_scaleSupported
        (mtHarmanPairSourceCell_scaleSupported hendpoint P i1 i2)
        hrecBlock (fun i => (mtGeometricLevel_pos hdelta recStart i.1).le)
        hLout hchain z0 D eIndex (mtUpperAdicScale_pos hdelta eIndex).le)
        hn
  have hlong : MTRealScaleSupported F Mlong
      ((1 + delta) ^ (chain.length + 3) * Mlong) := by
    intro n hn
    have hs := hlongRaw (n := n) (by simpa [F] using hn)
    refine ⟨hs.1, by simpa [Mlong, Lout] using hs.2.1, ?_⟩
    calc
      (n : ℝ) ≤
          ((mtAdjacentBlockUpperScale endpoint i1.1 *
            mtAdjacentBlockUpperScale endpoint i2.1) *
            ∏ j ∈ chain.toFinset,
              (mtGeometricLevel delta recStart j.1 * (1 + delta))) *
            ((1 + delta) * mtUpperAdicScale delta eIndex) := hs.2.2
      _ ≤ (1 + delta) ^ (chain.length + 3) * Mlong := by
        have hb : 0 ≤ 1 + delta := by linarith
        have hprod : (∏ j ∈ chain.toFinset,
            (mtGeometricLevel delta recStart j.1 * (1 + delta))) =
            (1 + delta) ^ chain.length *
              ∏ j ∈ chain.toFinset, mtGeometricLevel delta recStart j.1 :=
          prod_mul_constant_chain_toFinset
            (fun j : Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta) =>
              mtGeometricLevel delta recStart j.1) (1 + delta) hchain
        rw [hprod]
        dsimp [Mlong, Lout]
        have hU1 : 0 ≤ mtAdjacentBlockUpperScale endpoint i1.1 := by
          exact Nat.cast_nonneg _
        have hU2 : 0 ≤ mtAdjacentBlockUpperScale endpoint i2.1 := by
          exact Nat.cast_nonneg _
        have hL1 : 0 ≤ mtAdjacentBlockLowerScale endpoint i1.1 := by
          exact Nat.cast_nonneg _
        have hL2 : 0 ≤ mtAdjacentBlockLowerScale endpoint i2.1 := by
          exact Nat.cast_nonneg _
        have hchainScale : 0 ≤ (1 + delta) ^ chain.length *
            ∏ j ∈ chain.toFinset, mtGeometricLevel delta recStart j.1 := by
          exact mul_nonneg (pow_nonneg hb _) (Finset.prod_nonneg fun j _ =>
            (mtGeometricLevel_pos hdelta recStart j.1).le)
        have heScale : 0 ≤ (1 + delta) * mtUpperAdicScale delta eIndex :=
          mul_nonneg hb (mtUpperAdicScale_pos hdelta eIndex).le
        have houter : mtAdjacentBlockUpperScale endpoint i1.1 *
              mtAdjacentBlockUpperScale endpoint i2.1 ≤
            ((1 + delta) * mtAdjacentBlockLowerScale endpoint i1.1) *
              ((1 + delta) * mtAdjacentBlockLowerScale endpoint i2.1) :=
          mul_le_mul (hband i1.1) (hband i2.1) hU2 (mul_nonneg hb hL1)
        calc
          (mtAdjacentBlockUpperScale endpoint i1.1 *
              mtAdjacentBlockUpperScale endpoint i2.1) *
                ((1 + delta) ^ chain.length *
                  ∏ j ∈ chain.toFinset, mtGeometricLevel delta recStart j.1) *
              ((1 + delta) * mtUpperAdicScale delta eIndex) ≤
            (((1 + delta) * mtAdjacentBlockLowerScale endpoint i1.1) *
              ((1 + delta) * mtAdjacentBlockLowerScale endpoint i2.1)) *
                ((1 + delta) ^ chain.length *
                  ∏ j ∈ chain.toFinset, mtGeometricLevel delta recStart j.1) *
              ((1 + delta) * mtUpperAdicScale delta eIndex) := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right houter hchainScale) heScale
          _ = (1 + delta) ^ (chain.length + 3) *
              (((mtAdjacentBlockLowerScale endpoint i1.1 *
                mtAdjacentBlockLowerScale endpoint i2.1) *
                ∏ j ∈ chain.toFinset, mtGeometricLevel delta recStart j.1) *
                mtUpperAdicScale delta eIndex) := by
                rw [show chain.length + 3 = chain.length + 2 + 1 by omega,
                  pow_succ, pow_add]
                ring
  have hmul : MTRealScaleSupported
      (F * mtUpperAdicOneAF delta kIndex)
      (Mlong * K)
      (((1 + delta) ^ (chain.length + 3) * Mlong) * ((1 + delta) * K)) := by
    exact MTRealScaleSupported.mul hlong
      (mtRealIntervalAF_scaleSupported (fun _ => 1) K ((1 + delta) * K))
      (by
        dsimp [Mlong]
        exact mul_nonneg
          (mul_nonneg hLout (Finset.prod_nonneg fun j _ =>
            (mtGeometricLevel_pos hdelta recStart j.1).le))
          (mtUpperAdicScale_pos hdelta eIndex).le)
      (mtUpperAdicScale_pos hdelta kIndex).le
  have hexact : MTRealScaleSupported (F * mtUpperAdicOneAF delta kIndex)
      (Mlong * K) ((1 + delta) ^ (chain.length + 4) * (Mlong * K)) := by
    intro n hn
    have hs := hmul hn
    refine ⟨hs.1, hs.2.1, hs.2.2.trans_eq ?_⟩
    rw [show chain.length + 4 = chain.length + 3 + 1 by omega, pow_succ]
    ring
  have hpower : (1 + delta) ^ (chain.length + 4) ≤ 1 + eta :=
    (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + delta) (by omega)).trans hdilation
  have hboxScale : 0 ≤ Mlong * K := by
    exact mul_nonneg
      (by
        dsimp [Mlong]
        exact mul_nonneg
          (mul_nonneg hLout (Finset.prod_nonneg fun j _ =>
            (mtGeometricLevel_pos hdelta recStart j.1).le))
          (mtUpperAdicScale_pos hdelta eIndex).le)
      (by dsimp [K]; exact (mtUpperAdicScale_pos hdelta kIndex).le)
  have hcommon : MTRealScaleSupported (F * mtUpperAdicOneAF delta kIndex)
      (Mlong * K) ((1 + eta) * (Mlong * K)) := by
    intro n hn
    have hs := hexact hn
    exact ⟨hs.1, hs.2.1, hs.2.2.trans
      (mul_le_mul_of_nonneg_right hpower hboxScale)⟩
  unfold mtSignedBlockChainAdicBoxAF mtBlockChainAdicBoxAF
  unfold mtSeparatedPairBoxProductScale
  dsimp [F, mtBlockChainLongAF, mtBlockChainCoefficientAF, Mlong, Lout, K] at hcommon ⊢
  intro n hn
  exact (MTRealScaleSupported.smul hcommon ((-1 : ℂ) ^ chain.length)) hn

/-- Triple box with independent outer and recursive schedules fits one common product collar. -/
theorem mtSignedSeparatedTripleBox_scaleSupported_commonProductCollar
    {u : ℕ} {endpoint : ℕ → ℕ} {delta : ℝ} (hendpoint : ∀ i, 2 ≤ endpoint i)
    (hband : ∀ i, mtAdjacentBlockUpperScale endpoint i ≤
      (1 + delta) * mtAdjacentBlockLowerScale endpoint i)
    (P : Finset ℕ) (z0 D recStart : ℕ) {recRoot eta : ℝ}
    (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta recStart 0)
    (hroot : mtGeometricLevel delta recStart 0 < recRoot)
    (data : MTFiniteIterationSourceData
      (mtMinimalGeometricDepth delta recStart recRoot hdelta))
    (hblocks : data.block =
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D recStart delta recRoot hdelta hz0 hroot).block)
    (i1 i2 i3 : Fin u)
    {chain : List (Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta))}
    (hchain : chain.Nodup)
    (maxDepth eIndex kIndex : ℕ) (hlength : chain.length ≤ maxDepth)
    (hdilation : (1 + delta) ^ (maxDepth + 5) ≤ 1 + eta) :
    MTRealScaleSupported
      (mtSignedBlockChainAdicBoxAF
        (mtHarmanTripleCellCoefficient
          (mtHarmanSourceBlock endpoint P i1)
          (mtHarmanSourceBlock endpoint P i2)
          (mtHarmanSourceBlock endpoint P i3))
        data.block chain z0 D delta eIndex kIndex)
      (mtSeparatedTripleBoxProductScale endpoint delta recStart
        i1 i2 i3 chain eIndex kIndex)
      ((1 + eta) * mtSeparatedTripleBoxProductScale endpoint delta recStart
        i1 i2 i3 chain eIndex kIndex) := by
  have hrecBlock : ∀ i,
      MTRealScaleSupported (mtPrimeBlockAF (data.block i))
        (mtGeometricLevel delta recStart i.1)
        (mtGeometricLevel delta recStart i.1 * (1 + delta)) := by
    intro i
    rw [hblocks]
    exact mtMinimalGeometricBlock_scaleSupported
      z0 D recStart hdelta hz0 hroot i
  let Lout := (mtAdjacentBlockLowerScale endpoint i1.1 *
    mtAdjacentBlockLowerScale endpoint i2.1) *
    mtAdjacentBlockLowerScale endpoint i3.1
  let Mlong := (Lout * ∏ j ∈ chain.toFinset,
    mtGeometricLevel delta recStart j.1) * mtUpperAdicScale delta eIndex
  let K := mtUpperAdicScale delta kIndex
  let F := mtBlockChainLongAF
    (mtHarmanTripleCellCoefficient
      (mtHarmanSourceBlock endpoint P i1)
      (mtHarmanSourceBlock endpoint P i2)
      (mtHarmanSourceBlock endpoint P i3))
    data.block chain z0 D delta eIndex
  have hLout : 0 ≤ Lout := by
    dsimp [Lout]
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)
  have hlongRaw : MTRealScaleSupported F Mlong
      ((((mtAdjacentBlockUpperScale endpoint i1.1 *
          mtAdjacentBlockUpperScale endpoint i2.1) *
          mtAdjacentBlockUpperScale endpoint i3.1) *
          ∏ j ∈ chain.toFinset,
            (mtGeometricLevel delta recStart j.1 * (1 + delta))) *
          ((1 + delta) * mtUpperAdicScale delta eIndex)) := by
    intro n hn
    simpa only [F, Mlong, Lout] using
      (mtBlockChainLongAF_scaleSupported
        (mtHarmanTripleSourceCell_scaleSupported hendpoint P i1 i2 i3)
        hrecBlock (fun i => (mtGeometricLevel_pos hdelta recStart i.1).le)
        hLout hchain z0 D eIndex (mtUpperAdicScale_pos hdelta eIndex).le)
        hn
  have hlong : MTRealScaleSupported F Mlong
      ((1 + delta) ^ (chain.length + 4) * Mlong) := by
    intro n hn
    have hs := hlongRaw (n := n) (by simpa [F] using hn)
    refine ⟨hs.1, by simpa [Mlong, Lout] using hs.2.1, ?_⟩
    calc
      (n : ℝ) ≤
          (((mtAdjacentBlockUpperScale endpoint i1.1 *
            mtAdjacentBlockUpperScale endpoint i2.1) *
            mtAdjacentBlockUpperScale endpoint i3.1) *
            ∏ j ∈ chain.toFinset,
              (mtGeometricLevel delta recStart j.1 * (1 + delta))) *
            ((1 + delta) * mtUpperAdicScale delta eIndex) := hs.2.2
      _ ≤ (1 + delta) ^ (chain.length + 4) * Mlong := by
        have hb : 0 ≤ 1 + delta := by linarith
        have hprod : (∏ j ∈ chain.toFinset,
            (mtGeometricLevel delta recStart j.1 * (1 + delta))) =
            (1 + delta) ^ chain.length *
              ∏ j ∈ chain.toFinset, mtGeometricLevel delta recStart j.1 :=
          prod_mul_constant_chain_toFinset
            (fun j : Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta) =>
              mtGeometricLevel delta recStart j.1) (1 + delta) hchain
        rw [hprod]
        dsimp [Mlong, Lout]
        have hU2 : 0 ≤ mtAdjacentBlockUpperScale endpoint i2.1 := by
          exact Nat.cast_nonneg _
        have hU3 : 0 ≤ mtAdjacentBlockUpperScale endpoint i3.1 := by
          exact Nat.cast_nonneg _
        have hL1 : 0 ≤ mtAdjacentBlockLowerScale endpoint i1.1 := by
          exact Nat.cast_nonneg _
        have hL2 : 0 ≤ mtAdjacentBlockLowerScale endpoint i2.1 := by
          exact Nat.cast_nonneg _
        have hchainScale : 0 ≤ (1 + delta) ^ chain.length *
            ∏ j ∈ chain.toFinset, mtGeometricLevel delta recStart j.1 := by
          exact mul_nonneg (pow_nonneg hb _) (Finset.prod_nonneg fun j _ =>
            (mtGeometricLevel_pos hdelta recStart j.1).le)
        have heScale : 0 ≤ (1 + delta) * mtUpperAdicScale delta eIndex :=
          mul_nonneg hb (mtUpperAdicScale_pos hdelta eIndex).le
        have houter12 : mtAdjacentBlockUpperScale endpoint i1.1 *
              mtAdjacentBlockUpperScale endpoint i2.1 ≤
            ((1 + delta) * mtAdjacentBlockLowerScale endpoint i1.1) *
              ((1 + delta) * mtAdjacentBlockLowerScale endpoint i2.1) :=
          mul_le_mul (hband i1.1) (hband i2.1) hU2 (mul_nonneg hb hL1)
        have houter : (mtAdjacentBlockUpperScale endpoint i1.1 *
                mtAdjacentBlockUpperScale endpoint i2.1) *
              mtAdjacentBlockUpperScale endpoint i3.1 ≤
            (((1 + delta) * mtAdjacentBlockLowerScale endpoint i1.1) *
                ((1 + delta) * mtAdjacentBlockLowerScale endpoint i2.1)) *
              ((1 + delta) * mtAdjacentBlockLowerScale endpoint i3.1) :=
          mul_le_mul houter12 (hband i3.1) hU3
            (mul_nonneg (mul_nonneg hb hL1) (mul_nonneg hb hL2))
        calc
          ((mtAdjacentBlockUpperScale endpoint i1.1 *
                mtAdjacentBlockUpperScale endpoint i2.1) *
              mtAdjacentBlockUpperScale endpoint i3.1) *
                ((1 + delta) ^ chain.length *
                  ∏ j ∈ chain.toFinset, mtGeometricLevel delta recStart j.1) *
              ((1 + delta) * mtUpperAdicScale delta eIndex) ≤
            (((1 + delta) * mtAdjacentBlockLowerScale endpoint i1.1) *
                ((1 + delta) * mtAdjacentBlockLowerScale endpoint i2.1) *
              ((1 + delta) * mtAdjacentBlockLowerScale endpoint i3.1)) *
                ((1 + delta) ^ chain.length *
                  ∏ j ∈ chain.toFinset, mtGeometricLevel delta recStart j.1) *
              ((1 + delta) * mtUpperAdicScale delta eIndex) := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right houter hchainScale) heScale
          _ = (1 + delta) ^ (chain.length + 4) *
              ((((mtAdjacentBlockLowerScale endpoint i1.1 *
                mtAdjacentBlockLowerScale endpoint i2.1) *
                mtAdjacentBlockLowerScale endpoint i3.1) *
                ∏ j ∈ chain.toFinset, mtGeometricLevel delta recStart j.1) *
                mtUpperAdicScale delta eIndex) := by
                rw [show chain.length + 4 = chain.length + 3 + 1 by omega,
                  pow_succ, pow_add]
                ring
  have hmul : MTRealScaleSupported
      (F * mtUpperAdicOneAF delta kIndex)
      (Mlong * K)
      (((1 + delta) ^ (chain.length + 4) * Mlong) * ((1 + delta) * K)) := by
    exact MTRealScaleSupported.mul hlong
      (mtRealIntervalAF_scaleSupported (fun _ => 1) K ((1 + delta) * K))
      (by
        dsimp [Mlong]
        exact mul_nonneg
          (mul_nonneg hLout (Finset.prod_nonneg fun j _ =>
            (mtGeometricLevel_pos hdelta recStart j.1).le))
          (mtUpperAdicScale_pos hdelta eIndex).le)
      (mtUpperAdicScale_pos hdelta kIndex).le
  have hexact : MTRealScaleSupported (F * mtUpperAdicOneAF delta kIndex)
      (Mlong * K) ((1 + delta) ^ (chain.length + 5) * (Mlong * K)) := by
    intro n hn
    have hs := hmul hn
    refine ⟨hs.1, hs.2.1, hs.2.2.trans_eq ?_⟩
    rw [show chain.length + 5 = chain.length + 4 + 1 by omega, pow_succ]
    ring
  have hpower : (1 + delta) ^ (chain.length + 5) ≤ 1 + eta :=
    (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + delta) (by omega)).trans hdilation
  have hboxScale : 0 ≤ Mlong * K := by
    exact mul_nonneg
      (by
        dsimp [Mlong]
        exact mul_nonneg
          (mul_nonneg hLout (Finset.prod_nonneg fun j _ =>
            (mtGeometricLevel_pos hdelta recStart j.1).le))
          (mtUpperAdicScale_pos hdelta eIndex).le)
      (by dsimp [K]; exact (mtUpperAdicScale_pos hdelta kIndex).le)
  have hcommon : MTRealScaleSupported (F * mtUpperAdicOneAF delta kIndex)
      (Mlong * K) ((1 + eta) * (Mlong * K)) := by
    intro n hn
    have hs := hexact hn
    exact ⟨hs.1, hs.2.1, hs.2.2.trans
      (mul_le_mul_of_nonneg_right hpower hboxScale)⟩
  unfold mtSignedBlockChainAdicBoxAF mtBlockChainAdicBoxAF
  unfold mtSeparatedTripleBoxProductScale
  dsimp [F, mtBlockChainLongAF, mtBlockChainCoefficientAF, Mlong, Lout, K] at hcommon ⊢
  intro n hn
  exact (MTRealScaleSupported.smul hcommon ((-1 : ℂ) ^ chain.length)) hn

end

end RHTower.Sieve
