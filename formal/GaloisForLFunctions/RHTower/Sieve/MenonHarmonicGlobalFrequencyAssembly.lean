import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicLadderError
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicFrequencyMomentAssembly

/-!
# Menon's harmonic frequency assembly with one global support defect

The frequency partition is applied to the genuine prime/cofactor product at each ladder step.
The moving-support defect has already been formed globally, so it is paid once outside both the
ladder Cauchy--Schwarz and the all-small/some-large partition.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- Reciprocal Halász--Montgomery cost of one genuine harmonic block product, with the measure of
the frequency set exposed as a scalar. -/
def menonHarmonicProductCostVolume
    (_P : Finset ℕ) (A₀ B₀ : ℕ) (Q eta W V volE : ℝ) (j : ℕ) : ℝ :=
  V ^ 2 * ((2 * Real.pi)⁻¹ *
    (hmMassRecip ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊
      (2 * Real.pi * W) (2 * Real.pi * volE) *
        ((1 / (⌈(A₀ : ℝ) /
          ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊ : ℝ)) ^ 2 *
          ((geomCofactorBlockAt A₀ B₀ Q eta j).card : ℝ))))

/-- The product cost is monotone in the exposed frequency-set measure. -/
theorem menonHarmonicProductCostVolume_mono
    (P : Finset ℕ) (A₀ B₀ : ℕ) (Q eta W V : ℝ) {u v : ℝ} (j : ℕ)
    (hW : 1 ≤ W) (huv : u ≤ v) :
    menonHarmonicProductCostVolume P A₀ B₀ Q eta W V u j ≤
      menonHarmonicProductCostVolume P A₀ B₀ Q eta W V v j := by
  have hT : 1 ≤ 2 * Real.pi * W := by
    nlinarith [Real.pi_gt_three]
  have hvol : 2 * Real.pi * u ≤ 2 * Real.pi * v :=
    mul_le_mul_of_nonneg_left huv (by positivity)
  unfold menonHarmonicProductCostVolume
  gcongr
  exact hmMassRecip_mono_volume _ hT hvol

/-- One genuine harmonic block product, from a prime supremum and reciprocal
Halász--Montgomery on the common cofactor block. -/
theorem setIntegral_normSq_harmonicProduct_geom_le_HM
    {P : Finset ℕ} {A₀ B₀ : ℕ} {Q eta W V : ℝ}
    (hW : 1 ≤ W) (j : ℕ)
    (hleft : 1 ≤ ⌈(A₀ : ℝ) /
      ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : 1 ≤ ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (hprime : ∀ w ∈ E,
      ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w‖ ≤ V) :
    (∫ w in E,
      ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w *
        logPoly (harmonicRamareCofactorCoeff P)
          (geomCofactorBlockAt A₀ B₀ Q eta j) w‖ ^ 2) ≤
      menonHarmonicProductCostVolume P A₀ B₀ Q eta W V (volume.real E) j := by
  let D : Finset ℕ := geomCofactorBlockAt A₀ B₀ Q eta j
  let L₀ : ℕ := ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊
  let N : ℕ := ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊
  have hD : D ⊆ Finset.Icc L₀ N := by
    intro n hn
    simpa [D, L₀, N, geomCofactorBlockAt] using hn
  have hcof := setIntegral_normSq_harmonicRamareCofactor_le_HM_recip
    P D (L := L₀) (N := N) hleft hright hD hEm hW hEs
  have hprod := setIntegral_normSq_harmonicBlockProduct_le_supMeanSquare
    (harmonicRamareCofactorCoeff P) (geomBlock P Q (1 + eta) j) D
      hEm hEs hprime hcof
  dsimp only [D, L₀, N] at hprod
  simpa [menonHarmonicProductCostVolume] using hprod

/-- Full harmonic Ramaré bilinear energy.  The all-small and some-large estimates are applied to
each genuine product; the global moving-support error appears exactly once. -/
theorem integral_Icc_normSq_harmonicRamareBilinear_le_global_localMoments
    (k : ℕ) (hk : 1 ≤ k)
    {P : Finset ℕ} {A₀ B₀ L : ℕ} {Q eta W : ℝ}
    (hA : 0 < A₀) (hQ : 1 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hL : 1 ≤ L)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPrange : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (V : ℕ → ℝ) (hV : ∀ j ∈ Finset.range L, 0 < V j)
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : ∀ j ∈ Finset.range L,
      1 ≤ ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊) :
    (∫ w in Set.Icc (-W) W,
      ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ 2) ≤
      2 * (L : ℝ) * ∑ j ∈ Finset.range L,
        (menonHarmonicProductCostVolume P A₀ B₀ Q eta W (V j) (2 * W) j +
          menonHarmonicProductCostVolume P A₀ B₀ Q eta W
            (harmonicPrimeMass (geomBlock P Q (1 + eta) j))
            (menonHarmonicSomeLargeLocalMomentBudget k Q eta W L V) j) +
      2 * menonHarmonicLadderErrorBudget A₀ B₀ Q eta W L := by
  classical
  let Es : Set ℝ := menonHarmonicAllBlocksSmall P Q eta L V W
  let El : Set ℝ := menonHarmonicSomeBlockLarge P Q eta L V W
  have hEsm : MeasurableSet Es :=
    measurableSet_menonHarmonicAllBlocksSmall P Q eta L V W
  have hElm : MeasurableSet El :=
    measurableSet_menonHarmonicSomeBlockLarge P Q eta L V W
  have hEss : Es ⊆ Set.Icc (-W) W :=
    menonHarmonicAllBlocksSmall_subset P Q eta L V W
  have hEls : El ⊆ Set.Icc (-W) W := fun _ hw => hw.1
  have hsmallVol : volume.real Es ≤ 2 * W := by
    simpa only [Es] using volume_real_menonHarmonicAllBlocksSmall_le_two_mul
      P Q eta L V (le_trans (by norm_num) hW)
  have hlargeVol : volume.real El ≤
      menonHarmonicSomeLargeLocalMomentBudget k Q eta W L V := by
    simpa only [El, menonHarmonicSomeLargeLocalMomentBudget] using
      volume_menonHarmonicSomeBlockLarge_le_local_moments
      k hk hPprime (lt_trans zero_lt_one hQ) heta (le_trans (by norm_num) hW) V hV
  have hbase := setIntegral_normSq_harmonicRamareBilinear_le_ladder_closed
    (P := P) (A₀ := A₀) (B₀ := B₀)
    hA hQ heta hW hL hPprime hPrange measurableSet_Icc (fun _ hw => hw)
  refine hbase.trans (add_le_add ?_ le_rfl)
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_)
    (mul_nonneg (by norm_num) (Nat.cast_nonneg L))
  let f : ℝ → ℝ := fun w =>
    ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w *
      logPoly (harmonicRamareCofactorCoeff P)
        (geomCofactorBlockAt A₀ B₀ Q eta j) w‖ ^ 2
  have hf : Continuous f := by
    dsimp only [f]
    exact (((continuous_harmonicPrimeBlockPoly _).mul (continuous_logPoly _ _)).norm).pow 2
  have hsplit := setIntegral_menonHarmonic_frequencyPartition
    P Q eta L V W f hf.integrableOn_Icc
  have hsmall := setIntegral_normSq_harmonicProduct_geom_le_HM
    (P := P) (A₀ := A₀) (B₀ := B₀) (Q := Q) (eta := eta) (W := W)
    (V := V j) hW j (hleft j hj) (hright j hj)
    hEsm hEss (fun w hw => norm_harmonicPrimeBlockPoly_le_of_mem_allBlocksSmall hj hw)
  have hblockPrime : ∀ p ∈ geomBlock P Q (1 + eta) j, p.Prime := by
    intro p hp
    exact hPprime p (geomBlock_subset P Q (1 + eta) j hp)
  have hlarge := setIntegral_normSq_harmonicProduct_geom_le_HM
    (P := P) (A₀ := A₀) (B₀ := B₀) (Q := Q) (eta := eta) (W := W)
    (V := harmonicPrimeMass (geomBlock P Q (1 + eta) j))
    hW j (hleft j hj) (hright j hj)
    hElm hEls (fun w _ => norm_harmonicPrimeBlockPoly_le_mass hblockPrime w)
  have hsmall' := (menonHarmonicProductCostVolume_mono
    P A₀ B₀ Q eta W (V j) j hW hsmallVol).trans'
      (by simpa only [Es] using hsmall)
  have hlarge' := (menonHarmonicProductCostVolume_mono
    P A₀ B₀ Q eta W
      (harmonicPrimeMass (geomBlock P Q (1 + eta) j)) j hW hlargeVol).trans'
      (by simpa only [El] using hlarge)
  calc
    (∫ w in Set.Icc (-W) W,
      ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w *
        logPoly (harmonicRamareCofactorCoeff P)
          (geomCofactorBlockAt A₀ B₀ Q eta j) w‖ ^ 2) =
        (∫ w in Es, f w) + ∫ w in El, f w := by
          simpa only [f, Es, El] using hsplit
    _ ≤ _ := add_le_add hsmall' hlarge'

/-- Menon's literal harmonic shell with global support error and block-local adapted moments. -/
theorem integral_Icc_normSq_menonFinalRangeShell_le_global_localMoments
    (k : ℕ) (hk : 1 ≤ k)
    {x Q eta : ℝ} {L : ℕ} (hx : 1 ≤ x) (hQ : 1 < Q) (heta : 0 ≤ eta) (hL : 1 ≤ L)
    (hPrange : ∀ p ∈ menonFinalRangePrimes x,
      Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (V : ℕ → ℝ) (hV : ∀ j ∈ Finset.range L, 0 < V j)
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(⌈x⌉₊ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : ∀ j ∈ Finset.range L,
      1 ≤ ⌊(menonFinalRangeTopNat x : ℝ) / (Q * (1 + eta) ^ j)⌋₊) :
    (∫ w in Set.Icc (-x) x,
      ‖logPoly harmonicMoebiusC (menonFinalRangeShell x) w‖ ^ 2) ≤
      2 * (2 * (L : ℝ) * ∑ j ∈ Finset.range L,
        (menonHarmonicProductCostVolume (menonFinalRangePrimes x) ⌈x⌉₊
            (menonFinalRangeTopNat x) Q eta x (V j) (2 * x) j +
          menonHarmonicProductCostVolume (menonFinalRangePrimes x) ⌈x⌉₊
            (menonFinalRangeTopNat x) Q eta x
            (harmonicPrimeMass
              (geomBlock (menonFinalRangePrimes x) Q (1 + eta) j))
            (menonHarmonicSomeLargeLocalMomentBudget k Q eta x L V) j) +
        2 * menonHarmonicLadderErrorBudget ⌈x⌉₊
          (menonFinalRangeTopNat x) Q eta x L) +
      2 * menonFinalRangeHarmonicRoughEnergy x := by
  have hA : 0 < ⌈x⌉₊ := by
    have : 1 ≤ ⌈x⌉₊ := by exact_mod_cast hx.trans (Nat.le_ceil x)
    omega
  have hbil := integral_Icc_normSq_harmonicRamareBilinear_le_global_localMoments
    k hk (P := menonFinalRangePrimes x) (A₀ := ⌈x⌉₊)
    (B₀ := menonFinalRangeTopNat x) (L := L) (Q := Q) (eta := eta) (W := x)
    hA hQ heta hx hL (fun p hp => menonFinalRangePrimes_prime x hp)
    hPrange V hV hleft hright
  have hsplit := setIntegral_normSq_add_le
    (F := fun w => harmonicRamareBilinear (menonFinalRangePrimes x)
      (menonFinalRangeShell x) w)
    (G := fun w => logPoly harmonicMoebiusC (menonFinalRangeHarmonicRoughSet x) w)
    (E := Set.Icc (-x) x) (W := x)
    (by
      refine continuous_finsetSum (menonFinalRangePrimes x) fun p _ => ?_
      exact ((continuous_moebiusPhase p).div_const _).mul (continuous_logPoly _ _))
    (continuous_logPoly _ _) measurableSet_Icc (fun _ hw => hw)
  rw [menonFinalRangeHarmonicRoughEnergy]
  calc
    (∫ w in Set.Icc (-x) x,
      ‖logPoly harmonicMoebiusC (menonFinalRangeShell x) w‖ ^ 2) ≤
        2 * (∫ w in Set.Icc (-x) x,
          ‖harmonicRamareBilinear (menonFinalRangePrimes x)
            (menonFinalRangeShell x) w‖ ^ 2) +
        2 * ∫ w in Set.Icc (-x) x,
          ‖logPoly harmonicMoebiusC (menonFinalRangeHarmonicRoughSet x) w‖ ^ 2 := by
            simpa only [logPoly_harmonicMoebius_eq_menonFinalRange_ramare_add_rough,
              menonFinalRangeHarmonicRoughSet] using hsplit
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hbil (by norm_num)) le_rfl

end

end RHTower.Sieve
