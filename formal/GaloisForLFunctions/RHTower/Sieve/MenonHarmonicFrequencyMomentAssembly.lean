import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicFrequencyAssembly

/-!
# Moment substitution in Menon's harmonic some-large bound

The reciprocal Halász--Montgomery block cost depends monotonically on the frequency-set measure.
This module substitutes the adapted prime-power moment bound for the literal some-large measure,
producing a completely explicit finite sum with no frequency-set quantity left in it.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- Exact harmonic Ramaré block cost with the Gallagher-set measure exposed as a scalar. -/
def menonHarmonicBlockCostVolume
    (P : Finset ℕ) (A₀ B₀ : ℕ) (Q eta W V volE : ℝ) (j : ℕ) : ℝ :=
  2 * V ^ 2 * ((2 * Real.pi)⁻¹ *
      (hmMassRecip ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊
        (2 * Real.pi * W) (2 * Real.pi * volE) *
          ((1 / (⌈(A₀ : ℝ) /
            ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊ : ℝ)) ^ 2 *
            ((harmonicGeomCofactorBlock A₀ B₀ Q eta j).card : ℝ))))
    + 2 * harmonicPrimeMass (geomBlock P Q (1 + eta) j) ^ 2 *
        harmonicCofactorSupportError A₀ B₀ Q eta W j

theorem menonHarmonicAllSmallBlockCost_eq_volume
    (P : Finset ℕ) (A₀ B₀ : ℕ) (Q eta W V : ℝ) (E : Set ℝ) (j : ℕ) :
    menonHarmonicAllSmallBlockCost P A₀ B₀ Q eta W V E j =
      menonHarmonicBlockCostVolume P A₀ B₀ Q eta W V (volume.real E) j := rfl

/-- The reciprocal HM mass is monotone in the measure parameter. -/
theorem hmMassRecip_mono_volume
    (N : ℕ) {T u v : ℝ} (hT : 1 ≤ T) (huv : u ≤ v) :
    hmMassRecip N T u ≤ hmMassRecip N T v := by
  rw [hmMassRecip, hmMassRecip]
  have hfar : 0 ≤ plainKernelFarConst N T := plainKernelFarConst_nonneg N hT
  nlinarith [mul_le_mul_of_nonneg_left huv hfar]

/-- The exact harmonic block cost is monotone in the exposed set-measure budget. -/
theorem menonHarmonicBlockCostVolume_mono
    (P : Finset ℕ) (A₀ B₀ : ℕ) (Q eta W V : ℝ) {u v : ℝ} (j : ℕ)
    (hW : 1 ≤ W) (huv : u ≤ v) :
    menonHarmonicBlockCostVolume P A₀ B₀ Q eta W V u j ≤
      menonHarmonicBlockCostVolume P A₀ B₀ Q eta W V v j := by
  have hT : 1 ≤ 2 * Real.pi * W := by
    nlinarith [Real.pi_gt_three]
  have hvol : 2 * Real.pi * u ≤ 2 * Real.pi * v :=
    mul_le_mul_of_nonneg_left huv (by positivity)
  unfold menonHarmonicBlockCostVolume
  gcongr
  exact hmMassRecip_mono_volume _ hT hvol

/-- Explicit adapted-moment majorant for the whole harmonic some-large set. -/
def menonHarmonicSomeLargeMomentBudget
    (k N : ℕ) (Q eta W : ℝ) (L : ℕ) (V : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range L,
    menonHarmonicBlockMomentCost k N Q eta W j / (V j) ^ (2 * k)

/-- The complete some-large Ramaré integral with its set measure replaced by the adapted moment
budget. -/
theorem setIntegral_normSq_harmonicRamareBilinear_le_someLarge_moments
    (k N : ℕ) (hk : 1 ≤ k)
    {P : Finset ℕ} {A₀ B₀ L : ℕ} {Q eta W : ℝ}
    (hA₀ : 1 ≤ A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hL : 1 ≤ L)
    (hP : P ⊆ Finset.Icc 1 N) (hPprime : ∀ p ∈ P, p.Prime)
    (hPrange : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (V : ℕ → ℝ) (hV : ∀ j ∈ Finset.range L, 0 < V j)
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : ∀ j ∈ Finset.range L,
      1 ≤ ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊) :
    (∫ w in menonHarmonicSomeBlockLarge P Q eta L V W,
      ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ 2)
      ≤ (L : ℝ) * ∑ j ∈ Finset.range L,
          menonHarmonicBlockCostVolume P A₀ B₀ Q eta W
            (harmonicPrimeMass (geomBlock P Q (1 + eta) j))
            (menonHarmonicSomeLargeMomentBudget k N Q eta W L V) j := by
  have hbase := setIntegral_normSq_harmonicRamareBilinear_le_someLarge
    hA₀ hQ heta hW hL hPprime hPrange V hleft hright
  have hvol : volume.real (menonHarmonicSomeBlockLarge P Q eta L V W) ≤
      menonHarmonicSomeLargeMomentBudget k N Q eta W L V := by
    exact volume_menonHarmonicSomeBlockLarge_le_moments
      k N hk hP hPprime hQ heta (le_trans (by norm_num) hW) V hV
  refine hbase.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg L))
  refine Finset.sum_le_sum fun j _ => ?_
  rw [menonHarmonicAllSmallBlockCost_eq_volume]
  exact menonHarmonicBlockCostVolume_mono _ _ _ _ _ _ _ j hW hvol

/-- Explicit block-local adapted-moment majorant for the whole harmonic some-large set. -/
def menonHarmonicSomeLargeLocalMomentBudget
    (k : ℕ) (Q eta W : ℝ) (L : ℕ) (V : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range L,
    menonHarmonicLocalBlockMomentCost k Q eta W j / (V j) ^ (2 * k)

/-- The complete some-large Ramaré integral with each adapted moment truncated at its block's
own literal upper endpoint. -/
theorem setIntegral_normSq_harmonicRamareBilinear_le_someLarge_local_moments
    (k : ℕ) (hk : 1 ≤ k)
    {P : Finset ℕ} {A₀ B₀ L : ℕ} {Q eta W : ℝ}
    (hA₀ : 1 ≤ A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hL : 1 ≤ L)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPrange : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (V : ℕ → ℝ) (hV : ∀ j ∈ Finset.range L, 0 < V j)
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : ∀ j ∈ Finset.range L,
      1 ≤ ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊) :
    (∫ w in menonHarmonicSomeBlockLarge P Q eta L V W,
      ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ 2)
      ≤ (L : ℝ) * ∑ j ∈ Finset.range L,
          menonHarmonicBlockCostVolume P A₀ B₀ Q eta W
            (harmonicPrimeMass (geomBlock P Q (1 + eta) j))
            (menonHarmonicSomeLargeLocalMomentBudget k Q eta W L V) j := by
  have hbase := setIntegral_normSq_harmonicRamareBilinear_le_someLarge
    hA₀ hQ heta hW hL hPprime hPrange V hleft hright
  have hvol : volume.real (menonHarmonicSomeBlockLarge P Q eta L V W) ≤
      menonHarmonicSomeLargeLocalMomentBudget k Q eta W L V := by
    exact volume_menonHarmonicSomeBlockLarge_le_local_moments
      k hk hPprime hQ heta (le_trans (by norm_num) hW) V hV
  refine hbase.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg L))
  refine Finset.sum_le_sum fun j _ => ?_
  rw [menonHarmonicAllSmallBlockCost_eq_volume]
  exact menonHarmonicBlockCostVolume_mono _ _ _ _ _ _ _ j hW hvol

/-- The all-small set occupies at most the length `2W` of its ambient frequency interval. -/
theorem volume_real_menonHarmonicAllBlocksSmall_le_two_mul
    (P : Finset ℕ) (Q eta : ℝ) (L : ℕ) (V : ℕ → ℝ) {W : ℝ} (hW : 0 ≤ W) :
    volume.real (menonHarmonicAllBlocksSmall P Q eta L V W) ≤ 2 * W := by
  have hmono : volume (menonHarmonicAllBlocksSmall P Q eta L V W) ≤
      volume (Set.Icc (-W) W) :=
    measure_mono (menonHarmonicAllBlocksSmall_subset P Q eta L V W)
  have htop : volume (Set.Icc (-W) W) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono htop hmono
  rw [MeasureTheory.measureReal_def]
  rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)] at hreal
  linarith

/-- Menon's literal harmonic shell with every frequency-set measure replaced by an explicit
scalar: ambient length on the all-small side and adapted prime moments on the some-large side. -/
theorem integral_Icc_normSq_menonFinalRangeShell_le_explicitMoments
    (k : ℕ) (hk : 1 ≤ k)
    {x Q eta : ℝ} {L : ℕ} (hx : 1 ≤ x) (hQ : 0 < Q) (heta : 0 ≤ eta) (hL : 1 ≤ L)
    (hPrange : ∀ p ∈ menonFinalRangePrimes x,
      Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (V : ℕ → ℝ) (hV : ∀ j ∈ Finset.range L, 0 < V j)
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(⌈x⌉₊ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : ∀ j ∈ Finset.range L,
      1 ≤ ⌊(menonFinalRangeTopNat x : ℝ) / (Q * (1 + eta) ^ j)⌋₊) :
    (∫ w in Set.Icc (-x) x,
      ‖logPoly harmonicMoebiusC (menonFinalRangeShell x) w‖ ^ 2)
      ≤ 2 * ((L : ℝ) * ∑ j ∈ Finset.range L,
          menonHarmonicBlockCostVolume (menonFinalRangePrimes x) ⌈x⌉₊
            (menonFinalRangeTopNat x) Q eta x (V j) (2 * x) j
        + (L : ℝ) * ∑ j ∈ Finset.range L,
          menonHarmonicBlockCostVolume (menonFinalRangePrimes x) ⌈x⌉₊
            (menonFinalRangeTopNat x) Q eta x
            (harmonicPrimeMass
              (geomBlock (menonFinalRangePrimes x) Q (1 + eta) j))
            (menonHarmonicSomeLargeMomentBudget k (menonFinalRangeTopNat x)
              Q eta x L V) j)
        + 2 * menonFinalRangeHarmonicRoughEnergy x := by
  have hbase := integral_Icc_normSq_menonFinalRangeShell_le_frequencyPartition
    hx hQ heta hL hPrange V hleft hright
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hsmallVol :
      volume.real (menonHarmonicAllBlocksSmall
        (menonFinalRangePrimes x) Q eta L V x) ≤ 2 * x :=
    volume_real_menonHarmonicAllBlocksSmall_le_two_mul
      (menonFinalRangePrimes x) Q eta L V hx0
  have hP : menonFinalRangePrimes x ⊆
      Finset.Icc 1 (menonFinalRangeTopNat x) := by
    intro p hp
    have hmem := mem_primesRange.1 hp
    exact Finset.mem_Icc.2 ⟨hmem.1.one_le, hmem.2.2⟩
  have hlargeVol :
      volume.real (menonHarmonicSomeBlockLarge
        (menonFinalRangePrimes x) Q eta L V x) ≤
        menonHarmonicSomeLargeMomentBudget k (menonFinalRangeTopNat x)
          Q eta x L V := by
    exact volume_menonHarmonicSomeBlockLarge_le_moments
      k (menonFinalRangeTopNat x) hk hP
      (fun p hp => menonFinalRangePrimes_prime x hp) hQ heta hx0 V hV
  have hsmallCost :
      (∑ j ∈ Finset.range L,
          menonHarmonicAllSmallBlockCost (menonFinalRangePrimes x) ⌈x⌉₊
            (menonFinalRangeTopNat x) Q eta x (V j)
            (menonHarmonicAllBlocksSmall (menonFinalRangePrimes x) Q eta L V x) j) ≤
        ∑ j ∈ Finset.range L,
          menonHarmonicBlockCostVolume (menonFinalRangePrimes x) ⌈x⌉₊
            (menonFinalRangeTopNat x) Q eta x (V j) (2 * x) j := by
    refine Finset.sum_le_sum fun j _ => ?_
    rw [menonHarmonicAllSmallBlockCost_eq_volume]
    exact menonHarmonicBlockCostVolume_mono _ _ _ _ _ _ _ j hx hsmallVol
  have hlargeCost :
      (∑ j ∈ Finset.range L,
          menonHarmonicAllSmallBlockCost (menonFinalRangePrimes x) ⌈x⌉₊
            (menonFinalRangeTopNat x) Q eta x
            (harmonicPrimeMass
              (geomBlock (menonFinalRangePrimes x) Q (1 + eta) j))
            (menonHarmonicSomeBlockLarge (menonFinalRangePrimes x) Q eta L V x) j) ≤
        ∑ j ∈ Finset.range L,
          menonHarmonicBlockCostVolume (menonFinalRangePrimes x) ⌈x⌉₊
            (menonFinalRangeTopNat x) Q eta x
            (harmonicPrimeMass
              (geomBlock (menonFinalRangePrimes x) Q (1 + eta) j))
            (menonHarmonicSomeLargeMomentBudget k (menonFinalRangeTopNat x)
              Q eta x L V) j := by
    refine Finset.sum_le_sum fun j _ => ?_
    rw [menonHarmonicAllSmallBlockCost_eq_volume]
    exact menonHarmonicBlockCostVolume_mono _ _ _ _ _ _ _ j hx hlargeVol
  have hparts := add_le_add
    (mul_le_mul_of_nonneg_left hsmallCost (Nat.cast_nonneg L))
    (mul_le_mul_of_nonneg_left hlargeCost (Nat.cast_nonneg L))
  have htwoparts := mul_le_mul_of_nonneg_left hparts
    (show (0 : ℝ) ≤ 2 by norm_num)
  exact hbase.trans (add_le_add htwoparts le_rfl)

/-- Menon's literal harmonic shell with the some-large measure replaced by block-local adapted
moments, so no geometric block is padded to the global final-range endpoint. -/
theorem integral_Icc_normSq_menonFinalRangeShell_le_explicitLocalMoments
    (k : ℕ) (hk : 1 ≤ k)
    {x Q eta : ℝ} {L : ℕ} (hx : 1 ≤ x) (hQ : 0 < Q) (heta : 0 ≤ eta) (hL : 1 ≤ L)
    (hPrange : ∀ p ∈ menonFinalRangePrimes x,
      Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (V : ℕ → ℝ) (hV : ∀ j ∈ Finset.range L, 0 < V j)
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(⌈x⌉₊ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : ∀ j ∈ Finset.range L,
      1 ≤ ⌊(menonFinalRangeTopNat x : ℝ) / (Q * (1 + eta) ^ j)⌋₊) :
    (∫ w in Set.Icc (-x) x,
      ‖logPoly harmonicMoebiusC (menonFinalRangeShell x) w‖ ^ 2)
      ≤ 2 * ((L : ℝ) * ∑ j ∈ Finset.range L,
          menonHarmonicBlockCostVolume (menonFinalRangePrimes x) ⌈x⌉₊
            (menonFinalRangeTopNat x) Q eta x (V j) (2 * x) j
        + (L : ℝ) * ∑ j ∈ Finset.range L,
          menonHarmonicBlockCostVolume (menonFinalRangePrimes x) ⌈x⌉₊
            (menonFinalRangeTopNat x) Q eta x
            (harmonicPrimeMass
              (geomBlock (menonFinalRangePrimes x) Q (1 + eta) j))
            (menonHarmonicSomeLargeLocalMomentBudget k Q eta x L V) j)
        + 2 * menonFinalRangeHarmonicRoughEnergy x := by
  have hbase := integral_Icc_normSq_menonFinalRangeShell_le_frequencyPartition
    hx hQ heta hL hPrange V hleft hright
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hsmallVol :
      volume.real (menonHarmonicAllBlocksSmall
        (menonFinalRangePrimes x) Q eta L V x) ≤ 2 * x :=
    volume_real_menonHarmonicAllBlocksSmall_le_two_mul
      (menonFinalRangePrimes x) Q eta L V hx0
  have hlargeVol :
      volume.real (menonHarmonicSomeBlockLarge
        (menonFinalRangePrimes x) Q eta L V x) ≤
        menonHarmonicSomeLargeLocalMomentBudget k Q eta x L V := by
    exact volume_menonHarmonicSomeBlockLarge_le_local_moments
      k hk (fun p hp => menonFinalRangePrimes_prime x hp) hQ heta hx0 V hV
  have hsmallCost :
      (∑ j ∈ Finset.range L,
          menonHarmonicAllSmallBlockCost (menonFinalRangePrimes x) ⌈x⌉₊
            (menonFinalRangeTopNat x) Q eta x (V j)
            (menonHarmonicAllBlocksSmall (menonFinalRangePrimes x) Q eta L V x) j) ≤
        ∑ j ∈ Finset.range L,
          menonHarmonicBlockCostVolume (menonFinalRangePrimes x) ⌈x⌉₊
            (menonFinalRangeTopNat x) Q eta x (V j) (2 * x) j := by
    refine Finset.sum_le_sum fun j _ => ?_
    rw [menonHarmonicAllSmallBlockCost_eq_volume]
    exact menonHarmonicBlockCostVolume_mono _ _ _ _ _ _ _ j hx hsmallVol
  have hlargeCost :
      (∑ j ∈ Finset.range L,
          menonHarmonicAllSmallBlockCost (menonFinalRangePrimes x) ⌈x⌉₊
            (menonFinalRangeTopNat x) Q eta x
            (harmonicPrimeMass
              (geomBlock (menonFinalRangePrimes x) Q (1 + eta) j))
            (menonHarmonicSomeBlockLarge (menonFinalRangePrimes x) Q eta L V x) j) ≤
        ∑ j ∈ Finset.range L,
          menonHarmonicBlockCostVolume (menonFinalRangePrimes x) ⌈x⌉₊
            (menonFinalRangeTopNat x) Q eta x
            (harmonicPrimeMass
              (geomBlock (menonFinalRangePrimes x) Q (1 + eta) j))
            (menonHarmonicSomeLargeLocalMomentBudget k Q eta x L V) j := by
    refine Finset.sum_le_sum fun j _ => ?_
    rw [menonHarmonicAllSmallBlockCost_eq_volume]
    exact menonHarmonicBlockCostVolume_mono _ _ _ _ _ _ _ j hx hlargeVol
  have hparts := add_le_add
    (mul_le_mul_of_nonneg_left hsmallCost (Nat.cast_nonneg L))
    (mul_le_mul_of_nonneg_left hlargeCost (Nat.cast_nonneg L))
  have htwoparts := mul_le_mul_of_nonneg_left hparts
    (show (0 : ℝ) ≤ 2 by norm_num)
  exact hbase.trans (add_le_add htwoparts le_rfl)

end

end RHTower.Sieve
