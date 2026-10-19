import GaloisForLFunctions.BiScaleUncertainty.PrimeBlockLevelSetAndRamareHalaszEnergy
import GaloisForLFunctions.RHTower.Sieve.RamareLadderErrorSharp
import GaloisForLFunctions.RHTower.Sieve.RamareLadderHMRecip
import GaloisForLFunctions.RHTower.Sieve.CofactorLowFreqBound

/-!
# The Ramaré Geometric Ladder with Discharged Halász–Montgomery–Huxley Steps and Multiplicity-Free Error

This module connects `PrimeBlockLevelSetAndRamareHalaszEnergy` (`BiScaleUncertainty`) to three
previously isolated components of `RHTower/Sieve/`:

1. **Exact Initial-Interval Identification of `geomCofactorBlock` (`geomCofactorBlock_eq_Icc_one`):**
   Combines `TwoSidedCofactorBlock.geomCofactorBlockAt_one` with
   `CofactorLowFreqBound.geomCofactorBlockAt_one_eq` to prove that for `1 ≤ Q` and `0 ≤ η`,
   `geomCofactorBlock M Q η j = Finset.Icc 1 ⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊`.
   This bridges the geometric cofactor blocks of `RamareBlockSplit` to the initial-segment cofactor
   polynomials `logPoly a (Finset.Icc 1 M_j)` required by `BlockProductHalaszExplicit`.
2. **Discharged Halász–Montgomery–Huxley + Kuzmin–Landau Bound on Each Geometric Ladder Step
   (`integral_normSq_ramareLadderStep_le_halaszMontgomery_huxley_const`,
   `integral_normSq_ramareLadderStep_le_halaszMontgomery_huxley_kuzminLandau`):**
   Applies `integral_normSq_blockProduct_le_halaszMontgomery_huxley_const` to the `j`-th geometric
   ladder step `primeBlockPoly (geomBlock P Q (1 + η) j) w * logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w`,
   and discharges the remaining low-value cofactor mean square using the Kuzmin–Landau reciprocal
   kernel bound `RamareLadderHMRecip.setIntegral_normSq_cofactorBlock_le_HM_recip`.
3. **Multiplicity-Free Global Ramaré Ladder Assembly
   (`integral_normSq_ramareBilinear_le_sharp_ladder_error`,
   `integral_normSq_ramareBilinear_le_halaszMontgomery_huxley_ladder`,
   `menonFinalRangeFullEnergy_le_halaszMontgomery_huxley_ladder_add_harmonic`):**
   Combines `RamareBlockSplit.integral_normSq_ramareBilinear_le_ladder_error` with
   `RamareLadderErrorSharp.integral_normSq_ramareLadderError_le_sharp` (which eliminates the
   `log M / log Q` divisor-multiplicity factor via the Ramaré weight cap `‖μ(p) c_m‖ ≤ 1/ω_P(pm)`)
   and the step-by-step Halász–Montgomery–Huxley + Kuzmin–Landau bound, and feeds the resulting
   bilinear bound into `menonFinalRangeFullEnergy_le_two_mul_bilinear_add_harmonic`.
-/

open Finset MeasureTheory
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-! ## §1. Exact Initial-Interval Identification of `geomCofactorBlock` -/

/-- For `1 ≤ Q` and `0 ≤ η`, the common cofactor block `geomCofactorBlock M Q η j` of the `j`-th
Ramaré ladder step is literally the initial interval `Finset.Icc 1 ⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊`. -/
theorem geomCofactorBlock_eq_Icc_one (M : ℕ) {Q η : ℝ} (hQ : 1 ≤ Q) (hη : 0 ≤ η) (j : ℕ) :
    geomCofactorBlock M Q η j = Finset.Icc 1 ⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊ := by
  rw [← geomCofactorBlockAt_one M Q η j, geomCofactorBlockAt_one_eq hQ hη j]

/-! ## §2. Discharged Halász–Montgomery–Huxley + Kuzmin–Landau Bound on One Ladder Step -/

/-- **Halász–Montgomery–Huxley Bound on the `j`-th Geometric Ramaré Ladder Step
(`integral_normSq_ramareLadderStep_le_halaszMontgomery_huxley_const`):**
Rewriting `geomCofactorBlock M Q η j` via `geomCofactorBlock_eq_Icc_one` allows
`integral_normSq_blockProduct_le_halaszMontgomery_huxley_const` to bound the `j`-th step product
without any pointwise prime-block supremum hypothesis. -/
theorem integral_normSq_ramareLadderStep_le_halaszMontgomery_huxley_const
    (P : Finset ℕ) (M : ℕ) {Q η W : ℝ} (hQ : 1 ≤ Q) (hη : 0 ≤ η) (hW : 0 ≤ W)
    (j : ℕ) {N : ℕ} (hN : 1 ≤ N)
    (hB : geomBlock P Q (1 + η) j ⊆ Finset.Ico N (2 * N))
    {U V₀ E sigma₀ : ℝ} (hU : 0 < U) (hV₀ : 0 < V₀) (hE : 0 ≤ E)
    (hmass : ((geomBlock P Q (1 + η) j).card : ℝ) ≤ E / (N : ℝ))
    {J : ℕ} (hJ : (((geomBlock P Q (1 + η) j).card : ℕ) : ℝ) ≤ 2 ^ J * V₀)
    (hnear : ∀ i : ℕ, 3 * U ≤ 4 * Real.pi * ((2 ^ i : ℕ) : ℝ))
    (hlam : ∀ i : ℕ, logDyadicLambda (2 ^ i) (4 * Real.pi * W) ≤ 1)
    (hthr : 2400 * E ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - 2 * sigma₀))
    (hV₀_ge : (N : ℝ) ^ (-sigma₀) ≤ V₀) :
    (∫ w in Set.Icc (-W) W,
        ‖primeBlockPoly (geomBlock P Q (1 + η) j) w
          * logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ^ (2 : ℕ))
      ≤ V₀ ^ (2 : ℕ) *
          (∫ w in Set.Icc (-W) W,
            ‖logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ^ (2 : ℕ))
        + ∑ k ∈ Finset.range J, (2 ^ (k + 1) * V₀) ^ (2 : ℕ) *
            (2 * (((Nat.log 2 ⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊ + 1 : ℕ) : ℝ) *
              ∑ i ∈ Finset.range (Nat.log 2 ⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊ + 1),
                halaszBlockBound (ramareCofactorCoeff P) ⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊ W U i
                  (huxleyPrimeBlockLevelSetBound N W E sigma₀))) := by
  have hblk := geomCofactorBlock_eq_Icc_one M hQ hη j
  rw [hblk]
  exact integral_normSq_blockProduct_le_halaszMontgomery_huxley_const
    (ramareCofactorCoeff P) ⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊ hN hB hW hU hV₀ hE hmass hJ
    hnear hlam hthr hV₀_ge

/-- Explicit closed majorant for the `j`-th Ramaré ladder step combining the Kuzmin–Landau
reciprocal cofactor bound on the sub-threshold region `‖primeBlockPoly‖ ≤ V₀` with the
Halász–Montgomery–Huxley dyadic level-set sum above `V₀`. -/
def ramareStepHalaszHuxleyKuzminLandauBound
    (P : Finset ℕ) (M : ℕ) (Q η W : ℝ) (j N J : ℕ) (U V₀ E sigma₀ : ℝ) : ℝ :=
  V₀ ^ (2 : ℕ) * ladderHMBoundRecip M Q η W (volume.real (Set.Icc (-W) W)) j
    + ∑ k ∈ Finset.range J, (2 ^ (k + 1) * V₀) ^ (2 : ℕ) *
        (2 * (((Nat.log 2 ⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊ + 1 : ℕ) : ℝ) *
          ∑ i ∈ Finset.range (Nat.log 2 ⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊ + 1),
            halaszBlockBound (ramareCofactorCoeff P) ⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊ W U i
              (huxleyPrimeBlockLevelSetBound N W E sigma₀)))

/-- **Halász–Montgomery–Huxley + Kuzmin–Landau Bound on the `j`-th Geometric Ramaré Ladder Step
(`integral_normSq_ramareLadderStep_le_halaszMontgomery_huxley_kuzminLandau`):**
Discharges the sub-threshold cofactor integral in
`integral_normSq_ramareLadderStep_le_halaszMontgomery_huxley_const` using
`setIntegral_normSq_cofactorBlock_le_HM_recip`. -/
theorem integral_normSq_ramareLadderStep_le_halaszMontgomery_huxley_kuzminLandau
    (P : Finset ℕ) (M : ℕ) {Q η W : ℝ} (hQ : 1 ≤ Q) (hη : 0 ≤ η) (hW : 1 ≤ W)
    (j : ℕ) (hNj : 1 ≤ ⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊)
    {N : ℕ} (hN : 1 ≤ N)
    (hB : geomBlock P Q (1 + η) j ⊆ Finset.Ico N (2 * N))
    {U V₀ E sigma₀ : ℝ} (hU : 0 < U) (hV₀ : 0 < V₀) (hE : 0 ≤ E)
    (hmass : ((geomBlock P Q (1 + η) j).card : ℝ) ≤ E / (N : ℝ))
    {J : ℕ} (hJ : (((geomBlock P Q (1 + η) j).card : ℕ) : ℝ) ≤ 2 ^ J * V₀)
    (hnear : ∀ i : ℕ, 3 * U ≤ 4 * Real.pi * ((2 ^ i : ℕ) : ℝ))
    (hlam : ∀ i : ℕ, logDyadicLambda (2 ^ i) (4 * Real.pi * W) ≤ 1)
    (hthr : 2400 * E ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - 2 * sigma₀))
    (hV₀_ge : (N : ℝ) ^ (-sigma₀) ≤ V₀) :
    (∫ w in Set.Icc (-W) W,
        ‖primeBlockPoly (geomBlock P Q (1 + η) j) w
          * logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ^ (2 : ℕ))
      ≤ ramareStepHalaszHuxleyKuzminLandauBound P M Q η W j N J U V₀ E sigma₀ := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hstep := integral_normSq_ramareLadderStep_le_halaszMontgomery_huxley_const
    P M hQ hη hW0 j hN hB hU hV₀ hE hmass hJ hnear hlam hthr hV₀_ge
  have hcof := setIntegral_normSq_cofactorBlock_le_HM_recip P M hQ0 hη hW hNj
    measurableSet_Icc (Set.Subset.refl _)
  rw [ramareStepHalaszHuxleyKuzminLandauBound]
  have hmul : V₀ ^ (2 : ℕ) *
      (∫ w in Set.Icc (-W) W,
        ‖logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ^ (2 : ℕ))
      ≤ V₀ ^ (2 : ℕ) * ladderHMBoundRecip M Q η W (volume.real (Set.Icc (-W) W)) j :=
    mul_le_mul_of_nonneg_left hcof (sq_nonneg V₀)
  linarith

/-! ## §3. Multiplicity-Free Global Ramaré Ladder Assembly -/

/-- **Ramaré Bilinear Mean Square with Multiplicity-Free Ladder Error
(`integral_normSq_ramareBilinear_le_sharp_ladder_error`):**
Combines `RamareBlockSplit.integral_normSq_ramareBilinear_le_ladder_error` with
`RamareLadderErrorSharp.integral_normSq_ramareLadderError_le_sharp`, eliminating the
`log M / log Q` divisor-multiplicity factor from the global ladder error. -/
theorem integral_normSq_ramareBilinear_le_sharp_ladder_error
    {P : Finset ℕ} (M : ℕ) {Q η W : ℝ} (hQ : 1 ≤ Q) (hη : 0 ≤ η) (hW : 1 ≤ W)
    {L : ℕ} (hL : 1 ≤ L) (hPprime : ∀ q ∈ P, q.Prime)
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L) :
    (∫ w in Set.Icc (-W) W, ‖ramareBilinear P M w‖ ^ (2 : ℕ))
      ≤ 2 * (L : ℝ) * ∑ j ∈ Finset.range L,
          (∫ w in Set.Icc (-W) W,
            ‖primeBlockPoly (geomBlock P Q (1 + η) j) w
              * logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ^ (2 : ℕ))
        + 4 * (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((⌊(M : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ))
            * (η * (M : ℝ) + 6 * (M : ℝ) / Q) := by
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hsplit := integral_normSq_ramareBilinear_le_ladder_error M hQ0 hη hL hP (W := W)
  have herr := integral_normSq_ramareLadderError_le_sharp M hQ hη hW L hPprime
    (fun p hp => (hP p hp).1)
  linarith

/-- **Complete Unconditional Halász–Montgomery–Huxley + Kuzmin–Landau + Sharp-Error Bound on the
Ramaré Bilinear Form (`integral_normSq_ramareBilinear_le_halaszMontgomery_huxley_ladder`):**
Assembles the step-by-step discharged Halász–Montgomery–Huxley + Kuzmin–Landau bound across all
`L` steps of the geometric prime ladder together with the multiplicity-free ladder error bound. -/
theorem integral_normSq_ramareBilinear_le_halaszMontgomery_huxley_ladder
    {P : Finset ℕ} (M : ℕ) {Q η W : ℝ} (hQ : 1 ≤ Q) (hη : 0 ≤ η) (hW : 1 ≤ W)
    {L : ℕ} (hL : 1 ≤ L) (hPprime : ∀ q ∈ P, q.Prime)
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L)
    (N J : ℕ → ℕ) (U V₀ E sigma₀ : ℕ → ℝ)
    (hNj : ∀ j ∈ Finset.range L, 1 ≤ ⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊)
    (hN : ∀ j ∈ Finset.range L, 1 ≤ N j)
    (hB : ∀ j ∈ Finset.range L, geomBlock P Q (1 + η) j ⊆ Finset.Ico (N j) (2 * N j))
    (hU : ∀ j ∈ Finset.range L, 0 < U j)
    (hV₀ : ∀ j ∈ Finset.range L, 0 < V₀ j)
    (hE : ∀ j ∈ Finset.range L, 0 ≤ E j)
    (hmass : ∀ j ∈ Finset.range L,
      ((geomBlock P Q (1 + η) j).card : ℝ) ≤ E j / (N j : ℝ))
    (hJ : ∀ j ∈ Finset.range L,
      (((geomBlock P Q (1 + η) j).card : ℕ) : ℝ) ≤ 2 ^ (J j) * V₀ j)
    (hnear : ∀ j ∈ Finset.range L, ∀ i : ℕ, 3 * U j ≤ 4 * Real.pi * ((2 ^ i : ℕ) : ℝ))
    (hlam : ∀ i : ℕ, logDyadicLambda (2 ^ i) (4 * Real.pi * W) ≤ 1)
    (hthr : ∀ j ∈ Finset.range L, 2400 * E j ≤ (N j : ℝ) ^ ((1 : ℝ) / 2 - 2 * sigma₀ j))
    (hV₀_ge : ∀ j ∈ Finset.range L, (N j : ℝ) ^ (-sigma₀ j) ≤ V₀ j) :
    (∫ w in Set.Icc (-W) W, ‖ramareBilinear P M w‖ ^ (2 : ℕ))
      ≤ 2 * (L : ℝ) * ∑ j ∈ Finset.range L,
          ramareStepHalaszHuxleyKuzminLandauBound P M Q η W j (N j) (J j)
            (U j) (V₀ j) (E j) (sigma₀ j)
        + 4 * (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((⌊(M : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ))
            * (η * (M : ℝ) + 6 * (M : ℝ) / Q) := by
  have hbase := integral_normSq_ramareBilinear_le_sharp_ladder_error M hQ hη hW hL hPprime hP
  have hsum :
      (∑ j ∈ Finset.range L,
        ∫ w in Set.Icc (-W) W,
          ‖primeBlockPoly (geomBlock P Q (1 + η) j) w
            * logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ^ (2 : ℕ))
      ≤ ∑ j ∈ Finset.range L,
          ramareStepHalaszHuxleyKuzminLandauBound P M Q η W j (N j) (J j)
            (U j) (V₀ j) (E j) (sigma₀ j) := by
    refine Finset.sum_le_sum fun j hj => ?_
    exact integral_normSq_ramareLadderStep_le_halaszMontgomery_huxley_kuzminLandau
      P M hQ hη hW j (hNj j hj) (hN j hj) (hB j hj) (hU j hj) (hV₀ j hj) (hE j hj)
      (hmass j hj) (hJ j hj) (hnear j hj) hlam (hthr j hj) (hV₀_ge j hj)
  have h2L : 0 ≤ 2 * (L : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsum h2L
  linarith

/-- **Menon's Final-Range Full Möbius Energy Bounded by the Discharged Halász–Montgomery–Huxley
Ramaré Ladder plus Turán Harmonic Rough Energy
(`menonFinalRangeFullEnergy_le_halaszMontgomery_huxley_ladder_add_harmonic`):**
Combines `menonFinalRangeFullEnergy_le_two_mul_bilinear_add_harmonic` with
`integral_normSq_ramareBilinear_le_halaszMontgomery_huxley_ladder` on `menonFinalRangePrimes x` and
`menonFinalRangeTopNat x`. -/
theorem menonFinalRangeFullEnergy_le_halaszMontgomery_huxley_ladder_add_harmonic
    {x Q η : ℝ} (hx : 1 ≤ x) (hQ : 1 ≤ Q) (hη : 0 ≤ η)
    {L : ℕ} (hL : 1 ≤ L)
    (hP : ∀ p ∈ menonFinalRangePrimes x, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L)
    (hA : 0 < ∑ p ∈ menonFinalRangePrimes x, (1 : ℝ) / (p : ℝ))
    (N J : ℕ → ℕ) (U V₀ E sigma₀ : ℕ → ℝ)
    (hNj : ∀ j ∈ Finset.range L,
      1 ≤ ⌊(menonFinalRangeTopNat x : ℝ) / (Q * (1 + η) ^ j)⌋₊)
    (hN : ∀ j ∈ Finset.range L, 1 ≤ N j)
    (hB : ∀ j ∈ Finset.range L,
      geomBlock (menonFinalRangePrimes x) Q (1 + η) j ⊆ Finset.Ico (N j) (2 * N j))
    (hU : ∀ j ∈ Finset.range L, 0 < U j)
    (hV₀ : ∀ j ∈ Finset.range L, 0 < V₀ j)
    (hE : ∀ j ∈ Finset.range L, 0 ≤ E j)
    (hmass : ∀ j ∈ Finset.range L,
      ((geomBlock (menonFinalRangePrimes x) Q (1 + η) j).card : ℝ) ≤ E j / (N j : ℝ))
    (hJ : ∀ j ∈ Finset.range L,
      (((geomBlock (menonFinalRangePrimes x) Q (1 + η) j).card : ℕ) : ℝ) ≤ 2 ^ (J j) * V₀ j)
    (hnear : ∀ j ∈ Finset.range L, ∀ i : ℕ, 3 * U j ≤ 4 * Real.pi * ((2 ^ i : ℕ) : ℝ))
    (hlam : ∀ i : ℕ, logDyadicLambda (2 ^ i) (4 * Real.pi * x) ≤ 1)
    (hthr : ∀ j ∈ Finset.range L, 2400 * E j ≤ (N j : ℝ) ^ ((1 : ℝ) / 2 - 2 * sigma₀ j))
    (hV₀_ge : ∀ j ∈ Finset.range L, (N j : ℝ) ^ (-sigma₀ j) ≤ V₀ j) :
    menonFinalRangeFullEnergy x ≤
      2 * (2 * (L : ℝ) * ∑ j ∈ Finset.range L,
            ramareStepHalaszHuxleyKuzminLandauBound (menonFinalRangePrimes x)
              (menonFinalRangeTopNat x) Q η x j (N j) (J j)
              (U j) (V₀ j) (E j) (sigma₀ j)
          + 4 * (5 * Real.pi / 2 * x +
              5 * Real.exp 1 / 2 * ((⌊(menonFinalRangeTopNat x : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ))
              * (η * (menonFinalRangeTopNat x : ℝ) + 6 * (menonFinalRangeTopNat x : ℝ) / Q))
        + 2 * ((5 * Real.pi / 2 * x + 5 * Real.exp 1 / 2 * (menonFinalRangeTopNat x : ℝ))
          * ((menonFinalRangeTopNat x : ℝ) / (∑ p ∈ menonFinalRangePrimes x, (1 : ℝ) / (p : ℝ))
            + 2 * ((menonFinalRangePrimes x).card : ℝ) /
                (∑ p ∈ menonFinalRangePrimes x, (1 : ℝ) / (p : ℝ)))) := by
  have hfull := menonFinalRangeFullEnergy_le_two_mul_bilinear_add_harmonic hx hA
  have hbil : menonFinalRangeBilinearEnergy x
      ≤ 2 * (L : ℝ) * ∑ j ∈ Finset.range L,
          ramareStepHalaszHuxleyKuzminLandauBound (menonFinalRangePrimes x)
            (menonFinalRangeTopNat x) Q η x j (N j) (J j)
            (U j) (V₀ j) (E j) (sigma₀ j)
        + 4 * (5 * Real.pi / 2 * x +
            5 * Real.exp 1 / 2 * ((⌊(menonFinalRangeTopNat x : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ))
            * (η * (menonFinalRangeTopNat x : ℝ) + 6 * (menonFinalRangeTopNat x : ℝ) / Q) := by
    rw [menonFinalRangeBilinearEnergy]
    exact integral_normSq_ramareBilinear_le_halaszMontgomery_huxley_ladder
      (menonFinalRangeTopNat x) hQ hη hx hL (fun q hq => menonFinalRangePrimes_prime x hq) hP
      N J U V₀ E sigma₀ hNj hN hB hU hV₀ hE hmass hJ hnear hlam hthr hV₀_ge
  linarith

end

end GaloisForLFunctions.BiScaleUncertainty
