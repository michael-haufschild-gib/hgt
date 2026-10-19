import GaloisForLFunctions.BiScaleUncertainty.CriticalBandLargeValuesAndHalaszSpectralBounds
import GaloisForLFunctions.RHTower.Sieve.BlockProductHalaszExplicit
import GaloisForLFunctions.RHTower.Sieve.MenonFinalRangeRamareReduction

/-!
# Prime-Block Level-Set Rarity, Discharged Halász–Montgomery–Huxley Bilinear Bounds, and Menon's Final-Range Ramaré Reduction

This module connects `BiScaleUncertainty` to the prime-block level-set discretisation,
Halász–Montgomery–Huxley bilinear block bounds, and Menon's final-range Ramaré reduction in
`RHTower/Sieve/`:

1. **Discharging the Level-Set Count in `integral_normSq_blockProduct_le_halaszMontgomery` via
   `card_le_of_mem_primeBlockLevelSet` (`huxleyPrimeBlockLevelSetBound`,
   `card_le_huxleyPrimeBlockLevelSetBound_of_le`,
   `integral_normSq_blockProduct_le_halaszMontgomery_huxley`,
   `integral_normSq_blockProduct_le_halaszMontgomery_huxley_const`):**
   In `BlockProductHalaszExplicit.lean`, `integral_normSq_blockProduct_le_halaszMontgomery` leaves
   the per-level one-spaced family cardinality bound `C : ℕ → ℝ` (`1 ≤ C j` and `(P.card : ℝ) ≤ C j`)
   as an uninstantiated hypothesis. Here we define `huxleyPrimeBlockLevelSetBound N G E sigma` and
   use `PrimeBlockLevelSetCount.card_le_of_mem_primeBlockLevelSet` together with threshold
   monotonicity of `primeBlockLevelSet` to discharge `C`, `hC1`, and `hC` unconditionally.
2. **Halász–Montgomery Self-Duality Bound on `primeBlockLevelSet`
   (`sum_normSq_primeBlockPoly_le_halaszMontgomery`,
   `card_mul_sq_le_of_mem_primeBlockLevelSet_halaszMontgomery`):**
   Applies `halaszMontgomery_logPoly_finset` and `normSq_moebiusBlockCoeff_le` directly to
   `primeBlockPoly B` on any one-spaced family `P` inside `primeBlockLevelSet B G V`, bounding
   `(P.card : ℝ) * V^2` by the Halász–Montgomery quadratic form times `B.card`.
3. **Menon's Final-Range Ramaré Reduction with Explicit Turán Harmonic Rough Energy
   (`menonFinalRangeRoughEnergy_le_harmonic`,
   `menonFinalRangeFullEnergy_le_two_mul_bilinear_add_harmonic`):**
   Combines `MenonFinalRangeRamareReduction.menonFinalRangeFullEnergy_le_two_mul_bilinear_add_rough`
   with `RamareRoughSetSplit.integral_Icc_normSq_roughPoly_le_harmonic` to bound
   `menonFinalRangeRoughEnergy x` and `menonFinalRangeFullEnergy x` explicitly in terms of
   `menonFinalRangeBilinearEnergy x` and the harmonic prime sum on `menonFinalRangePrimes x`.
-/

open Finset MeasureTheory Filter Topology
open RHTower RHTower.Sieve
open scoped InnerProductSpace BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-! ## §1. Discharging the Level-Set Count in `integral_normSq_blockProduct_le_halaszMontgomery` -/

/-- Explicit Huxley two-term cardinality bound for a one-spaced frequency family inside
`primeBlockLevelSet B G ((N : ℝ) ^ (-sigma))`, clamped below at `1` so that `halaszBlockBound_mono`
applies without extra positivity side conditions. -/
def huxleyPrimeBlockLevelSetBound (N : ℕ) (G E sigma : ℝ) : ℝ :=
  max 1
    ((6594624 * (2 * Real.pi * G) * E ^ 3 * (N : ℝ) ^ (6 * sigma - 2)
          + 2 * E * (N : ℝ) ^ (2 * sigma))
        * (1 + 12 * Real.pi * (1 + Real.log (2 * (2 * Real.pi * G) + 1))))

/-- `huxleyPrimeBlockLevelSetBound` is always at least `1`. -/
theorem one_le_huxleyPrimeBlockLevelSetBound (N : ℕ) (G E sigma : ℝ) :
    1 ≤ huxleyPrimeBlockLevelSetBound N G E sigma :=
  le_max_left _ _

/-- Threshold anti-monotonicity of `primeBlockLevelSet`: if `V₁ ≤ V₂`, then every frequency where
`‖primeBlockPoly B w‖ ≥ V₂` also satisfies `‖primeBlockPoly B w‖ ≥ V₁`. -/
theorem primeBlockLevelSet_mono_right (B : Finset ℕ) (G : ℝ) {V₁ V₂ : ℝ} (hV : V₁ ≤ V₂) :
    primeBlockLevelSet B G V₂ ⊆ primeBlockLevelSet B G V₁ := by
  intro w hw
  exact ⟨hw.1, hV.trans hw.2⟩

/-- Any one-spaced family `P` inside `primeBlockLevelSet B G V` with `(N : ℝ) ^ (-sigma) ≤ V` has
cardinality at most `huxleyPrimeBlockLevelSetBound N G E sigma`. -/
theorem card_le_huxleyPrimeBlockLevelSetBound_of_le {N : ℕ} (hN : 1 ≤ N) {B : Finset ℕ}
    (hB : B ⊆ Finset.Ico N (2 * N)) {G E sigma V : ℝ} (hG : 0 ≤ G) (hE : 0 ≤ E)
    (hmass : (B.card : ℝ) ≤ E / (N : ℝ))
    (hthr : 2400 * E ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - 2 * sigma))
    (hV : (N : ℝ) ^ (-sigma) ≤ V)
    (P : Finset ℝ)
    (hPsep : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (1 : ℝ) ≤ |x - y|)
    (hPmem : ∀ x ∈ P, x ∈ primeBlockLevelSet B G V) :
    (P.card : ℝ) ≤ huxleyPrimeBlockLevelSetBound N G E sigma := by
  have hPmem' : ∀ x ∈ P, x ∈ primeBlockLevelSet B G ((N : ℝ) ^ (-sigma)) :=
    fun x hx => primeBlockLevelSet_mono_right B G hV (hPmem x hx)
  exact (card_le_of_mem_primeBlockLevelSet hN hB hG hE hmass hthr P hPsep hPmem').trans
    (le_max_right _ _)

/-- **Discharged Halász–Montgomery–Huxley Bound on the Möbius Bilinear Block
(`integral_normSq_blockProduct_le_halaszMontgomery_huxley`):**
Instantiates the abstract level-set counting function `C : ℕ → ℝ` in
`integral_normSq_blockProduct_le_halaszMontgomery` with
`fun j => huxleyPrimeBlockLevelSetBound N G E (sigma j)`, discharging `hC1` and `hC` via
`card_le_huxleyPrimeBlockLevelSetBound_of_le`. -/
theorem integral_normSq_blockProduct_le_halaszMontgomery_huxley
    (a : ℕ → ℂ) (M : ℕ) {N : ℕ} (hN : 1 ≤ N) {B : Finset ℕ}
    (hB : B ⊆ Finset.Ico N (2 * N))
    {G U V₀ E : ℝ} (hG : 0 ≤ G) (hU : 0 < U) (hV₀ : 0 < V₀) (hE : 0 ≤ E)
    (hmass : (B.card : ℝ) ≤ E / (N : ℝ))
    {J : ℕ} (hJ : ((B.card : ℕ) : ℝ) ≤ 2 ^ J * V₀)
    (hnear : ∀ i : ℕ, 3 * U ≤ 4 * Real.pi * ((2 ^ i : ℕ) : ℝ))
    (hlam : ∀ i : ℕ, logDyadicLambda (2 ^ i) (4 * Real.pi * G) ≤ 1)
    (sigma : ℕ → ℝ)
    (hthr : ∀ j : ℕ, 2400 * E ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - 2 * sigma j))
    (hlevel : ∀ j : ℕ, (N : ℝ) ^ (-sigma j) ≤ 2 ^ j * V₀) :
    (∫ w in Set.Icc (-G) G, ‖primeBlockPoly B w * logPoly a (Finset.Icc 1 M) w‖ ^ (2 : ℕ))
      ≤ V₀ ^ (2 : ℕ) * (∫ w in Set.Icc (-G) G, ‖logPoly a (Finset.Icc 1 M) w‖ ^ (2 : ℕ))
        + ∑ j ∈ Finset.range J, (2 ^ (j + 1) * V₀) ^ (2 : ℕ) *
            (2 * (((Nat.log 2 M + 1 : ℕ) : ℝ) *
              ∑ i ∈ Finset.range (Nat.log 2 M + 1),
                halaszBlockBound a M G U i
                  (huxleyPrimeBlockLevelSetBound N G E (sigma j)))) := by
  refine integral_normSq_blockProduct_le_halaszMontgomery a M B hG hU hV₀ hJ hnear hlam
    (fun j => huxleyPrimeBlockLevelSetBound N G E (sigma j))
    (fun j => one_le_huxleyPrimeBlockLevelSetBound N G E (sigma j)) ?_
  intro j P hPsep hPmem
  exact card_le_huxleyPrimeBlockLevelSetBound_of_le hN hB hG hE hmass (hthr j) (hlevel j)
    P hPsep hPmem

/-- **Base-Threshold Halász–Montgomery–Huxley Bound on the Möbius Bilinear Block
(`integral_normSq_blockProduct_le_halaszMontgomery_huxley_const`):**
When the base level `V₀` satisfies `(N : ℝ) ^ (-sigma₀) ≤ V₀`, every dyadic level `2 ^ j * V₀`
automatically satisfies `(N : ℝ) ^ (-sigma₀) ≤ 2 ^ j * V₀`, yielding a completely self-contained
bilinear block estimate with a single exponent `sigma₀`. -/
theorem integral_normSq_blockProduct_le_halaszMontgomery_huxley_const
    (a : ℕ → ℂ) (M : ℕ) {N : ℕ} (hN : 1 ≤ N) {B : Finset ℕ}
    (hB : B ⊆ Finset.Ico N (2 * N))
    {G U V₀ E sigma₀ : ℝ} (hG : 0 ≤ G) (hU : 0 < U) (hV₀ : 0 < V₀) (hE : 0 ≤ E)
    (hmass : (B.card : ℝ) ≤ E / (N : ℝ))
    {J : ℕ} (hJ : ((B.card : ℕ) : ℝ) ≤ 2 ^ J * V₀)
    (hnear : ∀ i : ℕ, 3 * U ≤ 4 * Real.pi * ((2 ^ i : ℕ) : ℝ))
    (hlam : ∀ i : ℕ, logDyadicLambda (2 ^ i) (4 * Real.pi * G) ≤ 1)
    (hthr : 2400 * E ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - 2 * sigma₀))
    (hV₀_ge : (N : ℝ) ^ (-sigma₀) ≤ V₀) :
    (∫ w in Set.Icc (-G) G, ‖primeBlockPoly B w * logPoly a (Finset.Icc 1 M) w‖ ^ (2 : ℕ))
      ≤ V₀ ^ (2 : ℕ) * (∫ w in Set.Icc (-G) G, ‖logPoly a (Finset.Icc 1 M) w‖ ^ (2 : ℕ))
        + ∑ j ∈ Finset.range J, (2 ^ (j + 1) * V₀) ^ (2 : ℕ) *
            (2 * (((Nat.log 2 M + 1 : ℕ) : ℝ) *
              ∑ i ∈ Finset.range (Nat.log 2 M + 1),
                halaszBlockBound a M G U i
                  (huxleyPrimeBlockLevelSetBound N G E sigma₀))) := by
  refine integral_normSq_blockProduct_le_halaszMontgomery_huxley a M hN hB hG hU hV₀ hE hmass hJ
    hnear hlam (fun _ => sigma₀) (fun _ => hthr) (fun j => ?_)
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  nlinarith

/-! ## §2. Halász–Montgomery Self-Duality Bound on `primeBlockLevelSet` -/

/-- Applying `halaszMontgomery_logPoly_finset` and `normSq_moebiusBlockCoeff_le` directly to
`primeBlockPoly B` bounds its discrete `L²` sum over any one-spaced family `P` of spread `≤ 2 * G`
by the Halász–Montgomery factor times `B.card`. -/
theorem sum_normSq_primeBlockPoly_le_halaszMontgomery
    {N : ℕ} (hN : 1 ≤ N) {B : Finset ℕ} (hB : B ⊆ Finset.Ico N (2 * N))
    {P : Finset ℝ} {G U : ℝ} (hG : 0 ≤ G) (hU : 0 < U)
    (hsep : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (1 : ℝ) ≤ |x - y|)
    (hspread : ∀ x ∈ P, ∀ y ∈ P, |x - y| ≤ 2 * G)
    (hnear : 3 * U ≤ 4 * Real.pi * (N : ℝ))
    (hlamT : logDyadicLambda N (4 * Real.pi * G) ≤ 1) :
    ∑ w ∈ P, ‖primeBlockPoly B w‖ ^ (2 : ℕ) ≤
      ((N : ℝ) + (12 * Real.pi * (N : ℝ) / (2 * Real.pi)) * (1 + Real.log P.card)
          + (P.card : ℝ) *
            (1 + 214 * Real.sqrt (4 * Real.pi * G)
              + 1536 * ((N : ℝ) / Real.sqrt U))) *
        (B.card : ℝ) := by
  have hrw : (∑ w ∈ P, ‖primeBlockPoly B w‖ ^ (2 : ℕ)) =
      ∑ w ∈ P, ‖logPoly moebiusCoeff B w‖ ^ (2 : ℕ) := by
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [primeBlockPoly_eq_logPoly_primeBlockLevelSetCount]
  rw [hrw]
  refine (halaszMontgomery_logPoly_finset hN hB moebiusCoeff hG hU hsep hspread hnear hlamT).trans ?_
  have hfac : 0 ≤ (N : ℝ) + (12 * Real.pi * (N : ℝ) / (2 * Real.pi)) * (1 + Real.log P.card)
      + (P.card : ℝ) *
        (1 + 214 * Real.sqrt (4 * Real.pi * G)
          + 1536 * ((N : ℝ) / Real.sqrt U)) := by
    rcases P.eq_empty_or_nonempty with rfl | hne
    · simp; positivity
    · have hcard1 : (1 : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hne
      have hlog0 : 0 ≤ Real.log (P.card : ℝ) := Real.log_nonneg hcard1
      positivity
  exact mul_le_mul_of_nonneg_left (normSq_moebiusBlockCoeff_le hB) hfac

/-- **Halász–Montgomery Level-Set Rarity Inequality
(`card_mul_sq_le_of_mem_primeBlockLevelSet_halaszMontgomery`):**
For any one-spaced family `P` inside `primeBlockLevelSet B G V` (`0 ≤ V`), `(P.card : ℝ) * V^2` is
bounded by the Halász–Montgomery quadratic form times `B.card`. -/
theorem card_mul_sq_le_of_mem_primeBlockLevelSet_halaszMontgomery
    {N : ℕ} (hN : 1 ≤ N) {B : Finset ℕ} (hB : B ⊆ Finset.Ico N (2 * N))
    {P : Finset ℝ} {G U V : ℝ} (hG : 0 ≤ G) (hU : 0 < U) (hV : 0 ≤ V)
    (hsep : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (1 : ℝ) ≤ |x - y|)
    (hmem : ∀ x ∈ P, x ∈ primeBlockLevelSet B G V)
    (hnear : 3 * U ≤ 4 * Real.pi * (N : ℝ))
    (hlamT : logDyadicLambda N (4 * Real.pi * G) ≤ 1) :
    (P.card : ℝ) * V ^ (2 : ℕ) ≤
      ((N : ℝ) + (12 * Real.pi * (N : ℝ) / (2 * Real.pi)) * (1 + Real.log P.card)
          + (P.card : ℝ) *
            (1 + 214 * Real.sqrt (4 * Real.pi * G)
              + 1536 * ((N : ℝ) / Real.sqrt U))) *
        (B.card : ℝ) := by
  have hspread : ∀ x ∈ P, ∀ y ∈ P, |x - y| ≤ 2 * G := by
    intro x hx y hy
    have hx' := (hmem x hx).1
    have hy' := (hmem y hy).1
    rw [Set.mem_Icc] at hx' hy'
    rw [abs_le]
    constructor <;> linarith [hx'.1, hx'.2, hy'.1, hy'.2]
  have hlower : (P.card : ℝ) * V ^ (2 : ℕ) ≤ ∑ w ∈ P, ‖primeBlockPoly B w‖ ^ (2 : ℕ) := by
    calc
      (P.card : ℝ) * V ^ (2 : ℕ) = ∑ _w ∈ P, V ^ (2 : ℕ) := by simp
      _ ≤ ∑ w ∈ P, ‖primeBlockPoly B w‖ ^ (2 : ℕ) := by
        refine Finset.sum_le_sum fun w hw => ?_
        exact pow_le_pow_left₀ hV (hmem w hw).2 2
  exact hlower.trans
    (sum_normSq_primeBlockPoly_le_halaszMontgomery hN hB hG hU hsep hspread hnear hlamT)

/-! ## §3. Menon's Final-Range Ramaré Reduction with Explicit Turán Harmonic Rough Energy -/

/-- Explicit Turán harmonic bound on `menonFinalRangeRoughEnergy x`: for `1 ≤ x` and positive
harmonic prime sum on `menonFinalRangePrimes x`, the rough Möbius mean square is bounded by the
reciprocal of the prime harmonic sum. -/
theorem menonFinalRangeRoughEnergy_le_harmonic {x : ℝ} (hx : 1 ≤ x)
    (hA : 0 < ∑ p ∈ menonFinalRangePrimes x, (1 : ℝ) / (p : ℝ)) :
    menonFinalRangeRoughEnergy x ≤
      (5 * Real.pi / 2 * x + 5 * Real.exp 1 / 2 * (menonFinalRangeTopNat x : ℝ))
        * ((menonFinalRangeTopNat x : ℝ) / (∑ p ∈ menonFinalRangePrimes x, (1 : ℝ) / (p : ℝ))
          + 2 * ((menonFinalRangePrimes x).card : ℝ) /
              (∑ p ∈ menonFinalRangePrimes x, (1 : ℝ) / (p : ℝ))) := by
  have hrw : menonFinalRangeRoughEnergy x =
      ∫ w in Set.Icc (-x) x,
        ‖logPoly (fun n => ((μ n : ℤ) : ℂ))
          (supportMeanSquareRoughSet (menonFinalRangePrimes x)
            (menonFinalRangeTopNat x)) w‖ ^ (2 : ℕ) := rfl
  rw [hrw]
  exact integral_Icc_normSq_roughPoly_le_harmonic
    (fun p hp => menonFinalRangePrimes_prime x hp) (menonFinalRangeTopNat x) hx hA

/-- **Menon's Final-Range Full Möbius Energy Bounded by Bilinear Energy plus Turán Harmonic Rough Cost
(`menonFinalRangeFullEnergy_le_two_mul_bilinear_add_harmonic`):**
Combines `menonFinalRangeFullEnergy_le_two_mul_bilinear_add_rough` with
`menonFinalRangeRoughEnergy_le_harmonic`. -/
theorem menonFinalRangeFullEnergy_le_two_mul_bilinear_add_harmonic {x : ℝ} (hx : 1 ≤ x)
    (hA : 0 < ∑ p ∈ menonFinalRangePrimes x, (1 : ℝ) / (p : ℝ)) :
    menonFinalRangeFullEnergy x ≤
      2 * menonFinalRangeBilinearEnergy x +
        2 * ((5 * Real.pi / 2 * x + 5 * Real.exp 1 / 2 * (menonFinalRangeTopNat x : ℝ))
          * ((menonFinalRangeTopNat x : ℝ) / (∑ p ∈ menonFinalRangePrimes x, (1 : ℝ) / (p : ℝ))
            + 2 * ((menonFinalRangePrimes x).card : ℝ) /
                (∑ p ∈ menonFinalRangePrimes x, (1 : ℝ) / (p : ℝ)))) := by
  have h1 := menonFinalRangeFullEnergy_le_two_mul_bilinear_add_rough x
  have h2 := menonFinalRangeRoughEnergy_le_harmonic hx hA
  linarith

end

end GaloisForLFunctions.BiScaleUncertainty
