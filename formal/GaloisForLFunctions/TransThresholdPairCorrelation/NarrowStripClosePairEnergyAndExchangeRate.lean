import GaloisForLFunctions.TransThresholdPairCorrelation.CoalescentSieveAnatomyAndModelCalibration
import GaloisForLFunctions.TransThresholdPairCorrelation.FejerWeightedPrimeMeanSquare
import GaloisForLFunctions.TransThresholdPairCorrelation.JacksonWeightedPrimeFrobeniusDecomposition
import GaloisForLFunctions.RHTower.PairCorrelationExchangeRate
import GaloisForLFunctions.RHTower.Sieve.PrimePairAverageSharp

/-!
# Narrow-Strip Close-Pair Energy, `2`-Adic Parity Collar Doubling, and the Exchange Rate Above `λ = 1`

This module resolves Open Problem 4 (*The exchange rate just above `λ = 1`*) of
`TransThresholdPairCorrelation` and applies the resulting spacing, parity-collar, and 2D-sieve
estimates across the corpus (`FejerWeightedPrimeMeanSquare`,
`JacksonWeightedPrimeFrobeniusDecomposition`, `PairCorrelationExchangeRate`, and
`PrimePairAverageSharp`):

1. **Universal narrow-strip exchange rate just above `λ = 1`
   (`narrowStrip_frobeniusFormFactor_eq`, `narrowStrip_proportion_gain_eq`,
   `narrowStrip_beats_two_thirds_iff`, `narrowStrip_gain_of_primeSurplusRatio`,
   `constrainedStrip_optimal_exchange_rate`):**
   At bandwidth `λ = 1 + δ` (`δ > 0`), let
   `narrowStripCesaroEnergy F δ := (2/δ²) ∫₁^{1+δ} (1 + δ − α) F(α) dα`
   be the Cesàro-weighted close-pair energy in `[1, 1 + δ]`. Then
   `(2 − frobeniusFormFactor F (1 + δ)) − 2/3 = δ (2 − (3 narrowStripCesaroEnergy F δ − 4) δ) / (3(1 + δ)²)`.
   Because the diagonal gain `2δ / (3(1 + δ)²)` is first-order in `δ` whereas the close-pair
   penalty is second-order (`δ² narrowStripCesaroEnergy F δ / (1 + δ)²`), the certified critical-line
   proportion strictly exceeds `2/3` if and only if
   `narrowStripCesaroEnergy F δ < 2/(3δ) + 4/3`
   (equivalently `generalPrimeSurplusRatio F (1 + δ) < δ(2 − δ)/(3(1 + δ))`).
   When `narrowStripCesaroEnergy F δ ≤ B` (`B > 1`) on `(0, δ₀]`, choosing `δ = min δ₀ (1/(3(B − 1)))`
   certifies a strictly positive gain over `2/3`, recovering `1/(3(3B − 2))` whenever
   `δ₀ ≥ 1/(3(B − 1))` and `δ₀ / (3(1 + δ₀)²) > 0` whenever `0 < δ₀ ≤ 1/(3(B − 1))`.

2. **Exact sub-threshold vanishing and `2`-adic parity doubling of the close-pair threshold
   (`log_sub_log_ge_sub_div`, `offDiag_triangleFn_eq_zero_of_le_inv_b`,
   `fejer_double_sum_eq_diag_of_le_inv_b`, `odd_offDiag_triangleFn_eq_zero_of_le_two_div_b`,
   `jacksonCloseApprox_offDiag_eq_zero_of_le_inv_four_b`,
   `jacksonPairKernel_odd_offDiag_eq_zero_of_le_inv_two_b`):**
   - For all `1 ≤ m < n`, `log n − log m ≥ (n − m) / n ≥ 1 / n`. Hence for `X ≤ 1/b`, every
     off-diagonal Fejér triangle weight `Λ_b(log n − log m)` (`m ≠ n ≤ X`) vanishes identically,
     reducing the Fejér double sum in `FejerWeightedPrimeMeanSquare` to the exact diagonal
     `Σ_{n≤X} Λ(n)²/n` with zero off-diagonal error.
   - For distinct odd integers `1 ≤ m < n`, `n − m ≥ 2` is even, so `log n − log m ≥ 2 / n`.
     Hence on the entire trans-threshold octave `X ≤ 2/b` (double the integer threshold `1/b`),
     every odd-odd off-diagonal Fejér weight `Λ_b(log n − log m)` vanishes identically, and any
     surviving off-diagonal close pair in `primeRange X` has `|n − m| = 1` with one member an even
     prime power `2^k > 1/b`.
   - For the Jackson pair kernel `W_b` (supported on `(−4b, 4b)`), every off-diagonal
     `jacksonCloseApprox` vanishes for `X ≤ 1/(4b)`, and all odd-odd off-diagonal terms vanish for
     `X ≤ 1/(2b)`.

3. **Trans-threshold strip confinement and 2D Selberg sieve bound on close prime pairs
   (`offDiag_triangleFn_support_strip`, `sieved_closePrimePair_strip_bound`):**
   For general `X > 1/b`, every nonzero off-diagonal Fejér close pair `m < n ≤ X` is confined to
   the trans-threshold strip `1/b < n ≤ X` with shift `1 ≤ n − m < b n ≤ b X`, and the weighted
   shifted prime-pair sum over `1 ≤ d ≤ K` is bounded unconditionally via
   `RHTower.Sieve.sum_card_primePair_le_sharp`, saving the two-dimensional Mertens factor
   `exp(mertensS h − mertensS P₁)²`.
-/

open MeasureTheory Real Set intervalIntegral Finset Zeta23.PrimeSide RHTower RHTower.Sieve
  RHTower.FejerWeight GaloisForLFunctions.HTGeometry
open scoped BigOperators ArithmeticFunction

noncomputable section

namespace GaloisForLFunctions.TransThresholdPairCorrelation

/-! ## 1. Universal Narrow-Strip Exchange Rate Just Above `λ = 1` -/

/-- The Cesàro-weighted close-pair energy in the narrow trans-threshold strip `[1, 1 + δ]`:
`narrowStripCesaroEnergy F δ = (2 / δ²) ∫₁^{1+δ} (1 + δ − α) F(α) dα`. -/
def narrowStripCesaroEnergy (F : ℝ → ℝ) (δ : ℝ) : ℝ :=
  (2 / δ ^ 2) * transThresholdIntegral F (1 + δ)

/-- **Exact Frobenius form-factor formula at `λ = 1 + δ` in terms of `narrowStripCesaroEnergy`:**
for `δ ≠ 0` and `1 + δ ≠ 0`, if `F` is continuous and `F(α) = α` on `[0, 1]`,
`frobeniusFormFactor F (1 + δ) = (4 + 6δ + 3δ² narrowStripCesaroEnergy F δ) / (3(1 + δ)²)`. -/
theorem narrowStrip_frobeniusFormFactor_eq {F : ℝ → ℝ} {δ : ℝ} (hδ : δ ≠ 0)
    (h1δ : 1 + δ ≠ 0) (hF_cont : Continuous F) (hF_sub : ∀ α ∈ Icc (0 : ℝ) 1, F α = α) :
    frobeniusFormFactor F (1 + δ)
      = (4 + 6 * δ + 3 * δ ^ 2 * narrowStripCesaroEnergy F δ) / (3 * (1 + δ) ^ 2) := by
  rw [frobeniusFormFactor_eq_split h1δ hF_cont hF_sub]
  unfold narrowStripCesaroEnergy
  field_simp
  ring

/-- **Universal narrow-strip proportion gain over `2/3`:**
for `δ ≠ 0` and `1 + δ ≠ 0`, if `F` is continuous and `F(α) = α` on `[0, 1]`,
`(2 − frobeniusFormFactor F (1 + δ)) − 2/3 = δ (2 − (3 narrowStripCesaroEnergy F δ − 4) δ) / (3(1 + δ)²)`. -/
theorem narrowStrip_proportion_gain_eq {F : ℝ → ℝ} {δ : ℝ} (hδ : δ ≠ 0)
    (h1δ : 1 + δ ≠ 0) (hF_cont : Continuous F) (hF_sub : ∀ α ∈ Icc (0 : ℝ) 1, F α = α) :
    (2 - frobeniusFormFactor F (1 + δ)) - 2 / 3
      = δ * (2 - (3 * narrowStripCesaroEnergy F δ - 4) * δ) / (3 * (1 + δ) ^ 2) := by
  rw [narrowStrip_frobeniusFormFactor_eq hδ h1δ hF_cont hF_sub]
  field_simp
  ring

/-- **Exact first-order vs. second-order criterion for beating `2/3` in a narrow strip `λ = 1 + δ`:**
for `0 < δ`, the certified critical-line proportion `2 − frobeniusFormFactor F (1 + δ)` strictly
exceeds `2/3` if and only if `narrowStripCesaroEnergy F δ < 2 / (3δ) + 4 / 3`
(equivalently, `transThresholdIntegral F (1 + δ) < δ / 3 + 2 δ² / 3`). -/
theorem narrowStrip_beats_two_thirds_iff {F : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hF_cont : Continuous F) (hF_sub : ∀ α ∈ Icc (0 : ℝ) 1, F α = α) :
    (2 / 3 < 2 - frobeniusFormFactor F (1 + δ) ↔
      narrowStripCesaroEnergy F δ < 2 / (3 * δ) + 4 / 3) ∧
    (2 / 3 < 2 - frobeniusFormFactor F (1 + δ) ↔
      transThresholdIntegral F (1 + δ) < δ / 3 + 2 * δ ^ 2 / 3) := by
  have h1δ : 0 < 1 + δ := by linarith
  have hgain := narrowStrip_proportion_gain_eq hδ.ne' h1δ.ne' hF_cont hF_sub
  have hden : 0 < 3 * (1 + δ) ^ 2 := by positivity
  have h3δ : 0 < 3 * δ := by positivity
  have hid : 3 * δ * (2 / (3 * δ) + 4 / 3) = 2 + 4 * δ := by
    have hcancel : 3 * δ * (2 / (3 * δ)) = 2 := mul_div_cancel₀ 2 h3δ.ne'
    linarith
  have hiff1 : 2 / 3 < 2 - frobeniusFormFactor F (1 + δ) ↔
      narrowStripCesaroEnergy F δ < 2 / (3 * δ) + 4 / 3 := by
    have hsub : 2 - frobeniusFormFactor F (1 + δ) - 2 / 3
        = δ * (2 - (3 * narrowStripCesaroEnergy F δ - 4) * δ) / (3 * (1 + δ) ^ 2) := hgain
    constructor
    · intro h
      have hpos : 0 < δ * (2 - (3 * narrowStripCesaroEnergy F δ - 4) * δ) / (3 * (1 + δ) ^ 2) := by
        linarith
      have hnum : 0 < δ * (2 - (3 * narrowStripCesaroEnergy F δ - 4) * δ) :=
        (div_pos_iff_of_pos_right hden).mp hpos
      have hpar : 0 < 2 - (3 * narrowStripCesaroEnergy F δ - 4) * δ :=
        (mul_pos_iff_of_pos_left hδ).mp hnum
      have hlt : 3 * δ * narrowStripCesaroEnergy F δ < 3 * δ * (2 / (3 * δ) + 4 / 3) := by linarith
      exact lt_of_mul_lt_mul_left hlt h3δ.le
    · intro h
      have hlt : 3 * δ * narrowStripCesaroEnergy F δ < 3 * δ * (2 / (3 * δ) + 4 / 3) :=
        mul_lt_mul_of_pos_left h h3δ
      have hpar : 0 < 2 - (3 * narrowStripCesaroEnergy F δ - 4) * δ := by linarith
      have hpos : 0 < δ * (2 - (3 * narrowStripCesaroEnergy F δ - 4) * δ) / (3 * (1 + δ) ^ 2) :=
        div_pos (mul_pos hδ hpar) hden
      linarith
  refine ⟨hiff1, hiff1.trans ?_⟩
  unfold narrowStripCesaroEnergy
  have hδ2 : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hid1 : δ ^ 2 * (2 / δ ^ 2 * transThresholdIntegral F (1 + δ))
      = 2 * transThresholdIntegral F (1 + δ) := by
    rw [← mul_assoc, mul_div_cancel₀ 2 hδ2.ne']
  have hid2 : 3 * (δ ^ 2 * (2 / (3 * δ) + 4 / 3)) = 6 * (δ / 3 + 2 * δ ^ 2 / 3) := by
    calc 3 * (δ ^ 2 * (2 / (3 * δ) + 4 / 3))
        = δ * (3 * δ * (2 / (3 * δ) + 4 / 3)) := by ring
      _ = δ * (2 + 4 * δ) := by rw [hid]
      _ = 6 * (δ / 3 + 2 * δ ^ 2 / 3) := by ring
  constructor
  · intro h
    have hm := mul_lt_mul_of_pos_left h hδ2
    linarith
  · intro h
    have hm : δ ^ 2 * (2 / δ ^ 2 * transThresholdIntegral F (1 + δ))
        < δ ^ 2 * (2 / (3 * δ) + 4 / 3) := by linarith
    exact lt_of_mul_lt_mul_left hm hδ2.le

/-- **Narrow-strip proportion gain in terms of the prime-side surplus ratio:**
for `1 + δ ≠ 0`,
`(2 − frobeniusFormFactor F (1 + δ)) − 2/3 = δ(2 − δ)/(3(1 + δ)) − generalPrimeSurplusRatio F (1 + δ)`. -/
theorem narrowStrip_gain_of_primeSurplusRatio {F : ℝ → ℝ} {δ : ℝ} (h1δ : 1 + δ ≠ 0)
    (hF_cont : Continuous F) (hF_sub : ∀ α ∈ Icc (0 : ℝ) 1, F α = α) :
    (2 - frobeniusFormFactor F (1 + δ)) - 2 / 3
      = δ * (2 - δ) / (3 * (1 + δ)) - generalPrimeSurplusRatio F (1 + δ) := by
  rw [(frobeniusFormFactor_eq_diag_add_generalPrimeSurplusRatio h1δ hF_cont hF_sub).1]
  field_simp
  ring

/-- **Constrained and unconstrained narrow-strip optimization theorem:**
Suppose `narrowStripCesaroEnergy F δ ≤ B` with `1 < B` and `0 < δ`.
1. For any `0 < δ ≤ 1 / (3(B − 1))`, `(2 − frobeniusFormFactor F (1 + δ)) − 2/3 ≥ δ / (3(1 + δ)²) > 0`.
2. At the optimal strip width `δ* = 1 / (3(B − 1))` (`1 + δ* = (3B − 2)/(3(B − 1))`),
   `(2 − frobeniusFormFactor F (1 + δ*)) − 2/3 ≥ 1 / (3(3B − 2)) > 0`. -/
theorem constrainedStrip_optimal_exchange_rate {F : ℝ → ℝ} {δ B : ℝ}
    (hB : 1 < B) (hδ : 0 < δ) (hδB : δ ≤ 1 / (3 * (B - 1)))
    (hF_cont : Continuous F) (hF_sub : ∀ α ∈ Icc (0 : ℝ) 1, F α = α)
    (hE : narrowStripCesaroEnergy F δ ≤ B) :
    δ * (2 - (3 * B - 4) * δ) / (3 * (1 + δ) ^ 2)
      ≤ (2 - frobeniusFormFactor F (1 + δ)) - 2 / 3 ∧
    δ / (3 * (1 + δ) ^ 2) ≤ δ * (2 - (3 * B - 4) * δ) / (3 * (1 + δ) ^ 2) ∧
    0 < δ / (3 * (1 + δ) ^ 2) ∧
    (δ = 1 / (3 * (B - 1)) →
      δ * (2 - (3 * B - 4) * δ) / (3 * (1 + δ) ^ 2) = 1 / (3 * (3 * B - 2))) := by
  have h1δ : 0 < 1 + δ := by linarith
  have hgain := narrowStrip_proportion_gain_eq hδ.ne' h1δ.ne' hF_cont hF_sub
  have hden : 0 < 3 * (1 + δ) ^ 2 := by positivity
  have hEδ : narrowStripCesaroEnergy F δ * δ ^ 2 ≤ B * δ ^ 2 :=
    mul_le_mul_of_nonneg_right hE (sq_nonneg δ)
  have h1 : δ * (2 - (3 * B - 4) * δ) / (3 * (1 + δ) ^ 2)
      ≤ (2 - frobeniusFormFactor F (1 + δ)) - 2 / 3 := by
    rw [hgain]
    exact div_le_div_of_nonneg_right (by linarith) hden.le
  have hB1 : 0 < 3 * (B - 1) := by linarith
  have hδ_prod : δ * (3 * (B - 1)) ≤ 1 := (le_div_iff₀ hB1).mp hδB
  have hδ2_prod : δ ^ 2 * (3 * (B - 1)) ≤ δ := by
    have := mul_le_mul_of_nonneg_left hδ_prod hδ.le
    linarith
  have h2 : δ / (3 * (1 + δ) ^ 2) ≤ δ * (2 - (3 * B - 4) * δ) / (3 * (1 + δ) ^ 2) := by
    apply div_le_div_of_nonneg_right _ hden.le
    have hsq : 0 ≤ δ ^ 2 := sq_nonneg δ
    have hexp : δ * (2 - (3 * B - 4) * δ) - δ = δ - δ ^ 2 * (3 * (B - 1)) + δ ^ 2 := by ring
    linarith
  refine ⟨h1, h2, by positivity, fun hδeq => ?_⟩
  rw [hδeq]
  have h3B2 : 3 * B - 2 ≠ 0 := by linarith
  have hB1' : B - 1 ≠ 0 := by linarith
  field_simp
  ring

/-! ## 2. Exact Sub-Threshold Close-Pair Vanishing and `2`-Adic Parity Collar Doubling -/

/-- **Fundamental lower bound on logarithmic spacing:** for `0 < m ≤ n`,
`(n − m) / n ≤ log n − log m`. -/
theorem log_sub_log_ge_sub_div {m n : ℝ} (hm : 0 < m) (hmn : m ≤ n) :
    (n - m) / n ≤ Real.log n - Real.log m := by
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  have h1 := Real.log_le_sub_one_of_pos (div_pos hm hn)
  rw [Real.log_div hm.ne' hn.ne'] at h1
  have h2 : m / n - 1 = -((n - m) / n) := by field_simp; ring
  linarith

/-- For `0 < b`, `0 < m ≤ n`, and `b * n ≤ n − m`, the Fejér triangle weight
`triangleFn b (log n − log m)` and its symmetric counterpart `triangleFn b (log m − log n)`
vanish identically. -/
theorem triangleFn_eq_zero_of_sub_ge {b m n : ℝ} (hb : 0 < b) (hm : 0 < m) (hmn : m ≤ n)
    (hbn : b * n ≤ n - m) :
    triangleFn b (Real.log n - Real.log m) = 0 ∧
      triangleFn b (Real.log m - Real.log n) = 0 := by
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  have hlog : b ≤ Real.log n - Real.log m := by
    have h1 : b ≤ (n - m) / n := (le_div_iff₀ hn).mpr hbn
    exact h1.trans (log_sub_log_ge_sub_div hm hmn)
  have hz : triangleFn b (Real.log n - Real.log m) = 0 := by
    apply triangleFn_eq_zero hb
    rw [abs_of_nonneg (by linarith)]
    exact hlog
  refine ⟨hz, ?_⟩
  apply triangleFn_eq_zero hb
  rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  exact hlog

/-- **Exact sub-threshold off-diagonal vanishing (`X ≤ 1/b`):**
for `0 < b` and `b * X ≤ 1`, every off-diagonal pair `n ≠ m` in `primeRange X` satisfies
`triangleFn b (log n − log m) = 0`. -/
theorem offDiag_triangleFn_eq_zero_of_le_inv_b {b X : ℝ} (hb : 0 < b) (hX : 0 ≤ X)
    (hbX : b * X ≤ 1) {n m : ℕ} (hn : n ∈ primeRange X) (hm : m ∈ primeRange X) (hnm : n ≠ m) :
    triangleFn b (Real.log n - Real.log m) = 0 := by
  have hn1 : 1 ≤ n := one_le_of_mem_primeRange hn
  have hm1 : 1 ≤ m := one_le_of_mem_primeRange hm
  have hnX : (n : ℝ) ≤ X := cast_le_of_mem_primeRange hX hn
  have hmX : (m : ℝ) ≤ X := cast_le_of_mem_primeRange hX hm
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · have hdiff : (1 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
      have : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hlt
      linarith
    have hbm : b * (m : ℝ) ≤ (m : ℝ) - (n : ℝ) :=
      (mul_le_mul_of_nonneg_left hmX hb.le).trans (hbX.trans hdiff)
    exact (triangleFn_eq_zero_of_sub_ge hb (by exact_mod_cast hn1)
      (by exact_mod_cast hlt.le) hbm).2
  · have hdiff : (1 : ℝ) ≤ (n : ℝ) - (m : ℝ) := by
      have : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hgt
      linarith
    have hbn : b * (n : ℝ) ≤ (n : ℝ) - (m : ℝ) :=
      (mul_le_mul_of_nonneg_left hnX hb.le).trans (hbX.trans hdiff)
    exact (triangleFn_eq_zero_of_sub_ge hb (by exact_mod_cast hm1)
      (by exact_mod_cast hgt.le) hbn).1

/-- **Upgrade of `FejerWeightedPrimeMeanSquare` below threshold (`b * X ≤ 1`):**
for `0 < b` and `b * X ≤ 1`, the Fejér-weighted prime double sum has zero off-diagonal terms and
equals the exact diagonal `Σ_{n ∈ primeRange X} Λ(n)² / n`. -/
theorem fejer_double_sum_eq_diag_of_le_inv_b {b X : ℝ} (hb : 0 < b) (hX : 0 ≤ X)
    (hbX : b * X ≤ 1) :
    (∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
        acoef n * acoef m * triangleFn b (Real.log n - Real.log m))
      = ∑ n ∈ primeRange X, (Λ n : ℝ) ^ 2 / n := by
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.sum_eq_single n]
  · have ht0 : triangleFn b 0 = 1 := by simp [triangleFn]
    rw [sub_self, ht0, mul_one, ← sq, acoef_sq]
  · intro m hm hmn
    rw [offDiag_triangleFn_eq_zero_of_le_inv_b hb hX hbX hn hm hmn.symm, mul_zero]
  · intro hnn; exact absurd hn hnn

/-- **`2`-adic parity doubling of the close-pair threshold (`b * X ≤ 2`):**
for `0 < b` and `b * X ≤ 2`, every pair of distinct odd integers `n, m ∈ primeRange X` has
`|n − m| ≥ 2`, and therefore `triangleFn b (log n − log m) = 0`. -/
theorem odd_offDiag_triangleFn_eq_zero_of_le_two_div_b {b X : ℝ} (hb : 0 < b) (hX : 0 ≤ X)
    (hbX : b * X ≤ 2) {n m : ℕ} (hn : n ∈ primeRange X) (hm : m ∈ primeRange X)
    (hn_odd : Odd n) (hm_odd : Odd m) (hnm : n ≠ m) :
    triangleFn b (Real.log n - Real.log m) = 0 := by
  have hn1 : 1 ≤ n := one_le_of_mem_primeRange hn
  have hm1 : 1 ≤ m := one_le_of_mem_primeRange hm
  have hnX : (n : ℝ) ≤ X := cast_le_of_mem_primeRange hX hn
  have hmX : (m : ℝ) ≤ X := cast_le_of_mem_primeRange hX hm
  obtain ⟨k, rfl⟩ := hn_odd
  obtain ⟨j, rfl⟩ := hm_odd
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · have h2 : (2 * k + 1) + 2 ≤ 2 * j + 1 := by omega
    have hdiff : (2 : ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) - ((2 * k + 1 : ℕ) : ℝ) := by
      have : ((2 * k + 1 : ℕ) : ℝ) + 2 ≤ ((2 * j + 1 : ℕ) : ℝ) := by exact_mod_cast h2
      linarith
    have hbm : b * ((2 * j + 1 : ℕ) : ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) - ((2 * k + 1 : ℕ) : ℝ) :=
      (mul_le_mul_of_nonneg_left hmX hb.le).trans (hbX.trans hdiff)
    exact (triangleFn_eq_zero_of_sub_ge hb (by exact_mod_cast hn1)
      (by exact_mod_cast hlt.le) hbm).2
  · have h2 : (2 * j + 1) + 2 ≤ 2 * k + 1 := by omega
    have hdiff : (2 : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) - ((2 * j + 1 : ℕ) : ℝ) := by
      have : ((2 * j + 1 : ℕ) : ℝ) + 2 ≤ ((2 * k + 1 : ℕ) : ℝ) := by exact_mod_cast h2
      linarith
    have hbn : b * ((2 * k + 1 : ℕ) : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) - ((2 * j + 1 : ℕ) : ℝ) :=
      (mul_le_mul_of_nonneg_left hnX hb.le).trans (hbX.trans hdiff)
    exact (triangleFn_eq_zero_of_sub_ge hb (by exact_mod_cast hm1)
      (by exact_mod_cast hgt.le) hbn).1

/-- **Exact vanishing of the odd-odd off-diagonal Fejér close-pair sum on `b * X ≤ 2`:**
on the entire trans-threshold collar `X ≤ 2/b`, all odd-odd off-diagonal terms in the Fejér
double sum vanish identically. -/
theorem odd_offDiag_fejer_sum_eq_zero_of_le_two_div_b {b X : ℝ} (hb : 0 < b) (hX : 0 ≤ X)
    (hbX : b * X ≤ 2) :
    (∑ n ∈ (primeRange X).filter Odd, ∑ m ∈ (primeRange X).filter Odd,
        if n = m then (0 : ℝ) else acoef n * acoef m * triangleFn b (Real.log n - Real.log m))
      = 0 := by
  refine Finset.sum_eq_zero fun n hn => Finset.sum_eq_zero fun m hm => ?_
  split_ifs with hnm
  · rfl
  · obtain ⟨hnP, hnO⟩ := Finset.mem_filter.mp hn
    obtain ⟨hmP, hmO⟩ := Finset.mem_filter.mp hm
    rw [odd_offDiag_triangleFn_eq_zero_of_le_two_div_b hb hX hbX hnP hmP hnO hmO hnm, mul_zero]

/-- **Downstream application to `JacksonWeightedPrimeFrobeniusDecomposition` (`4 * b * X ≤ 1`):**
whenever `4 * b * X ≤ 1` (`X ≤ 1/(4b)`), every off-diagonal pair `n ≠ m` in `primeRange X`
satisfies `jacksonCloseApprox b s₀ s₁ L d (log n) A (log m) A' = 0`. -/
theorem jacksonCloseApprox_offDiag_eq_zero_of_le_inv_four_b {b s₀ s₁ L X : ℝ} (hb : 0 < b)
    (h01 : s₀ ≤ s₁) (hX : 0 ≤ X) (hbX : 4 * b * X ≤ 1) (d : ℕ)
    {n m : ℕ} (hn : n ∈ primeRange X) (hm : m ∈ primeRange X) (hnm : n ≠ m)
    (A A' : ℤ → ℂ) :
    jacksonCloseApprox b s₀ s₁ L d (Real.log n) A (Real.log m) A' = 0 := by
  have hn1 : 1 ≤ n := one_le_of_mem_primeRange hn
  have hm1 : 1 ≤ m := one_le_of_mem_primeRange hm
  have hnX : (n : ℝ) ≤ X := cast_le_of_mem_primeRange hX hn
  have hmX : (m : ℝ) ≤ X := cast_le_of_mem_primeRange hX hm
  apply jacksonCloseApprox_eq_zero_of_le_abs hb h01 L d
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · have hdiff : (1 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
      have : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hlt
      linarith
    have hbm : 4 * b * (m : ℝ) ≤ (m : ℝ) - (n : ℝ) :=
      (mul_le_mul_of_nonneg_left hmX (by positivity)).trans (hbX.trans hdiff)
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hle := ((le_div_iff₀ hm0).mpr hbm).trans
      (log_sub_log_ge_sub_div (by exact_mod_cast hn1) (by exact_mod_cast hlt.le))
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    exact hle
  · have hdiff : (1 : ℝ) ≤ (n : ℝ) - (m : ℝ) := by
      have : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hgt
      linarith
    have hbn : 4 * b * (n : ℝ) ≤ (n : ℝ) - (m : ℝ) :=
      (mul_le_mul_of_nonneg_left hnX (by positivity)).trans (hbX.trans hdiff)
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hle := ((le_div_iff₀ hn0).mpr hbn).trans
      (log_sub_log_ge_sub_div (by exact_mod_cast hm1) (by exact_mod_cast hgt.le))
    rw [abs_of_nonneg (by linarith)]
    exact hle

/-- **Downstream `2`-adic parity doubling for `jacksonPairKernel` (`2 * b * X ≤ 1`):**
for `0 < b` and `2 * b * X ≤ 1` (`X ≤ 1/(2b)`), every pair of distinct odd integers
`n, m ∈ primeRange X` satisfies `jacksonPairKernel b s₀ s₁ L r (log n − log m) = 0`. -/
theorem jacksonPairKernel_odd_offDiag_eq_zero_of_le_inv_two_b {b s₀ s₁ L X : ℝ} (hb : 0 < b)
    (h01 : s₀ ≤ s₁) (hX : 0 ≤ X) (hbX : 2 * b * X ≤ 1) (r : ℤ)
    {n m : ℕ} (hn : n ∈ primeRange X) (hm : m ∈ primeRange X)
    (hn_odd : Odd n) (hm_odd : Odd m) (hnm : n ≠ m) :
    jacksonPairKernel b s₀ s₁ L r (Real.log n - Real.log m) = 0 := by
  have hn1 : 1 ≤ n := one_le_of_mem_primeRange hn
  have hm1 : 1 ≤ m := one_le_of_mem_primeRange hm
  have hnX : (n : ℝ) ≤ X := cast_le_of_mem_primeRange hX hn
  have hmX : (m : ℝ) ≤ X := cast_le_of_mem_primeRange hX hm
  obtain ⟨k, rfl⟩ := hn_odd
  obtain ⟨j, rfl⟩ := hm_odd
  apply jacksonPairKernel_eq_zero_of_le_abs hb h01 L r
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · have h2 : (2 * k + 1) + 2 ≤ 2 * j + 1 := by omega
    have hdiff : (2 : ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) - ((2 * k + 1 : ℕ) : ℝ) := by
      have : ((2 * k + 1 : ℕ) : ℝ) + 2 ≤ ((2 * j + 1 : ℕ) : ℝ) := by exact_mod_cast h2
      linarith
    have hbm : 4 * b * ((2 * j + 1 : ℕ) : ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) - ((2 * k + 1 : ℕ) : ℝ) := by
      have : 4 * b * ((2 * j + 1 : ℕ) : ℝ) ≤ 2 * (2 * b * X) := by
        calc 4 * b * ((2 * j + 1 : ℕ) : ℝ) ≤ 4 * b * X :=
              mul_le_mul_of_nonneg_left hmX (by positivity)
          _ = 2 * (2 * b * X) := by ring
      linarith
    have hm0 : (0 : ℝ) < ((2 * j + 1 : ℕ) : ℝ) := by exact_mod_cast hm1
    have hle := ((le_div_iff₀ hm0).mpr hbm).trans
      (log_sub_log_ge_sub_div (by exact_mod_cast hn1) (by exact_mod_cast hlt.le))
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    exact hle
  · have h2 : (2 * j + 1) + 2 ≤ 2 * k + 1 := by omega
    have hdiff : (2 : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) - ((2 * j + 1 : ℕ) : ℝ) := by
      have : ((2 * j + 1 : ℕ) : ℝ) + 2 ≤ ((2 * k + 1 : ℕ) : ℝ) := by exact_mod_cast h2
      linarith
    have hbn : 4 * b * ((2 * k + 1 : ℕ) : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) - ((2 * j + 1 : ℕ) : ℝ) := by
      have : 4 * b * ((2 * k + 1 : ℕ) : ℝ) ≤ 2 * (2 * b * X) := by
        calc 4 * b * ((2 * k + 1 : ℕ) : ℝ) ≤ 4 * b * X :=
              mul_le_mul_of_nonneg_left hnX (by positivity)
          _ = 2 * (2 * b * X) := by ring
      linarith
    have hn0 : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by exact_mod_cast hn1
    have hle := ((le_div_iff₀ hn0).mpr hbn).trans
      (log_sub_log_ge_sub_div (by exact_mod_cast hm1) (by exact_mod_cast hgt.le))
    rw [abs_of_nonneg (by linarith)]
    exact hle

/-! ## 3. Trans-Threshold Strip Confinement and 2D Selberg Sieve Bound on Close Prime Pairs -/

/-- **Trans-threshold strip confinement of close pairs:**
for `0 < b` and `1 ≤ m < n ≤ X`, if `triangleFn b (log n − log m) ≠ 0`, then `n` lies strictly
above the threshold `1 / b` and the additive shift `n − m` satisfies `1 ≤ n − m < b * n ≤ b * X`. -/
theorem offDiag_triangleFn_support_strip {b X : ℝ} (hb : 0 < b) (hX : 0 ≤ X)
    {m n : ℕ} (hm : m ∈ primeRange X) (hn : n ∈ primeRange X) (hmn : m < n)
    (hker : triangleFn b (Real.log n - Real.log m) ≠ 0) :
    1 / b < (n : ℝ) ∧ 1 ≤ n - m ∧ ((n - m : ℕ) : ℝ) < b * (n : ℝ) ∧ b * (n : ℝ) ≤ b * X := by
  have hm1 : 1 ≤ m := one_le_of_mem_primeRange hm
  have hnX : (n : ℝ) ≤ X := cast_le_of_mem_primeRange hX hn
  have hlt : ((n - m : ℕ) : ℝ) < b * (n : ℝ) := by
    by_contra hge
    have hge' : b * (n : ℝ) ≤ (n : ℝ) - (m : ℝ) := by
      have : b * (n : ℝ) ≤ ((n - m : ℕ) : ℝ) := not_lt.mp hge
      rwa [Nat.cast_sub hmn.le] at this
    exact hker (triangleFn_eq_zero_of_sub_ge hb (by exact_mod_cast hm1)
      (by exact_mod_cast hmn.le) hge').1
  have h1le : 1 ≤ n - m := Nat.le_sub_of_add_le' hmn
  have h1cast : (1 : ℝ) ≤ ((n - m : ℕ) : ℝ) := by exact_mod_cast h1le
  have hinv : 1 / b < (n : ℝ) := by
    rw [div_lt_iff₀ hb, mul_comm]
    linarith
  exact ⟨hinv, h1le, hlt, mul_le_mul_of_nonneg_left hnX hb.le⟩

/-- **Unconditional 2D Selberg sieve bound on weighted close prime pairs in a narrow strip:**
for any nonnegative per-pair weight upper bound `W ≥ 0`, the weighted sum of shifted prime pairs
`(m, m + d)` over shifts `1 ≤ d ≤ K` and primes `m ≤ Y` with `m > h` (`2 ≤ P₁ ≤ h`) is bounded
unconditionally by `W * (2 e K Y / exp(mertensS h − mertensS P₁)² + K * remainder(h, z))`. -/
theorem sieved_closePrimePair_strip_bound (Y : ℝ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) {h : ℕ} (K : ℕ)
    {z W : ℝ} (hz : 1 ≤ z) (hY : 0 ≤ Y) (hh2 : 2 ≤ h) (hP₁h : P₁ ≤ h)
    (hlev : ((h : ℝ)) ^ (18 : ℝ) ≤ Real.sqrt z)
    (hlog : 20 * mertensFirstConst ≤ Real.log h) (hW : 0 ≤ W) :
    (∑ d ∈ Finset.Icc 1 K,
        W * ((((Finset.Icc 1 ⌊Y⌋₊).filter
          (fun m => m.Prime ∧ (m + d).Prime ∧ h < m)).card : ℕ) : ℝ))
      ≤ W * (2 * Real.exp 1 * (K : ℝ) * Y / (Real.exp (mertensS h - mertensS P₁)) ^ (2 : ℕ)
          + (K : ℝ) * ∑ e ∈ (rangePrimorial P₁ h).divisors,
              (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0)) := by
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (sum_card_primePair_le_sharp Y hP₁ K hz hY hh2 hP₁h hlev hlog) hW

end GaloisForLFunctions.TransThresholdPairCorrelation
