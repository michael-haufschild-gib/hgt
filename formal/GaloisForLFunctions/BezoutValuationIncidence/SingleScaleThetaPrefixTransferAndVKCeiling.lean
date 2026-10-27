import GaloisForLFunctions.BezoutValuationIncidence.UnconditionalEscapedMoebiusDecayAndCrossRouteBridge
import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.IntegerThetaPrefixesReadTheDefectWithoutLoss
import GaloisForLFunctions.ArithmeticElectrostatics.TheHeckeDefectIsTheMomentOfInertia
import GaloisForLFunctions.SquareRootThreshold.ZetaLagFamilyVinogradovKorobovEnvelope

/-!
# Quantitative Single-Scale Integer Theta Prefix Transfer and Vinogradov–Korobov Sub-Trivial Ceiling

This module establishes quantitative single-scale bounds and equivalences for the integer theta
prefix readings across `RenormalizedBiarithmeticGeometry`, `ConjugateDiagonalGeometry`,
`ArithmeticElectrostatics`, `SquareRootThreshold`, and `BezoutValuationIncidence`:

1. **All-`n` Quantitative Lossless Prefix-to-Defect and Moment-of-Inertia Transfer
   (`exists_explicit_reading_transfer_constants`, `heckeDefect_le_of_explicit_reading`,
   `depthSecondMoment_le_of_explicit_reading`):**
   Replaces the existential `∃ N(f, ε)` threshold in `RBG.heckeDefect_le_of_readings` with an
   explicit finite-`n` error envelope `thetaPrefixError B D n` valid for **every** `n ≥ 1` and
   every `2^k |L| ≤ 2 log(n + 1)` (`CDG.exists_finiteThetaSource_logarithmic_error_bound`), and
   couples `AES.moment_le_heckeDefect` to bound the electrostatic transverse moment of inertia
   `4 L² M_f = 4 L² depthSecondMoment f ≤ reading f L 1 n + thetaPrefixError B₁ D₁ n` from a single
   finite integer-theta prefix reading.

2. **Single-Scale Logarithmic-Horizon Integer-Prefix Equivalence for `zetaZeroAbscissa ≤ 1 - θ`,
   `GrowingEndpointEscapedMoebiusLaw θ`, and `RiemannHypothesis`
   (`zetaZeroAbscissa_le_iff_singleScale_reading_rate`,
   `growingEndpointEscapedMoebiusLaw_iff_singleScale_reading_rate`,
   `riemannHypothesis_iff_singleScale_reading_subpoly`):**
   At the canonical minimal admissible dyadic prefix schedule `dyadicThetaPrefix k := ⌊exp(2^k/2)⌋₊ + 1`
   (where `2^k ≤ 2 log(dyadicThetaPrefix k + 1)` holds for **every** `k : ℕ`), proves that for every
   `0 < θ ≤ 1 / 2`:
   `zetaZeroAbscissa ≤ 1 - θ ↔ ∀ f ε > 0, ∃ C, ∀ k, reading f (2^k) 1 (dyadicThetaPrefix k) ≤ C * (dyadicThetaPrefix k + 1)^{2(1 - 2θ) + ε}`,
   and at the endpoint `θ = 1 / 2`:
   `RiemannHypothesis ↔ ∀ f ε > 0, ∃ C, ∀ k, reading f (2^k) 1 (dyadicThetaPrefix k) ≤ C * (dyadicThetaPrefix k + 1)^ε`.

3. **Unconditional Vinogradov–Korobov Sub-Trivial Single-Scale Prefix Ceiling
   (`exists_vk_carrier_depth_profile`, `exists_reading_logHorizon_vk_ceiling`,
   `tendsto_reading_logHorizon_div_sq_zero`):**
   Establishes the first unconditional sub-trivial single-scale upper bound on `RBG.reading f L 1 n`
   across the full logarithmic horizon `|L| ≤ 2 log(n + 1)`, beating the trivial strip ceiling
   `mass f · (n + 1)²` with unit leading constant by the Vinogradov–Korobov factor
   `exp(-4 δ_VK(n + 2) log(n + 1))` plus vanishing `O_f((log n)/n)` prefix/tail errors, and proving
   unconditionally that `reading f (L n) 1 n / (n + 1)² → 0` for every `f : CompactTest` and every
   `|L n| ≤ 2 log(n + 1)` (in particular `L n = 2 log(n + 1)`).
-/

open MeasureTheory Real Set Finset Filter Topology Complex
open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.BezoutValuationIncidence

open Zeta23 _root_.RHTower
open GaloisForLFunctions.ArithmeticPolarization
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open GaloisForLFunctions.SelectivePositivityAndThresholdLaws
open GaloisForLFunctions.ConjugateDiagonalGeometry
open GaloisForLFunctions.RenormalizedBiarithmeticGeometry
open GaloisForLFunctions.ArithmeticElectrostatics
open GaloisForLFunctions.SquareRootThreshold

/-! ## §1. All-`n` Quantitative Prefix Error Envelope, Lossless Transfer, and `AES` Moment Bound -/

/-- Explicit finite-`n` integer-theta prefix error envelope from `CDG.FiniteThetaMetric`. -/
def thetaPrefixError (B D : ℝ) (n : ℕ) : ℝ :=
  B * Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62) +
    D * ((16 / (n : ℝ)) * (xiLineTwoLogDerivConstant + Real.log ((n : ℝ) + 4)))

/-- Uniform all-`n ≥ 1` ceiling on `thetaPrefixError B D n` for nonnegative `B, D ≥ 0`. -/
theorem thetaPrefixError_le_const {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D) {n : ℕ} (hn : 1 ≤ n) :
    thetaPrefixError B D n ≤
      B * Real.exp 846 + D * (16 * |xiLineTwoLogDerivConstant| + 80) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hexp : Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62) ≤ Real.exp 846 := by
    apply Real.exp_le_exp.mpr
    have hsq : 0 ≤ ((n : ℝ) ^ 2 - 28) ^ 2 := sq_nonneg _
    nlinarith
  have hlog : Real.log ((n : ℝ) + 4) ≤ 5 * (n : ℝ) := by
    have h1 : Real.log ((n : ℝ) + 4) ≤ (n : ℝ) + 3 := by
      have := Real.log_le_sub_one_of_pos (by linarith : 0 < (n : ℝ) + 4)
      linarith
    linarith
  have htail : (16 / (n : ℝ)) * (xiLineTwoLogDerivConstant + Real.log ((n : ℝ) + 4)) ≤
      16 * |xiLineTwoLogDerivConstant| + 80 := by
    have hdiv_le : 16 / (n : ℝ) ≤ 16 := div_le_self (by norm_num) hn1
    have hc_le : xiLineTwoLogDerivConstant ≤ |xiLineTwoLogDerivConstant| := le_abs_self _
    calc (16 / (n : ℝ)) * (xiLineTwoLogDerivConstant + Real.log ((n : ℝ) + 4))
        ≤ (16 / (n : ℝ)) * (|xiLineTwoLogDerivConstant| + 5 * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = (16 / (n : ℝ)) * |xiLineTwoLogDerivConstant| + 80 := by field_simp [hn0.ne']; ring
      _ ≤ 16 * |xiLineTwoLogDerivConstant| + 80 := by
          nlinarith [abs_nonneg xiLineTwoLogDerivConstant]
  unfold thetaPrefixError
  exact add_le_add (mul_le_mul_of_nonneg_left hexp hB) (mul_le_mul_of_nonneg_left htail hD)

/-- `thetaPrefixError B D n → 0` as `n → ∞`. -/
theorem tendsto_thetaPrefixError_zero (B D : ℝ) :
    Tendsto (thetaPrefixError B D) atTop (𝓝 0) := by
  have ht1 : Tendsto (fun n : ℕ => B * Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62))
      atTop (𝓝 0) :=
    tendsto_explicitWindowError B
  have hinv : Tendsto (fun n : ℕ => 16 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlog_div : Tendsto (fun n : ℕ => (16 / (n : ℝ)) * Real.log ((n : ℝ) + 4)) atTop (𝓝 0) := by
    have hsqrt_atTop : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop := by
      rw [Filter.tendsto_atTop]
      intro b
      refine (eventually_ge_atTop ⌈max b 0 ^ 2⌉₊).mono fun n hn => ?_
      have h1 : max b 0 ^ 2 ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
      exact (le_max_left b 0).trans (Real.le_sqrt_of_sq_le h1)
    refine squeeze_zero_norm' ?_
      (by simpa using (tendsto_inv_atTop_zero.comp hsqrt_atTop).const_mul (32 * Real.sqrt 2))
    filter_upwards [eventually_ge_atTop 4] with n hn
    have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
    have hn_pos : (0 : ℝ) < n := by linarith
    have hlog_pos : 0 ≤ Real.log ((n : ℝ) + 4) := Real.log_nonneg (by linarith)
    rw [Real.norm_of_nonneg (by positivity)]
    have hsqrt_pos : 0 < Real.sqrt ((n : ℝ) + 4) := Real.sqrt_pos.mpr (by linarith)
    have hlog_le : Real.log ((n : ℝ) + 4) ≤ 2 * Real.sqrt ((n : ℝ) + 4) := by
      have hsq : Real.sqrt ((n : ℝ) + 4) ^ 2 = (n : ℝ) + 4 := Real.sq_sqrt (by linarith)
      have hl : Real.log ((n : ℝ) + 4) = 2 * Real.log (Real.sqrt ((n : ℝ) + 4)) := by
        rw [← hsq, Real.log_pow]; norm_num
      have hexp := Real.log_le_sub_one_of_pos hsqrt_pos
      linarith
    have h2n : Real.sqrt ((n : ℝ) + 4) ≤ Real.sqrt 2 * Real.sqrt (n : ℝ) := by
      rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      exact Real.sqrt_le_sqrt (by linarith)
    have hsn : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn_pos.le
    have hsn_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
    calc (16 / (n : ℝ)) * Real.log ((n : ℝ) + 4)
        ≤ (16 / (n : ℝ)) * (2 * (Real.sqrt 2 * Real.sqrt (n : ℝ))) :=
          mul_le_mul_of_nonneg_left (hlog_le.trans (by linarith)) (by positivity)
      _ = 32 * Real.sqrt 2 * (Real.sqrt (n : ℝ))⁻¹ := by
          rw [← hsn]; field_simp [hsn_pos.ne']; ring
  have ht2 : Tendsto (fun n : ℕ =>
      D * ((16 / (n : ℝ)) * (xiLineTwoLogDerivConstant + Real.log ((n : ℝ) + 4)))) atTop (𝓝 0) := by
    have hsum := ((hinv.mul_const xiLineTwoLogDerivConstant).add hlog_div).const_mul D
    simpa [mul_add] using hsum
  have hadd := ht1.add ht2
  rw [add_zero] at hadd
  exact hadd

/-- **Quantitative All-`n` Prefix Error Certificate for `reading` (`j = 1` and `j = 0`):**
For every `f : CompactTest`, there exist `B₁, D₁, B₀, D₀ ≥ 0` such that for every `n ≥ 1`:
* `|reading f L 1 n - heckeDefect f L| ≤ thetaPrefixError B₁ D₁ n` for all `|L| ≤ 2 log(n + 1)`;
* `|reading f 0 0 n - mass f| ≤ thetaPrefixError B₀ D₀ n`. -/
theorem exists_explicit_reading_transfer_constants (f : CompactTest) :
    ∃ B₁ D₁ B₀ D₀ : ℝ, 0 ≤ B₁ ∧ 0 ≤ D₁ ∧ 0 ≤ B₀ ∧ 0 ≤ D₀ ∧
      (∀ n : ℕ, 1 ≤ n → ∀ L : ℝ, |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
        |reading f L 1 n - heckeDefect f L| ≤ thetaPrefixError B₁ D₁ n) ∧
      (∀ n : ℕ, 1 ≤ n → |reading f 0 0 n - mass f| ≤ thetaPrefixError B₀ D₀ n) := by
  obtain ⟨B₁, D₁, hB₁, hD₁, hb₁⟩ := exists_finiteThetaSource_logarithmic_error_bound f 1
  obtain ⟨B₀, D₀, hB₀, hD₀, hb₀⟩ := exists_finiteThetaSource_logarithmic_error_bound f 0
  refine ⟨B₁, D₁, B₀, D₀, hB₁, hD₁, hB₀, hD₀, fun n hn L hL => ?_, fun n hn => ?_⟩
  · have h := hb₁ n hn L 0 (by simp; positivity) (by simpa using hL)
    rw [sourceTwist_zero] at h
    simpa [reading, heckeDefect, pow_one, thetaPrefixError] using h
  · have hlog : 0 ≤ 2 * Real.log ((n : ℝ) + 1) :=
      mul_nonneg (by norm_num) (Real.log_nonneg (by linarith [n.cast_nonneg (α := ℝ)]))
    have h := hb₀ n hn 0 0 (by simp; positivity) (by simp [hlog])
    rw [sourceTwist_zero] at h
    unfold reading mass thetaPrefixError
    simpa only [pow_zero, mul_one, zetaWeight, collidedForm] using h

/-- **Quantitative Lossless Finite-Prefix-to-Defect Transfer (`heckeDefect_le_of_explicit_reading`):**
Given the explicit prefix error constants `(B₁, D₁, B₀, D₀)` of `f`, a single integer-prefix check
at **any** `n ≥ 1` and dyadic scale `2^k |L| ≤ 2 log(n + 1)` transfers losslessly to
`heckeDefect f L ≤ mass f * (2 * cosh φ - 2)`. -/
theorem heckeDefect_le_of_explicit_reading (f : CompactTest) {B₁ D₁ B₀ D₀ : ℝ}
    (herr₁ : ∀ n : ℕ, 1 ≤ n → ∀ L : ℝ, |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
      |reading f L 1 n - heckeDefect f L| ≤ thetaPrefixError B₁ D₁ n)
    (herr₀ : ∀ n : ℕ, 1 ≤ n → |reading f 0 0 n - mass f| ≤ thetaPrefixError B₀ D₀ n)
    {n k : ℕ} (hn : 1 ≤ n) {L φ : ℝ}
    (hL : (2 : ℝ) ^ k * |L| ≤ 2 * Real.log ((n : ℝ) + 1))
    (hread : reading f ((2 : ℝ) ^ k * L) 1 n + thetaPrefixError B₁ D₁ n ≤
      (reading f 0 0 n - thetaPrefixError B₀ D₀ n) * (2 * Real.cosh ((2 : ℝ) ^ k * φ) - 2)) :
    heckeDefect f L ≤ mass f * (2 * Real.cosh φ - 2) := by
  have hE := herr₁ n hn ((2 : ℝ) ^ k * L) (by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ k)]; exact hL)
  have hM := herr₀ n hn
  have hc : 0 ≤ 2 * Real.cosh ((2 : ℝ) ^ k * φ) - 2 := two_mul_cosh_sub_two_nonneg _
  have hM_le : reading f 0 0 n - thetaPrefixError B₀ D₀ n ≤ mass f := by
    linarith [(abs_le.mp hM).2]
  apply heckeDefect_le_of_dyadic_le f L φ k
  calc heckeDefect f ((2 : ℝ) ^ k * L)
      ≤ reading f ((2 : ℝ) ^ k * L) 1 n + thetaPrefixError B₁ D₁ n := by
        linarith [(abs_le.mp hE).1]
    _ ≤ (reading f 0 0 n - thetaPrefixError B₀ D₀ n) * (2 * Real.cosh ((2 : ℝ) ^ k * φ) - 2) := hread
    _ ≤ mass f * (2 * Real.cosh ((2 : ℝ) ^ k * φ) - 2) := mul_le_mul_of_nonneg_right hM_le hc

/-- **Electrostatic Transverse Moment-of-Inertia Prefix Bound (`AES` × `RBG` Bridge):**
Coupling `AES.moment_le_heckeDefect` (`4 L² M_f ≤ E_f(L)`) with `herr₁` bounds the transverse
moment of inertia `depthSecondMoment f` directly from a single integer-theta prefix reading at any
admissible scale `|L| ≤ 2 log(n + 1)`. -/
theorem depthSecondMoment_le_of_explicit_reading (f : CompactTest) {B₁ D₁ : ℝ}
    (herr₁ : ∀ n : ℕ, 1 ≤ n → ∀ L : ℝ, |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
      |reading f L 1 n - heckeDefect f L| ≤ thetaPrefixError B₁ D₁ n)
    {n : ℕ} (hn : 1 ≤ n) {L : ℝ} (hL : |L| ≤ 2 * Real.log ((n : ℝ) + 1)) :
    4 * L ^ 2 * depthSecondMoment f ≤ reading f L 1 n + thetaPrefixError B₁ D₁ n := by
  have h1 := moment_le_heckeDefect f L
  have h2 := (abs_le.mp (herr₁ n hn L hL)).1
  linarith

/-! ## §2. Single-Scale Logarithmic-Horizon Integer-Prefix Equivalence for `Θ ≤ 1 - θ` and `RH` -/

/-- Canonical minimal admissible prefix length at dyadic scale `2^k`:
`dyadicThetaPrefix k = ⌊exp(2^k / 2)⌋₊ + 1`. -/
def dyadicThetaPrefix (k : ℕ) : ℕ :=
  ⌊Real.exp ((2 : ℝ) ^ k / 2)⌋₊ + 1

/-- Fundamental horizon and quadratic-exponential sandwich for `dyadicThetaPrefix k`:
* `1 ≤ dyadicThetaPrefix k`;
* `2^k ≤ 2 * log(dyadicThetaPrefix k + 1)` (admissible in `CDG`/`RBG` for **every** `k : ℕ`);
* `exp(2^k) ≤ (dyadicThetaPrefix k + 1)² ≤ 9 * exp(2^k)`. -/
theorem dyadicThetaPrefix_properties (k : ℕ) :
    1 ≤ dyadicThetaPrefix k ∧
    (2 : ℝ) ^ k ≤ 2 * Real.log ((dyadicThetaPrefix k : ℝ) + 1) ∧
    Real.exp ((2 : ℝ) ^ k) ≤ ((dyadicThetaPrefix k : ℝ) + 1) ^ 2 ∧
    ((dyadicThetaPrefix k : ℝ) + 1) ^ 2 ≤ 9 * Real.exp ((2 : ℝ) ^ k) := by
  have hexp_pos : 0 < Real.exp ((2 : ℝ) ^ k / 2) := Real.exp_pos _
  have hexp_ge1 : 1 ≤ Real.exp ((2 : ℝ) ^ k / 2) := Real.one_le_exp (by positivity)
  have hlt : Real.exp ((2 : ℝ) ^ k / 2) < (dyadicThetaPrefix k : ℝ) := by
    dsimp [dyadicThetaPrefix]
    push_cast
    exact Nat.lt_floor_add_one _
  have hle : (dyadicThetaPrefix k : ℝ) + 1 ≤ 3 * Real.exp ((2 : ℝ) ^ k / 2) := by
    dsimp [dyadicThetaPrefix]
    push_cast
    have hf : (⌊Real.exp ((2 : ℝ) ^ k / 2)⌋₊ : ℝ) ≤ Real.exp ((2 : ℝ) ^ k / 2) :=
      Nat.floor_le hexp_pos.le
    linarith
  have h1_lt : Real.exp ((2 : ℝ) ^ k / 2) ≤ (dyadicThetaPrefix k : ℝ) + 1 := by linarith
  have hlog : (2 : ℝ) ^ k ≤ 2 * Real.log ((dyadicThetaPrefix k : ℝ) + 1) := by
    have hl := Real.log_le_log hexp_pos h1_lt
    rw [Real.log_exp] at hl
    linarith
  have hexp_sq : Real.exp ((2 : ℝ) ^ k / 2) ^ 2 = Real.exp ((2 : ℝ) ^ k) := by
    rw [sq, ← Real.exp_add]
    congr 1; ring
  refine ⟨by unfold dyadicThetaPrefix; omega, hlog, ?_, ?_⟩
  · rw [← hexp_sq]
    exact pow_le_pow_left₀ hexp_pos.le h1_lt 2
  · calc ((dyadicThetaPrefix k : ℝ) + 1) ^ 2
        ≤ (3 * Real.exp ((2 : ℝ) ^ k / 2)) ^ 2 :=
          pow_le_pow_left₀ (by linarith) hle 2
      _ = 9 * Real.exp ((2 : ℝ) ^ k / 2) ^ 2 := by ring
      _ = 9 * Real.exp ((2 : ℝ) ^ k) := by rw [hexp_sq]

/-- **Single-Scale Logarithmic-Horizon Integer-Prefix Equivalence:**
For every `0 < θ ≤ 1 / 2`, `zetaZeroAbscissa ≤ 1 - θ` holds if and only if for every
`f : CompactTest` and every `ε > 0`, the single-scale integer-theta prefix readings along
`dyadicThetaPrefix k` grow at most like `(dyadicThetaPrefix k + 1)^{2(1 - 2θ) + ε}`. -/
theorem zetaZeroAbscissa_le_iff_singleScale_reading_rate {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ ≤ 1 / 2) :
    zetaZeroAbscissa ≤ 1 - θ ↔
      ∀ (f : CompactTest) (ε : ℝ), 0 < ε → ∃ C : ℝ, ∀ k : ℕ,
        reading f ((2 : ℝ) ^ k) 1 (dyadicThetaPrefix k) ≤
          C * ((dyadicThetaPrefix k : ℝ) + 1) ^ (2 * (1 - 2 * θ) + ε) := by
  have h35 : zetaZeroAbscissa ≤ 1 - θ ↔
      ∀ (f : CompactTest) (ε : ℝ), 0 < ε → ∃ C : ℝ, ∀ k : ℕ,
        heckeDefect f (2 ^ k) ≤ C * Real.exp ((1 - 2 * θ + ε) * 2 ^ k) :=
    (escapedMoebius_rbg_seven_way_tfae hθ0 hθ2).out 3 5
  rw [h35]
  constructor
  · intro hdef f ε hε
    obtain ⟨C₁, hC₁⟩ := hdef f (ε / 2) (half_pos hε)
    obtain ⟨B₁, D₁, _, _, hB₁, hD₁, _, _, herr₁, -⟩ := exists_explicit_reading_transfer_constants f
    set Emax : ℝ := B₁ * Real.exp 846 + D₁ * (16 * |xiLineTwoLogDerivConstant| + 80)
    have hEmax0 : 0 ≤ Emax := by
      dsimp [Emax]; exact add_nonneg (by positivity) (mul_nonneg hD₁ (by positivity))
    refine ⟨|C₁| + Emax, fun k => ?_⟩
    obtain ⟨hk1, hklog, hk_lo, -⟩ := dyadicThetaPrefix_properties k
    have habs_L : |(2 : ℝ) ^ k| ≤ 2 * Real.log ((dyadicThetaPrefix k : ℝ) + 1) := by
      rwa [abs_of_pos (by positivity : (0 : ℝ) < 2 ^ k)]
    have hdiff := (abs_le.mp (herr₁ (dyadicThetaPrefix k) hk1 ((2 : ℝ) ^ k) habs_L)).2
    have herr_bd := thetaPrefixError_le_const hB₁ hD₁ hk1
    have hexp_pos : 0 < Real.exp ((1 - 2 * θ + ε / 2) * (2 : ℝ) ^ k) := Real.exp_pos _
    have hdef_k : heckeDefect f ((2 : ℝ) ^ k) ≤
        |C₁| * Real.exp ((1 - 2 * θ + ε / 2) * (2 : ℝ) ^ k) :=
      (hC₁ k).trans (mul_le_mul_of_nonneg_right (le_abs_self C₁) hexp_pos.le)
    set p : ℝ := 1 - 2 * θ + ε / 2
    have hp_pos : 0 < p := by dsimp [p]; linarith
    have hp2 : 2 * p = 2 * (1 - 2 * θ) + ε := by dsimp [p]; ring
    have hn_ge1 : 1 ≤ (dyadicThetaPrefix k : ℝ) + 1 := by
      have : (1 : ℝ) ≤ dyadicThetaPrefix k := by exact_mod_cast hk1
      linarith
    have hrpow_ge1 : 1 ≤ ((dyadicThetaPrefix k : ℝ) + 1) ^ (2 * (1 - 2 * θ) + ε) :=
      Real.one_le_rpow hn_ge1 (by linarith)
    have hexp_le_rpow : Real.exp (p * (2 : ℝ) ^ k) ≤
        ((dyadicThetaPrefix k : ℝ) + 1) ^ (2 * (1 - 2 * θ) + ε) := by
      have h1 : Real.exp (p * (2 : ℝ) ^ k) = (Real.exp ((2 : ℝ) ^ k)) ^ p := by
        rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm]
      have h2 : (((dyadicThetaPrefix k : ℝ) + 1) ^ (2 : ℕ)) ^ p =
          ((dyadicThetaPrefix k : ℝ) + 1) ^ (2 * (1 - 2 * θ) + ε) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), Nat.cast_two, hp2]
      rw [h1, ← h2]
      exact Real.rpow_le_rpow (Real.exp_pos _).le hk_lo hp_pos.le
    calc reading f ((2 : ℝ) ^ k) 1 (dyadicThetaPrefix k)
        ≤ heckeDefect f ((2 : ℝ) ^ k) + Emax := by linarith
      _ ≤ |C₁| * Real.exp (p * (2 : ℝ) ^ k) + Emax := by linarith
      _ ≤ |C₁| * ((dyadicThetaPrefix k : ℝ) + 1) ^ (2 * (1 - 2 * θ) + ε) +
            Emax * ((dyadicThetaPrefix k : ℝ) + 1) ^ (2 * (1 - 2 * θ) + ε) :=
          add_le_add (mul_le_mul_of_nonneg_left hexp_le_rpow (abs_nonneg C₁))
            (le_mul_of_one_le_right hEmax0 hrpow_ge1)
      _ = (|C₁| + Emax) * ((dyadicThetaPrefix k : ℝ) + 1) ^ (2 * (1 - 2 * θ) + ε) := by ring
  · intro hread f ε hε
    obtain ⟨C₁, hC₁⟩ := hread f ε hε
    obtain ⟨B₁, D₁, _, _, hB₁, hD₁, _, _, herr₁, -⟩ := exists_explicit_reading_transfer_constants f
    set Emax : ℝ := B₁ * Real.exp 846 + D₁ * (16 * |xiLineTwoLogDerivConstant| + 80)
    have hEmax0 : 0 ≤ Emax := by
      dsimp [Emax]; exact add_nonneg (by positivity) (mul_nonneg hD₁ (by positivity))
    set q : ℝ := 2 * (1 - 2 * θ) + ε
    have hq_pos : 0 < q := by dsimp [q]; linarith
    refine ⟨|C₁| * (9 : ℝ) ^ (q / 2) + Emax, fun k => ?_⟩
    obtain ⟨hk1, hklog, _, hk_hi⟩ := dyadicThetaPrefix_properties k
    have habs_L : |(2 : ℝ) ^ k| ≤ 2 * Real.log ((dyadicThetaPrefix k : ℝ) + 1) := by
      rwa [abs_of_pos (by positivity : (0 : ℝ) < 2 ^ k)]
    have hdiff := (abs_le.mp (herr₁ (dyadicThetaPrefix k) hk1 ((2 : ℝ) ^ k) habs_L)).1
    have herr_bd := thetaPrefixError_le_const hB₁ hD₁ hk1
    have hn_pos : 0 < (dyadicThetaPrefix k : ℝ) + 1 := by positivity
    have hrpow_pos : 0 ≤ ((dyadicThetaPrefix k : ℝ) + 1) ^ q := Real.rpow_nonneg hn_pos.le q
    have hread_k : reading f ((2 : ℝ) ^ k) 1 (dyadicThetaPrefix k) ≤
        |C₁| * ((dyadicThetaPrefix k : ℝ) + 1) ^ q :=
      (hC₁ k).trans (mul_le_mul_of_nonneg_right (le_abs_self C₁) hrpow_pos)
    have hrpow_le_exp : ((dyadicThetaPrefix k : ℝ) + 1) ^ q ≤
        (9 : ℝ) ^ (q / 2) * Real.exp ((1 - 2 * θ + ε) * (2 : ℝ) ^ k) := by
      have hsq_eq : ((dyadicThetaPrefix k : ℝ) + 1) ^ q =
          (((dyadicThetaPrefix k : ℝ) + 1) ^ (2 : ℕ)) ^ (q / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le, Nat.cast_two]
        congr 1; ring
      have hmul_rpow : (9 * Real.exp ((2 : ℝ) ^ k)) ^ (q / 2) =
          (9 : ℝ) ^ (q / 2) * Real.exp ((q / 2) * (2 : ℝ) ^ k) := by
        rw [Real.mul_rpow (by norm_num) (Real.exp_pos _).le,
          Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm]
      have hexp_le : Real.exp ((q / 2) * (2 : ℝ) ^ k) ≤
          Real.exp ((1 - 2 * θ + ε) * (2 : ℝ) ^ k) := by
        apply Real.exp_le_exp.mpr
        dsimp [q]
        have hk0 : (0 : ℝ) < 2 ^ k := by positivity
        nlinarith
      calc ((dyadicThetaPrefix k : ℝ) + 1) ^ q
          ≤ (9 * Real.exp ((2 : ℝ) ^ k)) ^ (q / 2) := by
            rw [hsq_eq]
            exact Real.rpow_le_rpow (by positivity) hk_hi (by positivity)
        _ = (9 : ℝ) ^ (q / 2) * Real.exp ((q / 2) * (2 : ℝ) ^ k) := hmul_rpow
        _ ≤ (9 : ℝ) ^ (q / 2) * Real.exp ((1 - 2 * θ + ε) * (2 : ℝ) ^ k) :=
            mul_le_mul_of_nonneg_left hexp_le (Real.rpow_nonneg (by norm_num) _)
    have hexp_ge1 : 1 ≤ Real.exp ((1 - 2 * θ + ε) * (2 : ℝ) ^ k) :=
      Real.one_le_exp (by have : (0 : ℝ) < 2 ^ k := by positivity; nlinarith)
    calc heckeDefect f ((2 : ℝ) ^ k)
        ≤ reading f ((2 : ℝ) ^ k) 1 (dyadicThetaPrefix k) + Emax := by linarith
      _ ≤ |C₁| * ((dyadicThetaPrefix k : ℝ) + 1) ^ q + Emax := by linarith
      _ ≤ |C₁| * ((9 : ℝ) ^ (q / 2) * Real.exp ((1 - 2 * θ + ε) * (2 : ℝ) ^ k)) +
            Emax * Real.exp ((1 - 2 * θ + ε) * (2 : ℝ) ^ k) :=
          add_le_add (mul_le_mul_of_nonneg_left hrpow_le_exp (abs_nonneg C₁))
            (le_mul_of_one_le_right hEmax0 hexp_ge1)
      _ = (|C₁| * (9 : ℝ) ^ (q / 2) + Emax) * Real.exp ((1 - 2 * θ + ε) * (2 : ℝ) ^ k) := by ring

/-- Equivalence between `GrowingEndpointEscapedMoebiusLaw θ` and single-scale prefix growth. -/
theorem growingEndpointEscapedMoebiusLaw_iff_singleScale_reading_rate
    {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ ≤ 1 / 2) :
    GrowingEndpointEscapedMoebiusLaw θ ↔
      ∀ (f : CompactTest) (ε : ℝ), 0 < ε → ∃ C : ℝ, ∀ k : ℕ,
        reading f ((2 : ℝ) ^ k) 1 (dyadicThetaPrefix k) ≤
          C * ((dyadicThetaPrefix k : ℝ) + 1) ^ (2 * (1 - 2 * θ) + ε) := by
  have h03 : GrowingEndpointEscapedMoebiusLaw θ ↔ zetaZeroAbscissa ≤ 1 - θ :=
    (escapedMoebius_rbg_seven_way_tfae hθ0 hθ2).out 0 3
  exact h03.trans (zetaZeroAbscissa_le_iff_singleScale_reading_rate hθ0 hθ2)

/-- **Endpoint (`θ = 1 / 2`) Single-Scale Sub-Polynomial Integer-Prefix Criterion for `RH`:**
`RiemannHypothesis` holds if and only if for every `f : CompactTest` and `ε > 0`,
`reading f (2^k) 1 (dyadicThetaPrefix k) ≤ C * (dyadicThetaPrefix k + 1)^ε` for all `k : ℕ`. -/
theorem riemannHypothesis_iff_singleScale_reading_subpoly :
    RiemannHypothesis ↔
      ∀ (f : CompactTest) (ε : ℝ), 0 < ε → ∃ C : ℝ, ∀ k : ℕ,
        reading f ((2 : ℝ) ^ k) 1 (dyadicThetaPrefix k) ≤
          C * ((dyadicThetaPrefix k : ℝ) + 1) ^ ε := by
  have h1 := riemannHypothesis_iff_receiverDampingRate_eq_zero
  have h2 : receiverDampingRate = 0 ↔ zetaZeroAbscissa ≤ 1 - (1 / 2 : ℝ) := by
    rw [receiverDampingRate_eq_zetaZeroAbscissa_sub_half]
    have hnn : 0 ≤ receiverDampingRate := receiverDampingRate_nonneg
    rw [receiverDampingRate_eq_zetaZeroAbscissa_sub_half] at hnn
    constructor <;> intro h <;> linarith
  have h3 := zetaZeroAbscissa_le_iff_singleScale_reading_rate (θ := 1 / 2) (by norm_num) le_rfl
  rw [h1, h2, h3]
  simp only [show (2 : ℝ) * (1 - 2 * (1 / 2 : ℝ)) = 0 by ring, zero_add]

/-! ## §3. Unconditional Vinogradov–Korobov Sub-Trivial Single-Scale Prefix Ceiling -/

/-- **Two-Sided Vinogradov–Korobov Carrier Depth Profile:**
There exist `γ₀ ≥ exp(e³⁰)` and `0 < η₁ < 1 / 2` such that for every height `G ≥ γ₀` and every
`ρ : zetaZeroConfig.carrier` with `|(ρ : ℂ).im| ≤ G`,
`|zetaDepth ρ| ≤ 1 / 2 - min η₁ (vkZeroFreeWidth G)`. -/
theorem exists_vk_carrier_depth_profile :
    ∃ γ₀ η₁ : ℝ, Real.exp (Real.exp 30) ≤ γ₀ ∧ 0 < η₁ ∧ η₁ < 1 / 2 ∧
      ∀ G : ℝ, γ₀ ≤ G → ∀ ρ : zetaZeroConfig.carrier, |(ρ : ℂ).im| ≤ G →
        |zetaDepth ρ| ≤ 1 / 2 - min η₁ (vkZeroFreeWidth G) := by
  obtain ⟨γ₀, hγ₀e, hvk⟩ := exists_re_le_of_mem_zetaCarrier_vk
  have hγ₀pos : 0 < γ₀ := lt_of_lt_of_le (Real.exp_pos _) hγ₀e
  have hlogγ₀ : Real.exp 30 ≤ Real.log γ₀ := by
    rw [Real.le_log_iff_exp_le hγ₀pos]; exact hγ₀e
  have hlogγ₀pos : 0 < Real.log γ₀ := lt_of_lt_of_le (Real.exp_pos _) hlogγ₀
  have h23 : Real.exp 23 ≤ γ₀ := by
    refine le_trans (Real.exp_le_exp.mpr ?_) hγ₀e
    linarith [Real.add_one_le_exp (30 : ℝ)]
  set η₁ : ℝ := min lowZeroFreeWidth (1 / (100 * Real.log γ₀))
  have hη₁_pos : 0 < η₁ := lt_min lowZeroFreeWidth_pos (by positivity)
  have hη₁_lt : η₁ < 1 / 2 := by
    have hlog_gt1 : 1 ≤ Real.log γ₀ := le_trans (by linarith [Real.add_one_le_exp (30 : ℝ)]) hlogγ₀
    have hdiv : 1 / (100 * Real.log γ₀) ≤ 1 / 100 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith [min_le_right lowZeroFreeWidth (1 / (100 * Real.log γ₀))]
  have hre_carrier : ∀ G : ℝ, γ₀ ≤ G → ∀ s ∈ zetaZeroConfig.carrier, |s.im| ≤ G →
      s.re ≤ 1 - min η₁ (vkZeroFreeWidth G) := by
    intro G hG s hs him
    rcases le_or_gt |s.im| (Real.exp 23) with hlow | hmid
    · have h := re_le_of_mem_zetaCarrier_low hs hlow
      have hm : min η₁ (vkZeroFreeWidth G) ≤ lowZeroFreeWidth :=
        (min_le_left _ _).trans (min_le_left _ _)
      linarith
    · rcases le_or_gt |s.im| γ₀ with hmed | hhigh
      · have h := re_le_of_mem_zetaCarrier_high hs hmid.le
        have hpos_im : 0 < |s.im| := lt_of_lt_of_le (Real.exp_pos _) hmid.le
        have hlog_im_pos : 0 < Real.log |s.im| :=
          lt_of_lt_of_le (by norm_num : (0 : ℝ) < 23)
            ((Real.le_log_iff_exp_le hpos_im).mpr hmid.le)
        have hlog_le : Real.log |s.im| ≤ Real.log γ₀ := Real.log_le_log hpos_im hmed
        have hdiv : 1 / (100 * Real.log γ₀) ≤ 1 / 100 / Real.log |s.im| := by
          rw [div_div]
          exact one_div_le_one_div_of_le (by positivity) (by linarith)
        have hm : min η₁ (vkZeroFreeWidth G) ≤ 1 / (100 * Real.log γ₀) :=
          (min_le_left _ _).trans (min_le_right _ _)
        linarith
      · have h := hvk s hs hhigh.le
        have hant := vkZeroFreeWidth_antitone (hγ₀e.trans hhigh.le) him
        have hm : min η₁ (vkZeroFreeWidth G) ≤ vkZeroFreeWidth G := min_le_right _ _
        linarith
  refine ⟨γ₀, η₁, hγ₀e, hη₁_pos, hη₁_lt, fun G hG ρ him => ?_⟩
  have hρ_hi := hre_carrier G hG ρ ρ.2 him
  have hrefl_mem : (1 - (ρ : ℂ)) ∈ zetaZeroConfig.carrier :=
    ⟨riemannZeta_one_sub_eq_zero_of_mem_openStrip ρ.2.1 ρ.2.2.1 ρ.2.2.2,
      by simp; linarith [ρ.2.2.2], by simp; linarith [ρ.2.2.1]⟩
  have hrefl_im : |(1 - (ρ : ℂ)).im| ≤ G := by simpa using him
  have hρ_lo := hre_carrier G hG (1 - (ρ : ℂ)) hrefl_mem hrefl_im
  simp only [Complex.sub_re, Complex.one_re] at hρ_lo
  rw [zetaDepth, abs_le]
  constructor <;> linarith

private theorem depthKernel_le_exp_abs_two_mul (L : ℝ) {d : ℝ} (hd : 0 ≤ d) :
    depthKernel L d ≤ Real.exp (2 * d * |L|) := by
  unfold depthKernel
  rcases le_or_gt 0 L with hL | hL
  · rw [abs_of_nonneg hL, Real.cosh_eq]
    have hneg : Real.exp (-(2 * d * L)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    linarith [Real.exp_pos (2 * d * L)]
  · rw [abs_of_neg hL]
    have hcosh : Real.cosh (2 * d * L) = Real.cosh (2 * d * (-L)) := by
      rw [show 2 * d * L = -(2 * d * (-L)) by ring, Real.cosh_neg]
    rw [hcosh, Real.cosh_eq]
    have hneg : Real.exp (-(2 * d * (-L))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    linarith [Real.exp_pos (2 * d * (-L))]

/-- **Unconditional Vinogradov–Korobov Sub-Trivial Ceiling on `heckeDefect` and `reading`:**
For every `f : CompactTest`, there exist `N₀ ≥ 1`, `0 < η₁ < 1 / 2`, `C_tail ≥ 0`, and `B₁, D₁ ≥ 0`
such that for **every** `n ≥ N₀` and **every** `L : ℝ` with `|L| ≤ 2 * log(n + 1)`:
* `heckeDefect f L ≤ mass f * (n + 1)² * exp(-4 * min η₁ (vkZeroFreeWidth (n + 2)) * log(n + 1)) + C_tail * sourceReferenceTail n`;
* `reading f L 1 n ≤ mass f * (n + 1)² * exp(-4 * min η₁ (vkZeroFreeWidth (n + 2)) * log(n + 1)) + C_tail * sourceReferenceTail n + thetaPrefixError B₁ D₁ n`. -/
theorem exists_reading_logHorizon_vk_ceiling (f : CompactTest) :
    ∃ (N₀ : ℕ) (η₁ C_tail B₁ D₁ : ℝ),
      1 ≤ N₀ ∧ 0 < η₁ ∧ η₁ < 1 / 2 ∧ 0 ≤ C_tail ∧ 0 ≤ B₁ ∧ 0 ≤ D₁ ∧
      ∀ n : ℕ, N₀ ≤ n → ∀ L : ℝ, |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
        heckeDefect f L ≤
          mass f * ((n : ℝ) + 1) ^ 2 *
            Real.exp (-4 * min η₁ (vkZeroFreeWidth ((n : ℝ) + 2)) * Real.log ((n : ℝ) + 1)) +
          C_tail * sourceReferenceTail n ∧
        reading f L 1 n ≤
          mass f * ((n : ℝ) + 1) ^ 2 *
            Real.exp (-4 * min η₁ (vkZeroFreeWidth ((n : ℝ) + 2)) * Real.log ((n : ℝ) + 1)) +
          C_tail * sourceReferenceTail n + thetaPrefixError B₁ D₁ n := by
  obtain ⟨γ₀, η₁, hγ₀e, hη₁_pos, hη₁_lt, hvk_prof⟩ := exists_vk_carrier_depth_profile
  obtain ⟨C_tail, hC_tail, htail_bd⟩ := moving_depth_trace_tail_le f 1
  obtain ⟨B₁, D₁, _, _, hB₁, hD₁, _, _, herr₁, -⟩ := exists_explicit_reading_transfer_constants f
  set N₀ : ℕ := max 1 ⌈γ₀⌉₊
  refine ⟨N₀, η₁, C_tail, B₁, D₁, le_max_left _ _, hη₁_pos, hη₁_lt, hC_tail, hB₁, hD₁,
    fun n hn L hL => ?_⟩
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hnγ : γ₀ ≤ (n : ℝ) + 2 := by
    have h1 : γ₀ ≤ (⌈γ₀⌉₊ : ℝ) := Nat.le_ceil γ₀
    have h2 : (⌈γ₀⌉₊ : ℝ) ≤ n := by exact_mod_cast (le_max_right 1 ⌈γ₀⌉₊).trans hn
    linarith
  set δ : ℝ := min η₁ (vkZeroFreeWidth ((n : ℝ) + 2))
  have hvk_pos : 0 < vkZeroFreeWidth ((n : ℝ) + 2) := by
    unfold vkZeroFreeWidth
    have hg0 : 0 < (n : ℝ) + 2 := by positivity
    have hlg : Real.exp 30 ≤ Real.log ((n : ℝ) + 2) :=
      (Real.le_log_iff_exp_le hg0).mpr (hγ₀e.trans hnγ)
    have hlg0 : 0 < Real.log ((n : ℝ) + 2) := lt_of_lt_of_le (Real.exp_pos _) hlg
    have hllg : 30 ≤ Real.log (Real.log ((n : ℝ) + 2)) := by
      rw [← Real.log_exp 30]; exact Real.log_le_log (Real.exp_pos _) hlg
    have hllg0 : 0 < Real.log (Real.log ((n : ℝ) + 2)) := by linarith
    positivity
  have hδ_pos : 0 < δ := lt_min hη₁_pos hvk_pos
  have hδ_lt : δ < 1 / 2 := (min_le_left _ _).trans_lt hη₁_lt
  set Kcap : ℝ := ((n : ℝ) + 1) ^ 2 * Real.exp (-4 * δ * Real.log ((n : ℝ) + 1))
  have hKcap_nn : 0 ≤ Kcap := by dsimp [Kcap]; positivity
  have hdk_cap : depthKernel L (1 / 2 - δ) ≤ Kcap := by
    have hd_nn : 0 ≤ 1 / 2 - δ := by linarith
    have h1 := depthKernel_le_exp_abs_two_mul L hd_nn
    have h2 : Real.exp (2 * (1 / 2 - δ) * |L|) ≤
        Real.exp (2 * (1 / 2 - δ) * (2 * Real.log ((n : ℝ) + 1))) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hL (by positivity))
    have hn1_pos : 0 < (n : ℝ) + 1 := by positivity
    have h3 : Real.exp (2 * (1 / 2 - δ) * (2 * Real.log ((n : ℝ) + 1))) = Kcap := by
      dsimp [Kcap]
      rw [show 2 * (1 / 2 - δ) * (2 * Real.log ((n : ℝ) + 1)) =
        (Real.log ((n : ℝ) + 1) + Real.log ((n : ℝ) + 1)) + (-4 * δ * Real.log ((n : ℝ) + 1)) by ring,
        Real.exp_add, Real.exp_add, Real.exp_log hn1_pos, sq]
    exact (h1.trans h2).trans_eq h3
  have hcut_trace : zetaSourceTrace (fun z => sourceCutoff n z * sourceDepthKernel f L 1 z) ≤
      mass f * Kcap := by
    have hs_mass : Summable (fun ρ : zetaZeroConfig.carrier => zetaWeight f ρ * Kcap) :=
      (summable_zetaWeight f).mul_right Kcap
    have hterm_le : ∀ ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) * (sourceCutoff n ρ * sourceDepthKernel f L 1 ρ) ≤
          zetaWeight f ρ * Kcap := by
      intro ρ
      by_cases hχ0 : sourceCutoff n ρ = 0
      · rw [hχ0, zero_mul, mul_zero]
        exact mul_nonneg (zetaWeight_nonneg f ρ) hKcap_nn
      · have hmem_ball : (ρ : ℂ) ∈ Metric.closedBall (0 : ℂ) ((n : ℝ) + 2) := by
          have ht : (ρ : ℂ) ∈ tsupport (sourceCutoff n) := subset_tsupport _ hχ0
          rwa [(sourceCutoff n).tsupport_eq] at ht
        have hnorm_le : ‖(ρ : ℂ)‖ ≤ (n : ℝ) + 2 := by
          simpa [Metric.mem_closedBall, dist_zero_right] using hmem_ball
        have him_le : |(ρ : ℂ).im| ≤ (n : ℝ) + 2 :=
          (Complex.abs_im_le_norm (ρ : ℂ)).trans hnorm_le
        have hdepth := hvk_prof ((n : ℝ) + 2) hnγ ρ him_le
        have hmono : depthKernel L (zetaDepth ρ) ≤ depthKernel L (1 / 2 - δ) := by
          refine depthKernel_mono_depth L ?_
          rw [abs_of_nonneg (by linarith : 0 ≤ 1 / 2 - δ)]
          exact hdepth
        have hdk_ρ : depthKernel L (zetaDepth ρ) ≤ Kcap := hmono.trans hdk_cap
        have hcut1 : sourceCutoff n ρ ≤ 1 := (sourceCutoff n).le_one
        have hcut0 : 0 ≤ sourceCutoff n ρ := (sourceCutoff n).nonneg
        have hsdk : (zetaZeroConfig.mult ρ : ℝ) * (sourceCutoff n ρ * sourceDepthKernel f L 1 ρ) =
            sourceCutoff n ρ * (zetaWeight f ρ * depthKernel L (zetaDepth ρ)) := by
          dsimp [sourceDepthKernel, zetaWeight, zetaDepth]; ring
        rw [hsdk]
        calc sourceCutoff n ρ * (zetaWeight f ρ * depthKernel L (zetaDepth ρ))
            ≤ 1 * (zetaWeight f ρ * depthKernel L (zetaDepth ρ)) :=
              mul_le_mul_of_nonneg_right hcut1
                (mul_nonneg (zetaWeight_nonneg f ρ) (depthKernel_nonneg _ _))
          _ = zetaWeight f ρ * depthKernel L (zetaDepth ρ) := one_mul _
          _ ≤ zetaWeight f ρ * Kcap := mul_le_mul_of_nonneg_left hdk_ρ (zetaWeight_nonneg f ρ)
    have hsum_cut : Summable (fun ρ : zetaZeroConfig.carrier =>
        (zetaZeroConfig.mult ρ : ℝ) * (sourceCutoff n ρ * sourceDepthKernel f L 1 ρ)) :=
      Summable.of_nonneg_of_le
        (fun ρ => mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (sourceCutoff n).nonneg
            (mul_nonneg (Complex.normSq_nonneg _) (pow_nonneg (depthKernel_nonneg _ _) 1))))
        hterm_le hs_mass
    calc zetaSourceTrace (fun z => sourceCutoff n z * sourceDepthKernel f L 1 z)
        ≤ ∑' ρ : zetaZeroConfig.carrier, zetaWeight f ρ * Kcap :=
          hsum_cut.tsum_le_tsum hterm_le hs_mass
      _ = mass f * Kcap := by rw [tsum_mul_right]; rfl
  have htail0 := htail_bd n L 0 (by simp; positivity) (by simpa using hL)
  rw [sourceTwist_zero, zetaSourceTrace_depthKernel_eq] at htail0
  have htr_eq : (∑' ρ : zetaZeroConfig.carrier, zetaWeight f ρ * depthKernel L (zetaDepth ρ) ^ 1) =
      heckeDefect f L := by
    simp only [pow_one]; rfl
  rw [htr_eq] at htail0
  have hhd_le : heckeDefect f L ≤ mass f * Kcap + C_tail * sourceReferenceTail n := by
    linarith [(abs_le.mp htail0).2, hcut_trace]
  have hread_err := (abs_le.mp (herr₁ n hn1 L hL)).2
  refine ⟨?_, ?_⟩
  · dsimp [Kcap] at hhd_le; linarith
  · dsimp [Kcap] at hhd_le; linarith

/-- **Asymptotic Sub-Triviality of Single-Scale Prefix Readings:**
For every `f : CompactTest` and every scale schedule `L : ℕ → ℝ` inside the logarithmic horizon
`∀ n, |L n| ≤ 2 * log(n + 1)` (in particular `L n = 2 * log(n + 1)`),
`reading f (L n) 1 n / (n + 1)² → 0` as `n → ∞`. -/
theorem tendsto_reading_logHorizon_div_sq_zero (f : CompactTest) {L : ℕ → ℝ}
    (hL : ∀ n : ℕ, |L n| ≤ 2 * Real.log ((n : ℝ) + 1)) :
    Tendsto (fun n : ℕ => reading f (L n) 1 n / ((n : ℝ) + 1) ^ 2) atTop (𝓝 0) := by
  obtain ⟨N₀, η₁, C_tail, B₁, D₁, hN₀, hη₁_pos, _, hC_tail, hB₁, hD₁, hvk_bd⟩ :=
    exists_reading_logHorizon_vk_ceiling f
  set δ : ℕ → ℝ := fun n => min η₁ (vkZeroFreeWidth ((n : ℝ) + 2))
  have hvk_prod_atTop : Tendsto (fun n : ℕ => δ n * Real.log ((n : ℝ) + 1)) atTop atTop := by
    have hy_atTop : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 2)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
    have hlow_atTop : Tendsto
        (fun n : ℕ => min (η₁ * (Real.log ((n : ℝ) + 2) / 2))
          ((1 / (2 * 10 ^ 8 * (6 : ℝ) ^ (5 / 3 : ℝ))) *
            (Real.log ((n : ℝ) + 2)) ^ (1 / 18 : ℝ))) atTop atTop := by
      rw [Filter.tendsto_atTop]
      intro b
      have hb1 := ((hy_atTop.atTop_div_const two_pos).const_mul_atTop hη₁_pos).eventually
        (eventually_ge_atTop b)
      have hb2 := (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 18)).comp
        hy_atTop).const_mul_atTop (by positivity)).eventually (eventually_ge_atTop b)
      filter_upwards [hb1, hb2] with n h1 h2
      exact le_min h1 h2
    refine tendsto_atTop_mono' atTop ?_ hlow_atTop
    filter_upwards [eventually_ge_atTop (max N₀ 2),
      hy_atTop.eventually (eventually_ge_atTop (Real.exp 1))] with n hn hy1
    have hn2 : 2 ≤ n := (le_max_right N₀ 2).trans hn
    set y : ℝ := Real.log ((n : ℝ) + 2)
    have hy_pos : 0 < y := lt_of_lt_of_le (Real.exp_pos 1) hy1
    have hly_ge1 : 1 ≤ Real.log y := (Real.le_log_iff_exp_le hy_pos).mpr hy1
    have hly_pos : 0 < Real.log y := by linarith
    have hlog_n1 : y / 2 ≤ Real.log ((n : ℝ) + 1) := by
      have hn_sq : (n : ℝ) + 2 ≤ ((n : ℝ) + 1) ^ 2 := by
        have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
        nlinarith
      have hl := Real.log_le_log (by positivity) hn_sq
      rw [Real.log_pow, Nat.cast_two] at hl
      linarith
    have hly_le : Real.log y ≤ 6 * y ^ (1 / 6 : ℝ) := by
      have h1 := Real.add_one_le_exp (Real.log y / 6)
      have h2 : Real.exp (Real.log y / 6) = y ^ (1 / 6 : ℝ) := by
        rw [Real.rpow_def_of_pos hy_pos]; congr 1; ring
      linarith
    have hly_pow : Real.log y ^ (5 / 3 : ℝ) ≤ (6 : ℝ) ^ (5 / 3 : ℝ) * y ^ (5 / 18 : ℝ) := by
      calc Real.log y ^ (5 / 3 : ℝ)
          ≤ (6 * y ^ (1 / 6 : ℝ)) ^ (5 / 3 : ℝ) :=
            Real.rpow_le_rpow hly_pos.le hly_le (by norm_num)
        _ = (6 : ℝ) ^ (5 / 3 : ℝ) * (y ^ (1 / 6 : ℝ)) ^ (5 / 3 : ℝ) :=
            Real.mul_rpow (by norm_num) (Real.rpow_nonneg hy_pos.le _)
        _ = (6 : ℝ) ^ (5 / 3 : ℝ) * y ^ (5 / 18 : ℝ) := by
            rw [← Real.rpow_mul hy_pos.le]; congr 2; norm_num
    have hvk_lo : (1 / (2 * 10 ^ 8 * (6 : ℝ) ^ (5 / 3 : ℝ))) * y ^ (1 / 18 : ℝ) ≤
        vkZeroFreeWidth ((n : ℝ) + 2) * Real.log ((n : ℝ) + 1) := by
      unfold vkZeroFreeWidth
      change _ ≤ y ^ (-(2 : ℝ) / 3) * Real.log y ^ (-(5 : ℝ) / 3) / 10 ^ 8 * Real.log ((n : ℝ) + 1)
      have hrw1 : y ^ (-(2 : ℝ) / 3) = (y ^ (2 / 3 : ℝ))⁻¹ := by
        rw [show (-(2 : ℝ) / 3) = -(2 / 3 : ℝ) by ring, Real.rpow_neg hy_pos.le]
      have hrw2 : Real.log y ^ (-(5 : ℝ) / 3) = (Real.log y ^ (5 / 3 : ℝ))⁻¹ := by
        rw [show (-(5 : ℝ) / 3) = -(5 / 3 : ℝ) by ring, Real.rpow_neg hly_pos.le]
      rw [hrw1, hrw2]
      have hden_pos : 0 < y ^ (2 / 3 : ℝ) * Real.log y ^ (5 / 3 : ℝ) := by positivity
      have hden_le : y ^ (2 / 3 : ℝ) * Real.log y ^ (5 / 3 : ℝ) ≤
          (6 : ℝ) ^ (5 / 3 : ℝ) * y ^ (17 / 18 : ℝ) := by
        calc y ^ (2 / 3 : ℝ) * Real.log y ^ (5 / 3 : ℝ)
            ≤ y ^ (2 / 3 : ℝ) * ((6 : ℝ) ^ (5 / 3 : ℝ) * y ^ (5 / 18 : ℝ)) :=
              mul_le_mul_of_nonneg_left hly_pow (Real.rpow_nonneg hy_pos.le _)
          _ = (6 : ℝ) ^ (5 / 3 : ℝ) * (y ^ (2 / 3 : ℝ) * y ^ (5 / 18 : ℝ)) := by ring
          _ = (6 : ℝ) ^ (5 / 3 : ℝ) * y ^ (17 / 18 : ℝ) := by
              rw [← Real.rpow_add hy_pos]; congr 2; norm_num
      have hy_split : y = y ^ (17 / 18 : ℝ) * y ^ (1 / 18 : ℝ) := by
        rw [← Real.rpow_add hy_pos]
        norm_num
      have hinv_le : ((6 : ℝ) ^ (5 / 3 : ℝ) * y ^ (17 / 18 : ℝ))⁻¹ ≤
          (y ^ (2 / 3 : ℝ) * Real.log y ^ (5 / 3 : ℝ))⁻¹ :=
        inv_anti₀ hden_pos hden_le
      calc (1 / (2 * 10 ^ 8 * (6 : ℝ) ^ (5 / 3 : ℝ))) * y ^ (1 / 18 : ℝ)
          = ((6 : ℝ) ^ (5 / 3 : ℝ) * y ^ (17 / 18 : ℝ))⁻¹ / 10 ^ 8 * (y / 2) := by
            have hy_div : y / 2 = y ^ (17 / 18 : ℝ) * y ^ (1 / 18 : ℝ) / 2 := by
              rw [← hy_split]
            rw [hy_div]
            have hp17 : (y ^ (17 / 18 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hy_pos _).ne'
            have hp6 : ((6 : ℝ) ^ (5 / 3 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
            field_simp [hp17, hp6]
        _ ≤ (y ^ (2 / 3 : ℝ) * Real.log y ^ (5 / 3 : ℝ))⁻¹ / 10 ^ 8 * Real.log ((n : ℝ) + 1) := by
            refine mul_le_mul (div_le_div_of_nonneg_right hinv_le (by norm_num)) hlog_n1
              (by positivity) (by positivity)
        _ = (y ^ (2 / 3 : ℝ))⁻¹ * (Real.log y ^ (5 / 3 : ℝ))⁻¹ / 10 ^ 8 * Real.log ((n : ℝ) + 1) := by
            rw [mul_inv]
    dsimp only [δ]
    rcases le_total η₁ (vkZeroFreeWidth ((n : ℝ) + 2)) with hmin | hmin
    · rw [min_eq_left hmin]
      exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hlog_n1 hη₁_pos.le)
    · rw [min_eq_right hmin]
      exact (min_le_right _ _).trans hvk_lo
  have hexp_zero : Tendsto (fun n : ℕ =>
      mass f * Real.exp (-4 * δ n * Real.log ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have hneg : Tendsto (fun n : ℕ => -4 * δ n * Real.log ((n : ℝ) + 1)) atTop atBot := by
      rw [Filter.tendsto_atBot]
      intro b
      filter_upwards [hvk_prod_atTop.eventually (eventually_ge_atTop (-b / 4))] with n hn
      linarith
    have hc := (Real.tendsto_exp_atBot.comp hneg).const_mul (mass f)
    rw [mul_zero] at hc
    exact hc
  have htail_zero : Tendsto (fun n : ℕ =>
      (C_tail * sourceReferenceTail n + thetaPrefixError B₁ D₁ n) / ((n : ℝ) + 1) ^ 2)
      atTop (𝓝 0) := by
    have hnum : Tendsto (fun n : ℕ => C_tail * sourceReferenceTail n + thetaPrefixError B₁ D₁ n)
        atTop (𝓝 0) := by
      simpa using (tendsto_sourceReferenceTail.const_mul C_tail).add
        (tendsto_thetaPrefixError_zero B₁ D₁)
    refine squeeze_zero_norm' ?_ (by simpa using hnum.norm)
    filter_upwards [eventually_ge_atTop 1] with n _
    have hsq1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; nlinarith
    rw [norm_div, Real.norm_of_nonneg (sq_nonneg ((n : ℝ) + 1))]
    exact div_le_self (norm_nonneg _) hsq1
  have hup_zero : Tendsto (fun n : ℕ =>
      mass f * Real.exp (-4 * δ n * Real.log ((n : ℝ) + 1)) +
        (C_tail * sourceReferenceTail n + thetaPrefixError B₁ D₁ n) / ((n : ℝ) + 1) ^ 2)
      atTop (𝓝 0) := by
    have h := hexp_zero.add htail_zero
    rw [add_zero] at h
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup_zero ?_ ?_
  · filter_upwards with n
    exact div_nonneg (finiteThetaSourceMomentReading_nonneg f (L n) 1 n) (sq_nonneg _)
  · filter_upwards [eventually_ge_atTop N₀] with n hn
    have hbd := (hvk_bd n hn (L n) (hL n)).2
    have hsq_pos : 0 < ((n : ℝ) + 1) ^ 2 := by positivity
    rw [div_le_iff₀ hsq_pos]
    dsimp only [δ]
    have hid : (mass f * Real.exp (-4 * min η₁ (vkZeroFreeWidth ((n : ℝ) + 2)) *
          Real.log ((n : ℝ) + 1)) +
        (C_tail * sourceReferenceTail n + thetaPrefixError B₁ D₁ n) / ((n : ℝ) + 1) ^ 2) *
        ((n : ℝ) + 1) ^ 2 =
      mass f * ((n : ℝ) + 1) ^ 2 *
        Real.exp (-4 * min η₁ (vkZeroFreeWidth ((n : ℝ) + 2)) * Real.log ((n : ℝ) + 1)) +
        C_tail * sourceReferenceTail n + thetaPrefixError B₁ D₁ n := by
      field_simp [hsq_pos.ne']
    linarith [hbd, hid]

end GaloisForLFunctions.BezoutValuationIncidence

end
