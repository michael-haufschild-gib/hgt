import GaloisForLFunctions.RHTower.CHMDStage5FourModeGaussCoercivityAndPolarCone
import GaloisForLFunctions.RHTower.CHMDStage11SechSquareToeplitzSpectralDecomposition

/-!
# CHMD Stage 12: Four-Mode Digamma Shift and Positive-Minus-Positive Coercive Decomposition of the Decisive `sechHalf` Toeplitz Form

This module establishes **Stage 12** of the Causal Hyperbolic–Modular Duality (CHMD) route by
combining the 4-mode shifted digamma spectral density
`fourModeShiftedArchDensity r = Re ψ(17/4 + ir/2) - log π > 42 / 585 > 0` (`CHMDStage5`) with the
trigonometric wave-packet / `sechSqHalf` Toeplitz decomposition (`CHMDStage11`):

1. **Section 1 (The 4-Mode Lorentzian Spectral Weight `fourModeGaussSpectralWeight` and Exact
   Splitting of `EF.gammaBracket` and `evenArchPart`):**
   - In `evenArchPart K = ∫ r, (K r).re * EF.gammaBracket r`, the raw digamma kernel
     `EF.gammaBracket r = Re ψ(1/4 + ir/2) - log π` is indefinite (negative near `r = 0` and
     positive at large `|r|`).
   - Defining the strictly positive, bounded 4-mode Lorentzian resolvent weight
     `fourModeGaussSpectralWeight r = 1/(1/4 + r²) + 5/(25/4 + r²) + 9/(81/4 + r²) + 13/(169/4 + r²) ≤ 3248 / 585`,
     we have the exact identity
     `EF.gammaBracket r = fourModeShiftedArchDensity r - fourModeGaussSpectralWeight r`
     (`gammaBracket_eq_fourModeShiftedArchDensity_sub`), which splits `evenArchPart K` for every
     `GoodDensity K` into the strictly positive `fourModeShiftedArchDensity` integral minus the
     bounded 4-mode Lorentzian integral (`evenArchPart_eq_fourModeShifted_sub_gauss`).

2. **Section 2 (Unconditional Pointwise Positivity and $L^1$ Coercivity of the 4-Mode Shifted
   Archimedean Integral):**
   - Because `fourModeShiftedArchDensity r > 42 / 585 > 0` for all `r ∈ ℝ`, for every
     `GoodDensity K` with `(K r).re ≥ 0` on `ℝ`, the shifted archimedean integral satisfies the
     unconditional $L^1$ coercive lower bound
     `(42 / 585) * ∫ r, (K r).re ≤ ∫ r, (K r).re * fourModeShiftedArchDensity r`
     (`forty_two_div_585_mul_integral_le_fourModeShifted`).
   - Specializing to `specSq sechHalf` at `y = 0` (`∫ r, sechSqHalf r = 4`) gives the explicit
     rational lower bound `56 / 195 ≤ ∫ r, sechSqHalf r * fourModeShiftedArchDensity r`
     (`fifty_six_div_195_le_integral_sechSqHalf_fourModeShiftedArchDensity`), and specializing to
     any wave packet `(t, c)` gives
     `(42 / 585) * ∫ r, trigPacketWeight t c (√(r² + 2)) * sechSqHalf r ≤ ∫ r, trigPacketWeight t c (√(r² + 2)) * sechSqHalf r * fourModeShiftedArchDensity r`
     (`forty_two_div_585_mul_integral_trigPacketWeight_sechSqHalf_le`).

3. **Section 3 (Exact Positive-Minus-Positive Decomposition and Coercive Lower Bounds for the
   Decisive `sechHalf` Toeplitz Form):**
   - We prove the exact positive-minus-positive decomposition of
     `∑ i, ∑ j, c i * c j * cosineShiftFn lam sechHalf (t j - t i)` into the unconditionally
     nonnegative pole square + coercive `fourModeShiftedArchDensity` integral minus the 4-mode
     Lorentzian resolvent integral and prime series
     (`sum_sum_cosineShiftFn_sechHalf_eq_fourModeShifted_parts`,
     `sum_sum_cosineShiftFn_sechHalf_vonMangoldt_eq_fourModeShifted_parts`,
     `coercive_l1_sub_fourModeGauss_sub_prime_le_sum_sum_cosineShiftFn_sechHalf`).

4. **Section 4 (4-Mode Coercive Dominance Equivalences and Sufficiency Criteria for
   `RiemannHypothesis`):**
   - We establish the exact equivalence
     `riemannHypothesis_iff_forall_fourModeGauss_add_prime_le_pole_add_fourModeShifted` and the
     coercive $L^1$ sufficiency theorems
     `riemannHypothesis_of_forall_fourModeGauss_add_prime_le_fourModeShifted`,
     `riemannHypothesis_of_forall_fourModeGauss_add_prime_le_pole_add_l1_coercive`, and
     `riemannHypothesis_of_forall_fourModeGauss_add_prime_le_l1_coercive`.
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped ComplexConjugate Nat

noncomputable section

namespace RHTower.CHMDStage12

open WeilOneSided WeilSpectral RHTower.EvenSector
open RHTower.CHMDStage1 RHTower.CHMDStage3 RHTower.CHMDStage4 RHTower.CHMDStage11
open GaloisForLFunctions.HTGeometry

/-! ## Section 1: The 4-Mode Lorentzian Spectral Weight `fourModeGaussSpectralWeight` and Exact Splitting of `EF.gammaBracket` and `evenArchPart` -/

/-- The **4-mode Lorentzian (Gauss resolvent) spectral weight** on the critical line:
`fourModeGaussSpectralWeight r = 1/(1/4 + r²) + 5/(25/4 + r²) + 9/(81/4 + r²) + 13/(169/4 + r²)`. -/
def fourModeGaussSpectralWeight (r : ℝ) : ℝ :=
  1 / (1 / 4 + r ^ 2) + 5 / (25 / 4 + r ^ 2) +
    9 / (81 / 4 + r ^ 2) + 13 / (169 / 4 + r ^ 2)

/-- Strict positivity of `fourModeGaussSpectralWeight r` for every `r ∈ ℝ`. -/
theorem fourModeGaussSpectralWeight_pos (r : ℝ) :
    0 < fourModeGaussSpectralWeight r := by
  unfold fourModeGaussSpectralWeight
  positivity

/-- Evenness of `fourModeGaussSpectralWeight`. -/
theorem fourModeGaussSpectralWeight_neg (r : ℝ) :
    fourModeGaussSpectralWeight (-r) = fourModeGaussSpectralWeight r := by
  unfold fourModeGaussSpectralWeight
  rw [neg_sq]

/-- At `r = 0`, `fourModeGaussSpectralWeight 0 = m4GaussExtractionGain = 3248 / 585`. -/
theorem fourModeGaussSpectralWeight_zero :
    fourModeGaussSpectralWeight 0 = m4GaussExtractionGain := by
  unfold fourModeGaussSpectralWeight m4GaussExtractionGain
  ring

/-- Global upper bound `fourModeGaussSpectralWeight r ≤ 3248 / 585` for all `r ∈ ℝ`. -/
theorem fourModeGaussSpectralWeight_le_zero (r : ℝ) :
    fourModeGaussSpectralWeight r ≤ m4GaussExtractionGain := by
  rw [← fourModeGaussSpectralWeight_zero]
  unfold fourModeGaussSpectralWeight
  have h0 : (0 : ℝ) ^ 2 ≤ r ^ 2 := by nlinarith [sq_nonneg r]
  gcongr

/-- Continuity of `fourModeGaussSpectralWeight`. -/
theorem continuous_fourModeGaussSpectralWeight :
    Continuous fourModeGaussSpectralWeight := by
  unfold fourModeGaussSpectralWeight
  refine (((continuous_const.div (by fun_prop) fun r => by positivity).add
    (continuous_const.div (by fun_prop) fun r => by positivity)).add
    (continuous_const.div (by fun_prop) fun r => by positivity)).add
    (continuous_const.div (by fun_prop) fun r => by positivity)

/-- **Exact Decomposition of `EF.gammaBracket r`**:
`EF.gammaBracket r = fourModeShiftedArchDensity r - fourModeGaussSpectralWeight r`. -/
theorem gammaBracket_eq_fourModeShiftedArchDensity_sub (r : ℝ) :
    EF.gammaBracket r = fourModeShiftedArchDensity r - fourModeGaussSpectralWeight r := by
  unfold fourModeShiftedArchDensity fourModeGaussSpectralWeight
  ring

/-- `fourModeShiftedArchDensity r = EF.gammaBracket r + fourModeGaussSpectralWeight r`. -/
theorem fourModeShiftedArchDensity_eq_gammaBracket_add (r : ℝ) :
    fourModeShiftedArchDensity r = EF.gammaBracket r + fourModeGaussSpectralWeight r := by
  unfold fourModeShiftedArchDensity fourModeGaussSpectralWeight
  ring

/-- Continuity of `fourModeShiftedArchDensity`. -/
theorem continuous_fourModeShiftedArchDensity :
    Continuous fourModeShiftedArchDensity := by
  have heq : fourModeShiftedArchDensity =
      fun r : ℝ => EF.gammaBracket r + fourModeGaussSpectralWeight r :=
    funext fourModeShiftedArchDensity_eq_gammaBracket_add
  rw [heq]
  exact WeilHerglotz.continuous_gammaBracket.add continuous_fourModeGaussSpectralWeight

/-- Every `GoodDensity K` is integrable on `ℝ` against `fourModeGaussSpectralWeight`. -/
theorem integrable_fourModeGaussSpectralWeight {K : ℂ → ℂ} (hK : GoodDensity K) :
    Integrable fun r : ℝ => (K r).re * fourModeGaussSpectralWeight r := by
  refine hK.integrable_mul continuous_fourModeGaussSpectralWeight
    (M := m4GaussExtractionGain) fun r => ?_
  rw [abs_of_pos (fourModeGaussSpectralWeight_pos r)]
  have hle := fourModeGaussSpectralWeight_le_zero r
  have hm : 0 ≤ m4GaussExtractionGain := by unfold m4GaussExtractionGain; positivity
  nlinarith [abs_nonneg r]

/-- Every `GoodDensity K` is integrable on `ℝ` against `fourModeShiftedArchDensity`. -/
theorem integrable_fourModeShiftedArchDensity {K : ℂ → ℂ} (hK : GoodDensity K) :
    Integrable fun r : ℝ => (K r).re * fourModeShiftedArchDensity r := by
  have heq : (fun r : ℝ => (K r).re * fourModeShiftedArchDensity r) =
      fun r : ℝ => (K r).re * EF.gammaBracket r + (K r).re * fourModeGaussSpectralWeight r := by
    funext r
    rw [fourModeShiftedArchDensity_eq_gammaBracket_add, mul_add]
  rw [heq]
  exact hK.integrable_gammaBracket.add (integrable_fourModeGaussSpectralWeight hK)

/-- **Exact 4-Mode Splitting of `evenArchPart` for Any `GoodDensity K`**:
`evenArchPart K` equals the strictly positive `fourModeShiftedArchDensity` integral minus the
4-mode Lorentzian `fourModeGaussSpectralWeight` integral. -/
theorem evenArchPart_eq_fourModeShifted_sub_gauss {K : ℂ → ℂ} (hK : GoodDensity K) :
    evenArchPart K =
      (∫ r : ℝ, (K r).re * fourModeShiftedArchDensity r) -
        ∫ r : ℝ, (K r).re * fourModeGaussSpectralWeight r := by
  unfold evenArchPart
  have heq : (fun r : ℝ => (K r).re * EF.gammaBracket r) =
      fun r : ℝ => (K r).re * fourModeShiftedArchDensity r -
        (K r).re * fourModeGaussSpectralWeight r := by
    funext r
    rw [gammaBracket_eq_fourModeShiftedArchDensity_sub, mul_sub]
  rw [heq, integral_sub (integrable_fourModeShiftedArchDensity hK)
    (integrable_fourModeGaussSpectralWeight hK)]

/-! ## Section 2: Unconditional Pointwise Positivity and $L^1$ Coercivity of the 4-Mode Shifted Archimedean Integral -/

/-- Every `GoodDensity K` has integrable real part `(K r).re` on `ℝ`. -/
theorem integrable_re_of_goodDensity {K : ℂ → ℂ} (hK : GoodDensity K) :
    Integrable fun r : ℝ => (K r).re := by
  have h := hK.integrable_mul (P := fun _ => 1) continuous_const (M := 1) fun r => by
    simp
  simpa using h

/-- **Unconditional $L^1$ Coercivity of the 4-Mode Shifted Archimedean Integral**:
for any `GoodDensity K` that is nonnegative on the real line (`∀ r, 0 ≤ (K r).re`),
`(42 / 585) * ∫ r, (K r).re ≤ ∫ r, (K r).re * fourModeShiftedArchDensity r`. -/
theorem forty_two_div_585_mul_integral_le_fourModeShifted {K : ℂ → ℂ} (hK : GoodDensity K)
    (hnn : ∀ r : ℝ, 0 ≤ (K r).re) :
    (42 / 585 : ℝ) * (∫ r : ℝ, (K r).re) ≤
      ∫ r : ℝ, (K r).re * fourModeShiftedArchDensity r := by
  rw [← integral_const_mul]
  refine integral_mono ((integrable_re_of_goodDensity hK).const_mul (42 / 585))
    (integrable_fourModeShiftedArchDensity hK) fun r => ?_
  calc (42 / 585 : ℝ) * (K r).re
      = (K r).re * (42 / 585 : ℝ) := mul_comm _ _
    _ ≤ (K r).re * fourModeShiftedArchDensity r :=
        mul_le_mul_of_nonneg_left (forty_two_div_585_lt_fourModeShiftedArchDensity r).le (hnn r)

/-- Unconditional nonnegativity of `∫ r, (K r).re * fourModeShiftedArchDensity r` for any
real-line-nonnegative `GoodDensity K`. -/
theorem integral_fourModeShiftedArchDensity_nonneg {K : ℂ → ℂ} (hK : GoodDensity K)
    (hnn : ∀ r : ℝ, 0 ≤ (K r).re) :
    0 ≤ ∫ r : ℝ, (K r).re * fourModeShiftedArchDensity r := by
  have h0 : 0 ≤ (42 / 585 : ℝ) * (∫ r : ℝ, (K r).re) :=
    mul_nonneg (by positivity) (integral_nonneg hnn)
  exact h0.trans (forty_two_div_585_mul_integral_le_fourModeShifted hK hnn)

/-- **Explicit Rational Lower Bound for the 4-Mode Shifted Archimedean Integral of `sechSqHalf`**:
since `∫ r, sechSqHalf r = 4` and `fourModeShiftedArchDensity r > 42 / 585`, we have
`56 / 195 ≤ ∫ r, sechSqHalf r * fourModeShiftedArchDensity r`. -/
theorem fifty_six_div_195_le_integral_sechSqHalf_fourModeShiftedArchDensity :
    (56 / 195 : ℝ) ≤ ∫ r : ℝ, sechSqHalf r * fourModeShiftedArchDensity r := by
  have hK := goodDensity_specSq evenStrip_sechHalf
  have hle := forty_two_div_585_mul_integral_le_fourModeShifted hK fun r => by
    rw [specSq_sechHalf_ofReal_re]; exact (sechSqHalf_pos r).le
  simp_rw [specSq_sechHalf_ofReal_re] at hle
  rw [integral_sechSqHalf] at hle
  linarith

/-- For any `EvenStrip Φ` and wave packet `(t, c)`, the combined spectral density
`fun z => specSq (cosComb t c Φ) z + specSq (sinComb t c Φ) z` is a `GoodDensity`. -/
theorem goodDensity_specSq_cosComb_add_sinComb {Φ : ℂ → ℂ} (hΦ : EvenStrip Φ) {N : ℕ}
    (t c : Fin N → ℝ) :
    GoodDensity (fun z => specSq (cosComb t c Φ) z + specSq (sinComb t c Φ) z) := by
  have hA := goodDensity_specSq (evenStrip_cosComb t c hΦ)
  have hB := goodDensity_specSq (evenStrip_sinComb t c hΦ)
  have h := GoodDensity.sum (Finset.univ : Finset (Fin 2)) (fun _ => 1)
    (K := ![specSq (cosComb t c Φ), specSq (sinComb t c Φ)])
    (fun i _ => by fin_cases i <;> simpa)
  simpa [Fin.sum_univ_two] using h

/-- **Unconditional $L^1$ Coercivity of the 4-Mode Shifted Archimedean Integral on Wave Packets**:
for any `EvenStrip Φ` and finite wave packet `(t, c)`,
`(42 / 585) * ∫ r, trigPacketWeight t c (√(r² + 2)) * ‖Φ r‖² ≤ ∫ r, trigPacketWeight t c (√(r² + 2)) * ‖Φ r‖² * fourModeShiftedArchDensity r`. -/
theorem forty_two_div_585_mul_integral_trigPacketWeight_le_fourModeShifted {Φ : ℂ → ℂ}
    (hΦ : EvenStrip Φ) {N : ℕ} (t c : Fin N → ℝ) :
    (42 / 585 : ℝ) * (∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * ‖Φ r‖ ^ 2) ≤
      ∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * ‖Φ r‖ ^ 2 *
        fourModeShiftedArchDensity r := by
  have hK := goodDensity_specSq_cosComb_add_sinComb hΦ t c
  have hre : ∀ r : ℝ,
      ((fun z => specSq (cosComb t c Φ) z + specSq (sinComb t c Φ) z) r).re =
        trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * ‖Φ r‖ ^ 2 :=
    specSq_cosComb_add_sinComb_ofReal_re t c Φ
  have hle := forty_two_div_585_mul_integral_le_fourModeShifted hK fun r => by
    rw [hre]
    exact mul_nonneg (trigPacketWeight_nonneg t c _) (sq_nonneg _)
  simpa only [hre] using hle

/-- **Unconditional $L^1$ Coercivity for `sechHalf` Wave Packets**:
for every finite wave packet `(t, c)`,
`(42 / 585) * ∫ r, trigPacketWeight t c (√(r² + 2)) * sechSqHalf r ≤ ∫ r, trigPacketWeight t c (√(r² + 2)) * sechSqHalf r * fourModeShiftedArchDensity r`. -/
theorem forty_two_div_585_mul_integral_trigPacketWeight_sechSqHalf_le {N : ℕ}
    (t c : Fin N → ℝ) :
    (42 / 585 : ℝ) * (∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r) ≤
      ∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
        fourModeShiftedArchDensity r := by
  have h := forty_two_div_585_mul_integral_trigPacketWeight_le_fourModeShifted
    evenStrip_sechHalf t c
  simpa only [norm_sechHalf_ofReal_sq] using h

/-- Unconditional nonnegativity of the 4-mode shifted archimedean integral for every `sechHalf`
wave packet `(t, c)`. -/
theorem integral_trigPacketWeight_sechSqHalf_fourModeShiftedArchDensity_nonneg {N : ℕ}
    (t c : Fin N → ℝ) :
    0 ≤ ∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
      fourModeShiftedArchDensity r := by
  have h0 : 0 ≤ (42 / 585 : ℝ) *
      (∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r) :=
    mul_nonneg (by positivity)
      (integral_nonneg fun r => mul_nonneg (trigPacketWeight_nonneg t c _) (sechSqHalf_pos r).le)
  exact h0.trans (forty_two_div_585_mul_integral_trigPacketWeight_sechSqHalf_le t c)

/-- Unconditional nonnegativity of the 4-mode Lorentzian spectral integral for every `sechHalf`
wave packet `(t, c)`. -/
theorem integral_trigPacketWeight_sechSqHalf_fourModeGaussSpectralWeight_nonneg {N : ℕ}
    (t c : Fin N → ℝ) :
    0 ≤ ∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
      fourModeGaussSpectralWeight r :=
  integral_nonneg fun r => mul_nonneg
    (mul_nonneg (trigPacketWeight_nonneg t c _) (sechSqHalf_pos r).le)
    (fourModeGaussSpectralWeight_pos r).le

/-! ## Section 3: Exact Positive-Minus-Positive Decomposition and Coercive Lower Bounds for the Decisive `sechHalf` Toeplitz Form -/

/-- **4-Mode Splitting of the Combined Archimedean Part of `cosComb` and `sinComb`**:
for any `EvenStrip Φ` and wave packet `(t, c)`, the combined archimedean integral splits into the
coercive `fourModeShiftedArchDensity` integral minus the 4-mode Lorentzian integral. -/
theorem evenArchPart_cosComb_add_sinComb_eq_fourModeShifted_sub_gauss {Φ : ℂ → ℂ}
    (hΦ : EvenStrip Φ) {N : ℕ} (t c : Fin N → ℝ) :
    evenArchPart (specSq (cosComb t c Φ)) + evenArchPart (specSq (sinComb t c Φ)) =
      (∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * ‖Φ r‖ ^ 2 *
        fourModeShiftedArchDensity r) -
      (∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * ‖Φ r‖ ^ 2 *
        fourModeGaussSpectralWeight r) := by
  have hK := goodDensity_specSq_cosComb_add_sinComb hΦ t c
  have hre : ∀ r : ℝ,
      ((fun z => specSq (cosComb t c Φ) z + specSq (sinComb t c Φ) z) r).re =
        trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * ‖Φ r‖ ^ 2 :=
    specSq_cosComb_add_sinComb_ofReal_re t c Φ
  have hsplit := evenArchPart_eq_fourModeShifted_sub_gauss hK
  unfold evenArchPart at hsplit
  simp_rw [hre] at hsplit
  rw [evenArchPart_cosComb_add_sinComb hΦ t c, hsplit]

/-- **4-Mode Splitting of the Combined Archimedean Part for `sechHalf`**:
splits `evenArchPart` for `sechHalf` into the coercive `fourModeShiftedArchDensity` integral minus
the `fourModeGaussSpectralWeight` integral. -/
theorem evenArchPart_cosComb_add_sinComb_sechHalf_eq_fourModeShifted_sub_gauss {N : ℕ}
    (t c : Fin N → ℝ) :
    evenArchPart (specSq (cosComb t c sechHalf)) + evenArchPart (specSq (sinComb t c sechHalf)) =
      (∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
        fourModeShiftedArchDensity r) -
      (∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
        fourModeGaussSpectralWeight r) := by
  have h := evenArchPart_cosComb_add_sinComb_eq_fourModeShifted_sub_gauss evenStrip_sechHalf t c
  simpa only [norm_sechHalf_ofReal_sq] using h

/-- **Exact Positive-Minus-Positive Decomposition of the `sechHalf` Toeplitz Form**:
for any `lam` with `|lam n| ≤ Cg √n (1 + log n)`, the Toeplitz quadratic form decomposes into the
nonnegative pole square + coercive `fourModeShiftedArchDensity` integral minus the 4-mode Lorentzian
integral and prime series. -/
theorem sum_sum_cosineShiftFn_sechHalf_eq_fourModeShifted_parts {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {N : ℕ}
    (t c : Fin N → ℝ) :
    (∑ i, ∑ j, c i * c j * cosineShiftFn lam sechHalf (t j - t i)) =
      (2 / Real.cos (1 / 4 : ℝ) ^ 2) * trigPacketWeight t c (Real.sqrt (7 / 4)) +
        1 / (2 * Real.pi) *
          (∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
            fourModeShiftedArchDensity r) -
        (1 / (2 * Real.pi) *
          (∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
            fourModeGaussSpectralWeight r) +
        ∑' n : ℕ, (if 2 ≤ n then lam n / Real.sqrt n else 0) *
          (1 / Real.pi * ∫ r : ℝ,
            trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
              Real.cos (r * Real.log n))) := by
  have harch := evenArchPart_cosComb_add_sinComb_sechHalf_eq_fourModeShifted_sub_gauss t c
  rw [evenArchPart_cosComb_add_sinComb evenStrip_sechHalf t c] at harch
  simp_rw [norm_sechHalf_ofReal_sq] at harch
  rw [sum_sum_cosineShiftFn_sechHalf_eq_trigPacketWeight_parts hg t c, harch]
  ring

/-- **Exact Positive-Minus-Positive Decomposition of the Decisive `Λ` Toeplitz Form**:
specializing `sum_sum_cosineShiftFn_sechHalf_eq_fourModeShifted_parts` unconditionally to `lam = Λ`. -/
theorem sum_sum_cosineShiftFn_sechHalf_vonMangoldt_eq_fourModeShifted_parts {N : ℕ}
    (t c : Fin N → ℝ) :
    (∑ i, ∑ j, c i * c j *
        cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf (t j - t i)) =
      (2 / Real.cos (1 / 4 : ℝ) ^ 2) * trigPacketWeight t c (Real.sqrt (7 / 4)) +
        1 / (2 * Real.pi) *
          (∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
            fourModeShiftedArchDensity r) -
        (1 / (2 * Real.pi) *
          (∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
            fourModeGaussSpectralWeight r) +
        ∑' n : ℕ,
          (if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0) *
            (1 / Real.pi * ∫ r : ℝ,
              trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
                Real.cos (r * Real.log n))) :=
  sum_sum_cosineShiftFn_sechHalf_eq_fourModeShifted_parts
    abs_vonMangoldt_le_sqrt_mul_one_add_log t c

/-- **Unconditional $L^1$-Coercive Lower Bound for the `sechHalf` Toeplitz Form**:
for any `lam` with `|lam n| ≤ Cg √n (1 + log n)` and any wave packet `(t, c)`,
the `sechHalf` Toeplitz form is bounded below by the pole square plus the explicit $L^1$ floor
`(42 / 585) / (2π) * ∫ r, trigPacketWeight t c (√(r² + 2)) * sechSqHalf r` minus the 4-mode
Lorentzian integral and prime series. -/
theorem coercive_l1_sub_fourModeGauss_sub_prime_le_sum_sum_cosineShiftFn_sechHalf
    {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {N : ℕ}
    (t c : Fin N → ℝ) :
    (2 / Real.cos (1 / 4 : ℝ) ^ 2) * trigPacketWeight t c (Real.sqrt (7 / 4)) +
        1 / (2 * Real.pi) *
          ((42 / 585 : ℝ) *
            (∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r)) -
        (1 / (2 * Real.pi) *
          (∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
            fourModeGaussSpectralWeight r) +
        ∑' n : ℕ, (if 2 ≤ n then lam n / Real.sqrt n else 0) *
          (1 / Real.pi * ∫ r : ℝ,
            trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
              Real.cos (r * Real.log n))) ≤
      ∑ i, ∑ j, c i * c j * cosineShiftFn lam sechHalf (t j - t i) := by
  rw [sum_sum_cosineShiftFn_sechHalf_eq_fourModeShifted_parts hg t c]
  have hpi : 0 ≤ (1 / (2 * Real.pi) : ℝ) := by positivity
  have hcoerc := mul_le_mul_of_nonneg_left
    (forty_two_div_585_mul_integral_trigPacketWeight_sechSqHalf_le t c) hpi
  linarith

/-! ## Section 4: 4-Mode Coercive Dominance Equivalences and Sufficiency Criteria for `RiemannHypothesis` -/

/-- **4-Mode Positive-Minus-Positive Characterization of the `sechHalf` Toeplitz Sign**:
the Toeplitz quadratic form is nonnegative if and only if the 4-mode Lorentzian integral plus prime
series is bounded above by the pole square plus the coercive `fourModeShiftedArchDensity` integral. -/
theorem sum_sum_cosineShiftFn_sechHalf_nonneg_iff_fourModeGauss_add_prime_le
    {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {N : ℕ}
    (t c : Fin N → ℝ) :
    0 ≤ (∑ i, ∑ j, c i * c j * cosineShiftFn lam sechHalf (t j - t i)) ↔
      1 / (2 * Real.pi) *
          (∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
            fourModeGaussSpectralWeight r) +
        (∑' n : ℕ, (if 2 ≤ n then lam n / Real.sqrt n else 0) *
          (1 / Real.pi * ∫ r : ℝ,
            trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
              Real.cos (r * Real.log n))) ≤
      (2 / Real.cos (1 / 4 : ℝ) ^ 2) * trigPacketWeight t c (Real.sqrt (7 / 4)) +
        1 / (2 * Real.pi) *
          (∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
            fourModeShiftedArchDensity r) := by
  rw [sum_sum_cosineShiftFn_sechHalf_eq_fourModeShifted_parts hg t c, sub_nonneg]

/-- **Exact 4-Mode Positive-Minus-Positive Equivalence for `RiemannHypothesis`**:
`RiemannHypothesis` holds if and only if for every finite wave packet `(t, c)`, the 4-mode
Lorentzian integral plus prime series of `trigPacketWeight t c (√(r² + 2)) * sechSqHalf r` is
bounded above by the pole square plus the strictly positive `fourModeShiftedArchDensity` integral. -/
theorem riemannHypothesis_iff_forall_fourModeGauss_add_prime_le_pole_add_fourModeShifted :
    RiemannHypothesis ↔
      ∀ (N : ℕ) (t c : Fin N → ℝ),
        1 / (2 * Real.pi) *
            (∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
              fourModeGaussSpectralWeight r) +
          (∑' n : ℕ,
            (if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0) *
              (1 / Real.pi * ∫ r : ℝ,
                trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
                  Real.cos (r * Real.log n))) ≤
        (2 / Real.cos (1 / 4 : ℝ) ^ 2) * trigPacketWeight t c (Real.sqrt (7 / 4)) +
          1 / (2 * Real.pi) *
            (∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
              fourModeShiftedArchDensity r) := by
  rw [riemannHypothesis_iff_forall_sum_sum_cosineShiftFn_sechHalf_nonneg]
  exact forall_congr' fun N => forall_congr' fun t => forall_congr' fun c =>
    sum_sum_cosineShiftFn_sechHalf_nonneg_iff_fourModeGauss_add_prime_le
      abs_vonMangoldt_le_sqrt_mul_one_add_log t c

/-- **Pole-Dropped 4-Mode Shifted Digamma Sufficiency for `RiemannHypothesis`**:
if for every finite wave packet `(t, c)`, the 4-mode Lorentzian integral plus prime series is
bounded above by the `fourModeShiftedArchDensity` integral alone, then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_forall_fourModeGauss_add_prime_le_fourModeShifted
    (h : ∀ (N : ℕ) (t c : Fin N → ℝ),
      1 / (2 * Real.pi) *
          (∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
            fourModeGaussSpectralWeight r) +
        (∑' n : ℕ,
          (if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0) *
            (1 / Real.pi * ∫ r : ℝ,
              trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
                Real.cos (r * Real.log n))) ≤
      1 / (2 * Real.pi) *
        (∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
          fourModeShiftedArchDensity r)) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_forall_fourModeGauss_add_prime_le_pole_add_fourModeShifted]
  intro N t c
  have hdom := h N t c
  have hpole : 0 ≤ (2 / Real.cos (1 / 4 : ℝ) ^ 2) * trigPacketWeight t c (Real.sqrt (7 / 4)) :=
    mul_nonneg (by positivity) (trigPacketWeight_nonneg t c _)
  linarith

/-- **$L^1$-Coercive + Pole Sufficiency for `RiemannHypothesis` on `sechSqHalf` Wave Packets**:
if for every finite wave packet `(t, c)`, the 4-mode Lorentzian integral plus prime series is
bounded above by the pole square plus the explicit $L^1$ floor
`(42 / 585) / (2π) * ∫ r, trigPacketWeight t c (√(r² + 2)) * sechSqHalf r`, then
`RiemannHypothesis` holds unconditionally. -/
theorem riemannHypothesis_of_forall_fourModeGauss_add_prime_le_pole_add_l1_coercive
    (h : ∀ (N : ℕ) (t c : Fin N → ℝ),
      1 / (2 * Real.pi) *
          (∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
            fourModeGaussSpectralWeight r) +
        (∑' n : ℕ,
          (if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0) *
            (1 / Real.pi * ∫ r : ℝ,
              trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
                Real.cos (r * Real.log n))) ≤
      (2 / Real.cos (1 / 4 : ℝ) ^ 2) * trigPacketWeight t c (Real.sqrt (7 / 4)) +
        1 / (2 * Real.pi) *
          ((42 / 585 : ℝ) *
            (∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r))) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_forall_sum_sum_cosineShiftFn_sechHalf_nonneg]
  intro N t c
  have hdom := h N t c
  have hlow := coercive_l1_sub_fourModeGauss_sub_prime_le_sum_sum_cosineShiftFn_sechHalf
    abs_vonMangoldt_le_sqrt_mul_one_add_log t c
  linarith

/-- **Pure $L^1$-Coercive Sufficiency for `RiemannHypothesis` on `sechSqHalf` Wave Packets**:
if for every finite wave packet `(t, c)`, the 4-mode Lorentzian integral plus prime series is
bounded above by `(42 / 585) / (2π) * ∫ r, trigPacketWeight t c (√(r² + 2)) * sechSqHalf r`, then
`RiemannHypothesis` holds unconditionally. -/
theorem riemannHypothesis_of_forall_fourModeGauss_add_prime_le_l1_coercive
    (h : ∀ (N : ℕ) (t c : Fin N → ℝ),
      1 / (2 * Real.pi) *
          (∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
            fourModeGaussSpectralWeight r) +
        (∑' n : ℕ,
          (if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0) *
            (1 / Real.pi * ∫ r : ℝ,
              trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
                Real.cos (r * Real.log n))) ≤
      1 / (2 * Real.pi) *
        ((42 / 585 : ℝ) *
          (∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r))) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_forall_fourModeGauss_add_prime_le_pole_add_l1_coercive fun N t c => ?_
  have hdom := h N t c
  have hpole : 0 ≤ (2 / Real.cos (1 / 4 : ℝ) ^ 2) * trigPacketWeight t c (Real.sqrt (7 / 4)) :=
    mul_nonneg (by positivity) (trigPacketWeight_nonneg t c _)
  linarith

end RHTower.CHMDStage12

end
