import GaloisForLFunctions.RHTower.CHMDStage4EllipticHyperbolicClosure
import GaloisForLFunctions.HTGeometry.SechSquareConvolutionKernel

/-!
# CHMD Stage 11: Sech-Square Bridge, Trigonometric Wave-Packet Weights, and the Three-Part Spectral Decomposition of the Decisive Toeplitz Form

This module establishes **Stage 11** of the Causal Hyperbolic–Modular Duality (CHMD) route by
unifying the real Poisson-history profile `sechSqHalf (s : ℝ) = 4 e^s / (1 + e^s)² = cosh(s/2)⁻²`
(`GaloisForLFunctions.HTGeometry.SechSquareConvolutionKernel`) with the complex reference strip
function `sechHalf (z : ℂ) = (cosh(z/2))⁻¹` (`RHTower.EvenSector.EvenSectorSechRepresentation`),
and deriving the exact three-part spectral decomposition of every finite Toeplitz quadratic form
`∑ i, ∑ j, c i * c j * cosineShiftFn lam sechHalf (t j - t i)` in terms of the nonnegative
trigonometric wave-packet weight `trigPacketWeight t c ρ = (∑ i, c i cos(t_i ρ))² + (∑ i, c i sin(t_i ρ))²`:

1. **Section 1 (Exact Bridge Between `sechHalf : ℂ → ℂ` and `sechSqHalf : ℝ → ℝ` and Closed Form at `y = 0`):**
   - On the real line `r ∈ ℝ`, `sechHalf r = (cosh(r/2))⁻¹`, `‖sechHalf r‖² = sechSqHalf r`, and
     `(specSq sechHalf r).re = sechSqHalf r` (`sechHalf_ofReal`, `norm_sechHalf_ofReal_sq`,
     `specSq_sechHalf_ofReal_re`).
   - At the poles `z = ±I/2`, `sechHalf (±I/2) = (cos(1/4))⁻¹`, so
     `evenPolePart (specSq sechHalf) = 2 / cos(1/4)² > 2 > 0`
     (`evenPolePart_specSq_sechHalf`, `two_lt_evenPolePart_specSq_sechHalf`,
     `evenPolePart_specSq_sechHalf_pos`).
   - Using `sechSqHalfSymbol_of_pos`, the `n`-th prime Fourier integral of `specSq sechHalf` at
     `y = 0` has the exact strictly positive hyperbolic-cosecant closed form
     `(1 / π) ∫ r, (specSq sechHalf r).re * cos(r log n) = 4 log n / sinh(π log n) > 0` for every
     `n ≥ 2` (`primeFourierWeight_sechHalf_of_two_le`, `primeFourierWeight_sechHalf_pos`), giving
     the exact closed-form expansion of `cosineShiftFn lam sechHalf 0`
     (`cosineShiftFn_sechHalf_zero_eq`).

2. **Section 2 (The Nonnegative Trigonometric Wave-Packet Weight `trigPacketWeight t c ρ`):**
   - For any finite wave packet `t, c : Fin N → ℝ`, we define
     `trigPacketWeight t c ρ = (∑ i, c i cos(t_i ρ))² + (∑ i, c i sin(t_i ρ))² ≥ 0`.
   - We prove nonnegativity (`trigPacketWeight_nonneg`), evenness (`trigPacketWeight_neg`),
     evaluation at `0` (`trigPacketWeight_zero`), the double-sum cosine identity
     `trigPacketWeight t c ρ = ∑ i, ∑ j, c i * c j * cos((t_j - t_i) ρ)`
     (`trigPacketWeight_eq_sum_sum_cos`), and the pointwise real-line identity
     `(specSq (cosComb t c sechHalf) r + specSq (sinComb t c sechHalf) r).re = trigPacketWeight t c (√(r² + 2)) * sechSqHalf r ≥ 0`
     (`specSq_cosComb_add_sinComb_sechHalf_ofReal_re`,
     `specSq_cosComb_add_sinComb_sechHalf_ofReal_re_nonneg`).

3. **Section 3 (Exact Three-Part Spectral Decomposition of Finite Toeplitz Quadratic Forms):**
   - We prove that for every `EvenStrip Φ` and every weight `lam` with
     `|lam n| ≤ Cg √n (1 + log n)`, the pole part, archimedean part, and prime part of the
     elliptic–hyperbolic wave-packet pair `(cosComb t c Φ, sinComb t c Φ)` collapse into single
     integrals/sums against the nonnegative spectral density
     `r ↦ trigPacketWeight t c (√(r² + 2)) * ‖Φ r‖²`
     (`evenPolePart_cosComb_add_sinComb`, `evenArchPart_cosComb_add_sinComb`,
     `evenPrimePart_cosComb_add_sinComb`).
   - Specializing to `Φ = sechHalf` yields the exact three-part decomposition of the decisive
     Toeplitz quadratic form (`sum_sum_cosineShiftFn_sechHalf_eq_trigPacketWeight_parts`,
     `sum_sum_cosineShiftFn_sechHalf_vonMangoldt_eq_trigPacketWeight_parts`), in which the pole
     contribution `(2 / cos(1/4)²) * trigPacketWeight t c (√(7/4)) ≥ 0` is unconditionally
     nonnegative for every packet `(t, c)`.

4. **Section 4 (Prime-vs-Archimedean Dominance Criteria for the Decisive Toeplitz Sign and `RiemannHypothesis`):**
   - We prove that the Toeplitz quadratic form for `(t, c)` is nonnegative if and only if the
     prime series of `trigPacketWeight t c (√(r² + 2)) * sechSqHalf r` is bounded above by the
     pole + archimedean energy (`sum_sum_cosineShiftFn_sechHalf_nonneg_iff_prime_le_pole_add_arch`),
     and that pure archimedean dominance suffices unconditionally by dropping the nonnegative pole
     bonus (`sum_sum_cosineShiftFn_sechHalf_nonneg_of_prime_le_arch`,
     `riemannHypothesis_iff_forall_trigPacketWeight_sechSqHalf_prime_le_pole_add_arch`,
     `riemannHypothesis_of_forall_trigPacketWeight_sechSqHalf_prime_le_arch`).
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped ComplexConjugate Nat

noncomputable section

namespace RHTower.CHMDStage11

open WeilOneSided WeilSpectral RHTower.EvenSector RHTower.CHMDStage3 RHTower.CHMDStage4
open GaloisForLFunctions.HTGeometry

/-! ## Section 1: Exact Bridge Between `sechHalf : ℂ → ℂ` and `sechSqHalf : ℝ → ℝ` and Closed Form at `y = 0` -/

/-- On the real line, `sechHalf (r : ℂ)` is the real value `(cosh(r / 2))⁻¹`. -/
theorem sechHalf_ofReal (r : ℝ) :
    sechHalf (r : ℂ) = (((Real.cosh (r / 2))⁻¹ : ℝ) : ℂ) := by
  unfold sechHalf
  rw [show (r : ℂ) / 2 = ((r / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cosh, ← Complex.ofReal_inv]

/-- **Exact Bridge Between `sechHalf` and `sechSqHalf`**:
on the real line `r ∈ ℝ`, `‖sechHalf r‖²` equals the Poisson history profile `sechSqHalf r`. -/
theorem norm_sechHalf_ofReal_sq (r : ℝ) :
    ‖sechHalf (r : ℂ)‖ ^ 2 = sechSqHalf r := by
  rw [sechHalf_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (Real.cosh_pos (r / 2))),
    sechSqHalf_eq_cosh, Real.rpow_neg (Real.cosh_pos (r / 2)).le, Real.rpow_two, inv_pow]

/-- On the real line `r ∈ ℝ`, `(specSq sechHalf r).re = sechSqHalf r`. -/
theorem specSq_sechHalf_ofReal_re (r : ℝ) :
    (specSq sechHalf (r : ℂ)).re = sechSqHalf r := by
  rw [specSq_re_ofReal, norm_sechHalf_ofReal_sq]

/-- Strict positivity of `cos(1/4)`. -/
theorem cos_one_fourth_pos : 0 < Real.cos (1 / 4 : ℝ) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_gt_three]

/-- `cosh((I / 2) / 2) = cos(1 / 4)`. -/
theorem cosh_I_div_four :
    Complex.cosh ((I / 2 : ℂ) / 2) = (Real.cos (1 / 4 : ℝ) : ℂ) := by
  rw [show (I / 2 : ℂ) / 2 = ((1 / 4 : ℝ) : ℂ) * I by push_cast; ring,
    Complex.cosh_mul_I, Complex.ofReal_cos]

/-- Evaluation of `sechHalf` at the upper pole `I / 2`. -/
theorem sechHalf_I_div_two :
    sechHalf (I / 2) = (((Real.cos (1 / 4 : ℝ))⁻¹ : ℝ) : ℂ) := by
  unfold sechHalf
  rw [cosh_I_div_four, ← Complex.ofReal_inv]

/-- Evaluation of `sechHalf` at the lower pole `-I / 2`. -/
theorem sechHalf_neg_I_div_two :
    sechHalf (-I / 2) = (((Real.cos (1 / 4 : ℝ))⁻¹ : ℝ) : ℂ) := by
  rw [show (-I / 2 : ℂ) = -(I / 2) by ring, evenStrip_sechHalf.even, sechHalf_I_div_two]

/-- **Exact Closed Form for the Pole Part of `specSq sechHalf`**:
`evenPolePart (specSq sechHalf) = 2 / cos(1 / 4)²`. -/
theorem evenPolePart_specSq_sechHalf :
    evenPolePart (specSq sechHalf) = 2 / Real.cos (1 / 4 : ℝ) ^ 2 := by
  unfold evenPolePart specSq
  have h1 : conj (I / 2 : ℂ) = -I / 2 := by
    rw [map_div₀, Complex.conj_I, map_ofNat]
  have h2 : conj (-I / 2 : ℂ) = I / 2 := by
    rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
  rw [h1, h2, sechHalf_I_div_two, sechHalf_neg_I_div_two, Complex.conj_ofReal,
    ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_re]
  ring

/-- The pole part of `specSq sechHalf` is strictly greater than `2`. -/
theorem two_lt_evenPolePart_specSq_sechHalf :
    2 < evenPolePart (specSq sechHalf) := by
  rw [evenPolePart_specSq_sechHalf]
  have hcpos : 0 < Real.cos (1 / 4 : ℝ) := cos_one_fourth_pos
  have hlt1 : Real.cos (1 / 4 : ℝ) < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := 1 / 4) le_rfl
      (by linarith [Real.pi_gt_three]) (by norm_num)
    rwa [Real.cos_zero] at h
  have hsq : Real.cos (1 / 4 : ℝ) ^ 2 < 1 := by nlinarith
  rw [lt_div_iff₀ (sq_pos_of_pos hcpos)]
  linarith

/-- Strict positivity of `evenPolePart (specSq sechHalf)`. -/
theorem evenPolePart_specSq_sechHalf_pos :
    0 < evenPolePart (specSq sechHalf) :=
  lt_trans (by norm_num) two_lt_evenPolePart_specSq_sechHalf

/-- The cosine Fourier integral of `sechSqHalf` equals `(sechSqHalfSymbol x).re`. -/
theorem integral_sechSqHalf_mul_cos (x : ℝ) :
    (∫ r : ℝ, sechSqHalf r * Real.cos (r * x)) = (sechSqHalfSymbol x).re := by
  unfold sechSqHalfSymbol
  have hint : Integrable fun s : ℝ =>
      (sechSqHalf s : ℂ) * Complex.exp (-((x : ℂ) * (s : ℂ)) * Complex.I) := by
    refine integrable_sechSqHalf.norm.mono'
      ((Complex.continuous_ofReal.comp continuous_sechSqHalf).mul (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun s => ?_)
    rw [norm_mul, norm_exp_neg_mul_I, mul_one, Complex.norm_real]
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [← hre]
  congr 1
  funext r
  rw [show -((x : ℂ) * (r : ℂ)) * Complex.I = ((-(r * x) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-- **Exact Hyperbolic-Cosecant Closed Form for the Normalized Cosine Transform of `sechSqHalf`**:
for every `x > 0`, `(1 / π) ∫ r, sechSqHalf r * cos(r x) dr = 4 x / sinh(π x)`. -/
theorem integral_sechSqHalf_mul_cos_of_pos {x : ℝ} (hx : 0 < x) :
    (1 / Real.pi) * (∫ r : ℝ, sechSqHalf r * Real.cos (r * x)) =
      4 * x / Real.sinh (Real.pi * x) := by
  rw [integral_sechSqHalf_mul_cos, sechSqHalfSymbol_of_pos hx, Complex.ofReal_re]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **Exact Closed Form for the `n`-th Prime Fourier Weight of `specSq sechHalf` (`n ≥ 2`)**:
for every integer `n ≥ 2`,
`(1 / π) ∫ r, (specSq sechHalf r).re * cos(r log n) dr = 4 log n / sinh(π log n)`. -/
theorem primeFourierWeight_sechHalf_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    (1 / Real.pi) * (∫ r : ℝ, (specSq sechHalf r).re * Real.cos (r * Real.log n)) =
      4 * Real.log n / Real.sinh (Real.pi * Real.log n) := by
  simp_rw [specSq_sechHalf_ofReal_re]
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  exact integral_sechSqHalf_mul_cos_of_pos hlog

/-- For every integer `n ≥ 2`, the `n`-th prime Fourier weight of `specSq sechHalf` at `y = 0` is
strictly positive. -/
theorem primeFourierWeight_sechHalf_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < (1 / Real.pi) * (∫ r : ℝ, (specSq sechHalf r).re * Real.cos (r * Real.log n)) := by
  rw [primeFourierWeight_sechHalf_of_two_le hn]
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsinh : 0 < Real.sinh (Real.pi * Real.log n) := Real.sinh_pos_iff.mpr (by positivity)
  positivity

/-- The archimedean part of `specSq sechHalf` is `∫ r, sechSqHalf r * EF.gammaBracket r`. -/
theorem evenArchPart_specSq_sechHalf :
    evenArchPart (specSq sechHalf) = ∫ r : ℝ, sechSqHalf r * EF.gammaBracket r := by
  unfold evenArchPart
  simp_rw [specSq_sechHalf_ofReal_re]

/-- **Exact Closed Form for the Prime Part of `specSq sechHalf`**:
for any weight sequence `lam : ℕ → ℝ`, `evenPrimePart lam (specSq sechHalf)` is the hyperbolic-cosecant
series `∑' n, (lam n / √n) * (4 log n / sinh(π log n))`. -/
theorem evenPrimePart_specSq_sechHalf (lam : ℕ → ℝ) :
    evenPrimePart lam (specSq sechHalf) =
      ∑' n : ℕ, (if 2 ≤ n then lam n / Real.sqrt n else 0) *
        (4 * Real.log n / Real.sinh (Real.pi * Real.log n)) := by
  unfold evenPrimePart
  refine tsum_congr fun n => ?_
  by_cases hn : 2 ≤ n
  · rw [if_pos hn, primeFourierWeight_sechHalf_of_two_le hn]
  · simp [hn]

/-- **Exact Closed Form for `cosineShiftFn lam sechHalf 0` (`evenWeilDensity lam (specSq sechHalf)`)**:
at `y = 0`, `cosineShiftFn lam sechHalf 0` decomposes into `2 / cos(1/4)²`, the `sechSqHalf`
archimedean integral, and the `4 log n / sinh(π log n)` prime series. -/
theorem cosineShiftFn_sechHalf_zero_eq (lam : ℕ → ℝ) :
    cosineShiftFn lam sechHalf 0 =
      2 / Real.cos (1 / 4 : ℝ) ^ 2 +
        1 / (2 * Real.pi) * (∫ r : ℝ, sechSqHalf r * EF.gammaBracket r) -
        ∑' n : ℕ, (if 2 ≤ n then lam n / Real.sqrt n else 0) *
          (4 * Real.log n / Real.sinh (Real.pi * Real.log n)) := by
  have h0 : rhoCosShift 0 sechHalf = specSq sechHalf := by
    funext z; unfold rhoCosShift; simp
  unfold cosineShiftFn
  rw [h0, evenWeilDensity_eq_parts, evenPolePart_specSq_sechHalf,
    evenArchPart_specSq_sechHalf, evenPrimePart_specSq_sechHalf]

/-! ## Section 2: The Nonnegative Trigonometric Wave-Packet Weight `trigPacketWeight t c ρ` -/

/-- **The Nonnegative Trigonometric Wave-Packet Weight**:
for a finite wave packet `t, c : Fin N → ℝ` and spectral parameter `ρ ∈ ℝ`,
`trigPacketWeight t c ρ = (∑ i, c i cos(t_i ρ))² + (∑ i, c i sin(t_i ρ))²`. -/
def trigPacketWeight {N : ℕ} (t c : Fin N → ℝ) (ρ : ℝ) : ℝ :=
  (∑ i, c i * Real.cos (t i * ρ)) ^ 2 + (∑ i, c i * Real.sin (t i * ρ)) ^ 2

/-- Unconditional nonnegativity of `trigPacketWeight t c ρ` for all `ρ ∈ ℝ`. -/
theorem trigPacketWeight_nonneg {N : ℕ} (t c : Fin N → ℝ) (ρ : ℝ) :
    0 ≤ trigPacketWeight t c ρ := by
  unfold trigPacketWeight
  positivity

/-- Evenness of `trigPacketWeight t c`. -/
theorem trigPacketWeight_neg {N : ℕ} (t c : Fin N → ℝ) (ρ : ℝ) :
    trigPacketWeight t c (-ρ) = trigPacketWeight t c ρ := by
  unfold trigPacketWeight
  have hcos : (∑ i, c i * Real.cos (t i * -ρ)) = ∑ i, c i * Real.cos (t i * ρ) :=
    Finset.sum_congr rfl fun i _ => by rw [mul_neg, Real.cos_neg]
  have hsin : (∑ i, c i * Real.sin (t i * -ρ)) = -(∑ i, c i * Real.sin (t i * ρ)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_neg, Real.sin_neg, mul_neg]
  rw [hcos, hsin, neg_sq]

/-- At `ρ = 0`, `trigPacketWeight t c 0 = (∑ i, c i)²`. -/
theorem trigPacketWeight_zero {N : ℕ} (t c : Fin N → ℝ) :
    trigPacketWeight t c 0 = (∑ i, c i) ^ 2 := by
  unfold trigPacketWeight
  simp

/-- **Double-Sum Cosine Expansion of `trigPacketWeight`**:
`trigPacketWeight t c ρ = ∑ i, ∑ j, c i * c j * cos((t j - t i) * ρ)`. -/
theorem trigPacketWeight_eq_sum_sum_cos {N : ℕ} (t c : Fin N → ℝ) (ρ : ℝ) :
    trigPacketWeight t c ρ =
      ∑ i, ∑ j, c i * c j * Real.cos ((t j - t i) * ρ) := by
  unfold trigPacketWeight
  rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (t j - t i) * ρ = t j * ρ - t i * ρ by ring, Real.cos_sub]
  ring

/-- Continuity of `trigPacketWeight t c : ℝ → ℝ`. -/
theorem continuous_trigPacketWeight {N : ℕ} (t c : Fin N → ℝ) :
    Continuous (trigPacketWeight t c) := by
  unfold trigPacketWeight
  fun_prop

/-- **Pointwise Real-Line Identity for `specSq (cosComb t c Φ) + specSq (sinComb t c Φ)`**:
for any `Φ : ℂ → ℂ` and `r ∈ ℝ`, the real part of the combined spectral square on the real line is
`trigPacketWeight t c (√(r² + 2)) * ‖Φ r‖²`. -/
theorem specSq_cosComb_add_sinComb_ofReal_re {N : ℕ} (t c : Fin N → ℝ) (Φ : ℂ → ℂ) (r : ℝ) :
    (specSq (cosComb t c Φ) r + specSq (sinComb t c Φ) r).re =
      trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * ‖Φ r‖ ^ 2 := by
  have hz : |((r : ℂ)).im| < Real.sqrt 2 := by simp
  rw [specSq_cosComb_add_specSq_sinComb t c Φ hz, Complex.re_sum, Finset.sum_product]
  simp_rw [Complex.re_ofReal_mul, cosShift_ofReal_re]
  rw [trigPacketWeight_eq_sum_sum_cos, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Pointwise Real-Line Identity for `sechHalf`**:
on the real line `r ∈ ℝ`, `(specSq (cosComb t c sechHalf) r + specSq (sinComb t c sechHalf) r).re`
equals the nonnegative product `trigPacketWeight t c (√(r² + 2)) * sechSqHalf r`. -/
theorem specSq_cosComb_add_sinComb_sechHalf_ofReal_re {N : ℕ} (t c : Fin N → ℝ) (r : ℝ) :
    (specSq (cosComb t c sechHalf) r + specSq (sinComb t c sechHalf) r).re =
      trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r := by
  rw [specSq_cosComb_add_sinComb_ofReal_re, norm_sechHalf_ofReal_sq]

/-- Pointwise nonnegativity of `(specSq (cosComb t c sechHalf) r + specSq (sinComb t c sechHalf) r).re`
on the real line `r ∈ ℝ`. -/
theorem specSq_cosComb_add_sinComb_sechHalf_ofReal_re_nonneg {N : ℕ} (t c : Fin N → ℝ) (r : ℝ) :
    0 ≤ (specSq (cosComb t c sechHalf) r + specSq (sinComb t c sechHalf) r).re := by
  rw [specSq_cosComb_add_sinComb_sechHalf_ofReal_re]
  exact mul_nonneg (trigPacketWeight_nonneg t c _) (sechSqHalf_pos r).le

/-! ## Section 3: Exact Three-Part Spectral Decomposition of Finite Toeplitz Quadratic Forms -/

/-- The pole part of `rhoCosShift y Φ` is `cos(y √(7/4)) * evenPolePart (specSq Φ)`. -/
theorem evenPolePart_rhoCosShift (y : ℝ) (Φ : ℂ → ℂ) :
    evenPolePart (rhoCosShift y Φ) =
      Real.cos (y * Real.sqrt (7 / 4)) * evenPolePart (specSq Φ) := by
  unfold evenPolePart rhoCosShift
  rw [rhoC_I_div_two, rhoC_neg_I_div_two, ← mul_add, ← Complex.ofReal_mul,
    ← Complex.ofReal_cos, Complex.re_ofReal_mul]

/-- The pole part of `rhoCosShift y sechHalf` is `(2 / cos(1/4)²) * cos(y √(7/4))`. -/
theorem evenPolePart_rhoCosShift_sechHalf (y : ℝ) :
    evenPolePart (rhoCosShift y sechHalf) =
      (2 / Real.cos (1 / 4 : ℝ) ^ 2) * Real.cos (y * Real.sqrt (7 / 4)) := by
  rw [evenPolePart_rhoCosShift, evenPolePart_specSq_sechHalf, mul_comm]

/-- The archimedean part of `rhoCosShift y Φ` is
`∫ r, cos(y √(r² + 2)) * ‖Φ r‖² * EF.gammaBracket r`. -/
theorem evenArchPart_rhoCosShift (y : ℝ) (Φ : ℂ → ℂ) :
    evenArchPart (rhoCosShift y Φ) =
      ∫ r : ℝ, Real.cos (y * Real.sqrt (r ^ 2 + 2)) * ‖Φ r‖ ^ 2 * EF.gammaBracket r := by
  unfold evenArchPart
  simp_rw [cosShift_ofReal_re]

/-- The archimedean part of `rhoCosShift y sechHalf` is
`∫ r, cos(y √(r² + 2)) * sechSqHalf r * EF.gammaBracket r`. -/
theorem evenArchPart_rhoCosShift_sechHalf (y : ℝ) :
    evenArchPart (rhoCosShift y sechHalf) =
      ∫ r : ℝ, Real.cos (y * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * EF.gammaBracket r := by
  rw [evenArchPart_rhoCosShift]
  simp_rw [norm_sechHalf_ofReal_sq]

/-- **Double-Sum Pole Identity for `rhoCosShift`**:
`∑ i, ∑ j, c i * c j * evenPolePart (rhoCosShift (t j - t i) Φ) = trigPacketWeight t c (√(7/4)) * evenPolePart (specSq Φ)`. -/
theorem sum_sum_evenPolePart_rhoCosShift {N : ℕ} (t c : Fin N → ℝ) (Φ : ℂ → ℂ) :
    (∑ i, ∑ j, c i * c j * evenPolePart (rhoCosShift (t j - t i) Φ)) =
      trigPacketWeight t c (Real.sqrt (7 / 4)) * evenPolePart (specSq Φ) := by
  simp_rw [evenPolePart_rhoCosShift]
  rw [trigPacketWeight_eq_sum_sum_cos, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Combined Pole Part of `cosComb` and `sinComb`**:
`evenPolePart (specSq (cosComb t c Φ)) + evenPolePart (specSq (sinComb t c Φ)) = trigPacketWeight t c (√(7/4)) * evenPolePart (specSq Φ)`. -/
theorem evenPolePart_cosComb_add_sinComb {N : ℕ} (t c : Fin N → ℝ) (Φ : ℂ → ℂ) :
    evenPolePart (specSq (cosComb t c Φ)) + evenPolePart (specSq (sinComb t c Φ)) =
      trigPacketWeight t c (Real.sqrt (7 / 4)) * evenPolePart (specSq Φ) := by
  have hI1 : |(I / 2 : ℂ).im| < Real.sqrt 2 := abs_im_lt_sqrt_two (by norm_num [abs_of_pos])
  have hI2 : |(-I / 2 : ℂ).im| < Real.sqrt 2 := abs_im_lt_sqrt_two (by norm_num [abs_of_pos])
  have hcomb : evenPolePart (specSq (cosComb t c Φ)) + evenPolePart (specSq (sinComb t c Φ)) =
      evenPolePart (fun z => specSq (cosComb t c Φ) z + specSq (sinComb t c Φ) z) := by
    unfold evenPolePart
    rw [← Complex.add_re]
    congr 1
    ring
  rw [hcomb]
  dsimp only [evenPolePart]
  rw [specSq_cosComb_add_specSq_sinComb t c Φ hI1,
    specSq_cosComb_add_specSq_sinComb t c Φ hI2,
    ← Finset.sum_add_distrib, Complex.re_sum, Finset.sum_product]
  have hterm : ∀ i j : Fin N,
      (((c i * c j : ℝ) : ℂ) * rhoCosShift (t j - t i) Φ (I / 2) +
        ((c i * c j : ℝ) : ℂ) * rhoCosShift (t j - t i) Φ (-I / 2)).re =
        c i * c j * evenPolePart (rhoCosShift (t j - t i) Φ) := fun i j => by
    unfold evenPolePart
    rw [← mul_add, Complex.re_ofReal_mul]
  simp_rw [hterm]
  exact sum_sum_evenPolePart_rhoCosShift t c Φ

/-- **Combined Pole Part of `cosComb` and `sinComb` for `sechHalf`**:
equals `(2 / cos(1/4)²) * trigPacketWeight t c (√(7/4))`. -/
theorem evenPolePart_cosComb_add_sinComb_sechHalf {N : ℕ} (t c : Fin N → ℝ) :
    evenPolePart (specSq (cosComb t c sechHalf)) + evenPolePart (specSq (sinComb t c sechHalf)) =
      (2 / Real.cos (1 / 4 : ℝ) ^ 2) * trigPacketWeight t c (Real.sqrt (7 / 4)) := by
  rw [evenPolePart_cosComb_add_sinComb, evenPolePart_specSq_sechHalf, mul_comm]

/-- **Unconditional Nonnegativity of the Combined Pole Part for `sechHalf`**:
for every finite packet `(t, c)`, the pole contribution to the `sechHalf` Toeplitz form is `≥ 0`. -/
theorem evenPolePart_cosComb_add_sinComb_sechHalf_nonneg {N : ℕ} (t c : Fin N → ℝ) :
    0 ≤ evenPolePart (specSq (cosComb t c sechHalf)) +
      evenPolePart (specSq (sinComb t c sechHalf)) := by
  rw [evenPolePart_cosComb_add_sinComb_sechHalf]
  exact mul_nonneg (by positivity) (trigPacketWeight_nonneg t c _)

/-- **Combined Archimedean Part of `cosComb` and `sinComb`**:
for any `EvenStrip Φ`, the sum of the archimedean parts of `specSq (cosComb t c Φ)` and
`specSq (sinComb t c Φ)` is `∫ r, trigPacketWeight t c (√(r² + 2)) * ‖Φ r‖² * EF.gammaBracket r`. -/
theorem evenArchPart_cosComb_add_sinComb {Φ : ℂ → ℂ} (hΦ : EvenStrip Φ) {N : ℕ}
    (t c : Fin N → ℝ) :
    evenArchPart (specSq (cosComb t c Φ)) + evenArchPart (specSq (sinComb t c Φ)) =
      ∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * ‖Φ r‖ ^ 2 * EF.gammaBracket r := by
  have hA := goodDensity_specSq (evenStrip_cosComb t c hΦ)
  have hB := goodDensity_specSq (evenStrip_sinComb t c hΦ)
  unfold evenArchPart
  rw [← integral_add hA.integrable_gammaBracket hB.integrable_gammaBracket]
  congr 1
  funext r
  rw [← add_mul, ← Complex.add_re, specSq_cosComb_add_sinComb_ofReal_re]

/-- **Combined Prime Part of `cosComb` and `sinComb`**:
for any `EvenStrip Φ` and `lam` with `|lam n| ≤ Cg √n (1 + log n)`, the sum of the prime parts of
`specSq (cosComb t c Φ)` and `specSq (sinComb t c Φ)` equals the prime series of the nonnegative
density `r ↦ trigPacketWeight t c (√(r² + 2)) * ‖Φ r‖²`. -/
theorem evenPrimePart_cosComb_add_sinComb {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {Φ : ℂ → ℂ}
    (hΦ : EvenStrip Φ) {N : ℕ} (t c : Fin N → ℝ) :
    evenPrimePart lam (specSq (cosComb t c Φ)) + evenPrimePart lam (specSq (sinComb t c Φ)) =
      ∑' n : ℕ, (if 2 ≤ n then lam n / Real.sqrt n else 0) *
        (1 / Real.pi * ∫ r : ℝ,
          trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * ‖Φ r‖ ^ 2 * Real.cos (r * Real.log n)) := by
  have hA := goodDensity_specSq (evenStrip_cosComb t c hΦ)
  have hB := goodDensity_specSq (evenStrip_sinComb t c hΦ)
  unfold evenPrimePart
  rw [← Summable.tsum_add (hA.summable_prime hg) (hB.summable_prime hg)]
  refine tsum_congr fun n => ?_
  rw [← mul_add, ← mul_add, ← integral_add (hA.integrable_cos _) (hB.integrable_cos _)]
  congr 3
  funext r
  rw [← add_mul, ← Complex.add_re, specSq_cosComb_add_sinComb_ofReal_re]

/-- **Exact Three-Part Spectral Decomposition of the Finite Toeplitz Form (`sum_sum_cosineShiftFn`)**:
for any `lam` with `|lam n| ≤ Cg √n (1 + log n)` and any `EvenStrip Φ`, the finite Toeplitz
quadratic form `∑ i, ∑ j, c i * c j * cosineShiftFn lam Φ (t j - t i)` decomposes into the pole,
archimedean, and prime pairings of `trigPacketWeight t c (√(r² + 2)) * ‖Φ r‖²`. -/
theorem sum_sum_cosineShiftFn_eq_trigPacketWeight_parts {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {Φ : ℂ → ℂ}
    (hΦ : EvenStrip Φ) {N : ℕ} (t c : Fin N → ℝ) :
    (∑ i, ∑ j, c i * c j * cosineShiftFn lam Φ (t j - t i)) =
      trigPacketWeight t c (Real.sqrt (7 / 4)) * evenPolePart (specSq Φ) +
        1 / (2 * Real.pi) *
          (∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * ‖Φ r‖ ^ 2 * EF.gammaBracket r) -
        ∑' n : ℕ, (if 2 ≤ n then lam n / Real.sqrt n else 0) *
          (1 / Real.pi * ∫ r : ℝ,
            trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * ‖Φ r‖ ^ 2 * Real.cos (r * Real.log n)) := by
  rw [sum_sum_cosineShiftFn_eq_add_evenWeilDensity_unconditional hg hΦ t c,
    evenWeilDensity_eq_parts, evenWeilDensity_eq_parts,
    show ∀ a₁ b₁ c₁ a₂ b₂ d₂ : ℝ,
      (a₁ + 1 / (2 * Real.pi) * b₁ - c₁) + (a₂ + 1 / (2 * Real.pi) * b₂ - d₂) =
        (a₁ + a₂) + 1 / (2 * Real.pi) * (b₁ + b₂) - (c₁ + d₂) from fun _ _ _ _ _ _ => by ring,
    evenPolePart_cosComb_add_sinComb,
    evenArchPart_cosComb_add_sinComb hΦ,
    evenPrimePart_cosComb_add_sinComb hg hΦ]

/-- **Exact Three-Part Spectral Decomposition of the `sechHalf` Toeplitz Form**:
for any `lam` with `|lam n| ≤ Cg √n (1 + log n)`, the `sechHalf` Toeplitz quadratic form expands
explicitly in terms of `trigPacketWeight t c` and `sechSqHalf`. -/
theorem sum_sum_cosineShiftFn_sechHalf_eq_trigPacketWeight_parts {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {N : ℕ}
    (t c : Fin N → ℝ) :
    (∑ i, ∑ j, c i * c j * cosineShiftFn lam sechHalf (t j - t i)) =
      (2 / Real.cos (1 / 4 : ℝ) ^ 2) * trigPacketWeight t c (Real.sqrt (7 / 4)) +
        1 / (2 * Real.pi) *
          (∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * EF.gammaBracket r) -
        ∑' n : ℕ, (if 2 ≤ n then lam n / Real.sqrt n else 0) *
          (1 / Real.pi * ∫ r : ℝ,
            trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * Real.cos (r * Real.log n)) := by
  rw [sum_sum_cosineShiftFn_eq_trigPacketWeight_parts hg evenStrip_sechHalf t c,
    evenPolePart_specSq_sechHalf, mul_comm (trigPacketWeight t c _)]
  simp_rw [norm_sechHalf_ofReal_sq]

/-- **Exact Three-Part Spectral Decomposition of the Decisive `Λ` Toeplitz Form**:
specializing `sum_sum_cosineShiftFn_sechHalf_eq_trigPacketWeight_parts` unconditionally to the
von Mangoldt weight `lam = Λ`. -/
theorem sum_sum_cosineShiftFn_sechHalf_vonMangoldt_eq_trigPacketWeight_parts {N : ℕ}
    (t c : Fin N → ℝ) :
    (∑ i, ∑ j, c i * c j *
        cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf (t j - t i)) =
      (2 / Real.cos (1 / 4 : ℝ) ^ 2) * trigPacketWeight t c (Real.sqrt (7 / 4)) +
        1 / (2 * Real.pi) *
          (∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * EF.gammaBracket r) -
        ∑' n : ℕ,
          (if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0) *
            (1 / Real.pi * ∫ r : ℝ,
              trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
                Real.cos (r * Real.log n)) :=
  sum_sum_cosineShiftFn_sechHalf_eq_trigPacketWeight_parts
    abs_vonMangoldt_le_sqrt_mul_one_add_log t c

/-! ## Section 4: Prime-vs-Archimedean Dominance Criteria for the Decisive Toeplitz Sign and `RiemannHypothesis` -/

/-- **Prime-vs-(Pole + Archimedean) Characterization of the `sechHalf` Toeplitz Sign**:
for any `lam` with `|lam n| ≤ Cg √n (1 + log n)` and any wave packet `(t, c)`, the Toeplitz
quadratic form is nonnegative if and only if the prime series of
`trigPacketWeight t c (√(r² + 2)) * sechSqHalf r` is bounded above by the pole + archimedean energy. -/
theorem sum_sum_cosineShiftFn_sechHalf_nonneg_iff_prime_le_pole_add_arch {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {N : ℕ}
    (t c : Fin N → ℝ) :
    0 ≤ (∑ i, ∑ j, c i * c j * cosineShiftFn lam sechHalf (t j - t i)) ↔
      (∑' n : ℕ, (if 2 ≤ n then lam n / Real.sqrt n else 0) *
        (1 / Real.pi * ∫ r : ℝ,
          trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * Real.cos (r * Real.log n))) ≤
        (2 / Real.cos (1 / 4 : ℝ) ^ 2) * trigPacketWeight t c (Real.sqrt (7 / 4)) +
          1 / (2 * Real.pi) *
            (∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * EF.gammaBracket r) := by
  rw [sum_sum_cosineShiftFn_sechHalf_eq_trigPacketWeight_parts hg t c, sub_nonneg]

/-- **Pole-Bonus Sufficiency for the `sechHalf` Toeplitz Sign**:
because `(2 / cos(1/4)²) * trigPacketWeight t c (√(7/4)) ≥ 0` unconditionally, bounding the prime
series above by the archimedean integral alone implies nonnegativity of the Toeplitz quadratic form
with a bonus margin of `(2 / cos(1/4)²) * trigPacketWeight t c (√(7/4)) ≥ 0`. -/
theorem sum_sum_cosineShiftFn_sechHalf_nonneg_of_prime_le_arch {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {N : ℕ}
    (t c : Fin N → ℝ)
    (hdom : (∑' n : ℕ, (if 2 ≤ n then lam n / Real.sqrt n else 0) *
        (1 / Real.pi * ∫ r : ℝ,
          trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * Real.cos (r * Real.log n))) ≤
      1 / (2 * Real.pi) *
        (∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * EF.gammaBracket r)) :
    (2 / Real.cos (1 / 4 : ℝ) ^ 2) * trigPacketWeight t c (Real.sqrt (7 / 4)) ≤
      ∑ i, ∑ j, c i * c j * cosineShiftFn lam sechHalf (t j - t i) := by
  rw [sum_sum_cosineShiftFn_sechHalf_eq_trigPacketWeight_parts hg t c]
  linarith

/-- **Exact `trigPacketWeight` / `sechSqHalf` Dominance Equivalence for `RiemannHypothesis`**:
`RiemannHypothesis` holds if and only if for every finite wave packet `t, c : Fin N → ℝ`, the
prime series of the nonnegative spectral density `trigPacketWeight t c (√(r² + 2)) * sechSqHalf r`
is bounded above by the pole + archimedean energy. -/
theorem riemannHypothesis_iff_forall_trigPacketWeight_sechSqHalf_prime_le_pole_add_arch :
    RiemannHypothesis ↔
      ∀ (N : ℕ) (t c : Fin N → ℝ),
        (∑' n : ℕ,
          (if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0) *
            (1 / Real.pi * ∫ r : ℝ,
              trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
                Real.cos (r * Real.log n))) ≤
          (2 / Real.cos (1 / 4 : ℝ) ^ 2) * trigPacketWeight t c (Real.sqrt (7 / 4)) +
            1 / (2 * Real.pi) *
              (∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
                EF.gammaBracket r) := by
  rw [riemannHypothesis_iff_forall_sum_sum_cosineShiftFn_sechHalf_nonneg]
  exact forall_congr' fun N => forall_congr' fun t => forall_congr' fun c =>
    sum_sum_cosineShiftFn_sechHalf_nonneg_iff_prime_le_pole_add_arch
      abs_vonMangoldt_le_sqrt_mul_one_add_log t c

/-- **Pure Archimedean Dominance Sufficiency for `RiemannHypothesis` on `sechSqHalf` Wave Packets**:
if for every finite wave packet `(t, c)`, the prime series of
`trigPacketWeight t c (√(r² + 2)) * sechSqHalf r` is bounded above by the archimedean integral
`(1 / 2π) ∫ r, trigPacketWeight t c (√(r² + 2)) * sechSqHalf r * EF.gammaBracket r`, then
`RiemannHypothesis` holds unconditionally. -/
theorem riemannHypothesis_of_forall_trigPacketWeight_sechSqHalf_prime_le_arch
    (h : ∀ (N : ℕ) (t c : Fin N → ℝ),
      (∑' n : ℕ,
        (if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0) *
          (1 / Real.pi * ∫ r : ℝ,
            trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
              Real.cos (r * Real.log n))) ≤
        1 / (2 * Real.pi) *
          (∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
            EF.gammaBracket r)) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_forall_trigPacketWeight_sechSqHalf_prime_le_pole_add_arch]
  intro N t c
  have hdom := h N t c
  have hpole : 0 ≤ (2 / Real.cos (1 / 4 : ℝ) ^ 2) * trigPacketWeight t c (Real.sqrt (7 / 4)) :=
    mul_nonneg (by positivity) (trigPacketWeight_nonneg t c _)
  linarith

end RHTower.CHMDStage11

end
