import GaloisForLFunctions.RHTower.CHMDStage17ComplexWavePacketFactorizationAndCoshSinhDecomposition

/-!
# Stage 18 of the Causal Hyperbolic–Modular Duality (CHMD) Route:
# Exact Strip Sector Cone of `specSq sechHalf`, Imaginary-Part Cauchy–Schwarz Bound for
# `complexTrigPacketWeight`, and Complexified 2-Point Half-Angle Square Factorizations

This module advances the Causal Hyperbolic–Modular Duality (CHMD) route directly on the decisive
Toeplitz sign (`sum_sum_cosineShiftFn_sechHalf_vonMangoldt_eq_tsum_complexTrigPacketWeight`) by
establishing three exact structural laws on the critical strip:

1. **Exact Norm-Square, Imaginary-Part Formula, and Strip Sector Cone of `specSq sechHalf z`
   (Section 1)**:
   - Proves the exact norm-square formula for `Complex.cosh (z / 2)` on all of $\mathbb{C}$:
     `Complex.normSq (Complex.cosh (z / 2)) = Real.cos (z.im / 2) ^ 2 + Real.sinh (z.re / 2) ^ 2`
     (`normSq_cosh_half`, `normSq_cosh_half_sq`),
     and the exact imaginary-part formula:
     `(Complex.cosh (z / 2) ^ 2).im = Real.sinh (z.re / 2) * Real.cosh (z.re / 2) * Real.sin z.im`
     (`im_cosh_half_sq`).
   - Deduces the global real, imaginary, and norm formulas for `specSq sechHalf z` on $\mathbb{C}$
     (`re_specSq_sechHalf`, `im_specSq_sechHalf`, `norm_specSq_sechHalf`), the global lower bound
     `Real.cos z.im * ‖specSq sechHalf z‖ ≤ (specSq sechHalf z).re` (`cos_mul_norm_le_re_specSq_sechHalf`),
     and on the strip `|z.im| ≤ 5 / 4` the imaginary-part bound
     `|(specSq sechHalf z).im| ≤ |Real.sin z.im| * ‖specSq sechHalf z‖`
     (`abs_im_specSq_sechHalf_le_abs_sin_mul_norm`) and the **Exact Strip Sector Cone Inequality**:
     `Real.cos z.im * |(specSq sechHalf z).im| ≤ |Real.sin z.im| * (specSq sechHalf z).re`
     (`cos_mul_abs_im_specSq_sechHalf_le_abs_sin_mul_re`).

2. **Imaginary-Part Cross Weight, Lagrange Cauchy–Schwarz Bound for `complexTrigPacketWeight`,
   and Strip Sector Lower Bound for Wave-Packet Zero Summands (Section 2)**:
   - Defines `crossTrigPacketWeight t c u v` and proves
     `(complexTrigPacketWeight t c w).im = 2 * crossTrigPacketWeight t c w.re w.im`
     (`im_complexTrigPacketWeight_eq_two_mul_cross`).
   - Proves via Lagrange's identity that
     `crossTrigPacketWeight t c u v ^ 2 ≤ coshTrigPacketWeight t c u v * sinhTrigPacketWeight t c u v`
     (`crossTrigPacketWeight_sq_le_cosh_mul_sinh`) and consequently
     `(complexTrigPacketWeight t c w).im ^ 2 ≤
       4 * coshTrigPacketWeight t c w.re w.im * sinhTrigPacketWeight t c w.re w.im`
     (`im_complexTrigPacketWeight_sq_le_four_mul_cosh_mul_sinh`).
   - Combines the Strip Sector Cone with `complexTrigPacketWeight` to prove the unconditional
     pointwise strip lower bound `re_complexTrigPacketWeight_mul_specSq_sechHalf_ge` on
     `|z.im| ≤ 5 / 4` and at every nontrivial zero `gammaOf ρ`
     (`re_complexTrigPacketWeight_mul_specSq_sechHalf_gammaOf_ge`).

3. **Complexified 2-Point Half-Angle Square Factorizations and Wave-Packet Convolution
   Annihilation against `xiCoshHalf` (Section 3)**:
   - Proves for all $w \in \mathbb{C}$ and $y \in \mathbb{R}$:
     `complexTrigPacketWeight (twoPointShift y) twoPointDiffCoeff w = 2 * (1 - Complex.cos (y * w)) = 4 * Complex.sin (y * w / 2) ^ 2`
     (`complexTrigPacketWeight_twoPointDiff`, `complexTrigPacketWeight_twoPointDiff_eq_four_mul_sin_sq`)
     and
     `complexTrigPacketWeight (twoPointShift y) twoPointSumCoeff w = 2 * (1 + Complex.cos (y * w)) = 4 * Complex.cos (y * w / 2) ^ 2`
     (`complexTrigPacketWeight_twoPointSum`, `complexTrigPacketWeight_twoPointSum_eq_four_mul_cos_sq`).
   - Deduces the unconditional zero-side half-angle square series for `2 * (F(0) ∓ F(y))`
     (`two_mul_cosineShiftFn_sechHalf_zero_sub_eq_tsum_four_sin_sq`,
     `two_mul_cosineShiftFn_sechHalf_zero_add_eq_tsum_four_cos_sq`) and the unconditional
     wave-packet convolution annihilation against `xiCoshHalf`
     (`sum_sum_integral_cosShiftKernel_xiCoshHalf_mul_cosineShiftFn_sechHalf_vonMangoldt_eq_zero`).
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped Real ComplexConjugate Nat

noncomputable section

namespace RHTower.CHMDStage18

open WeilOneSided WeilSpectral RHTower.EvenSector RHTower.WeilPolarMajorant
open RHTower.CHMDStage1 RHTower.CHMDStage2 RHTower.CHMDStage3 RHTower.CHMDStage4
open RHTower.CHMDStage11 RHTower.CHMDStage12 RHTower.CHMDStage13 RHTower.CHMDStage14
open RHTower.CHMDStage15 RHTower.CHMDStage16 RHTower.CHMDStage17
open GaloisForLFunctions.HTGeometry

/-! ## Section 1: Exact Norm-Square, Imaginary-Part Formula, and Strip Sector Cone of `specSq sechHalf z` -/

/-- **Exact Norm-Square Formula for `Complex.cosh (z / 2)`**:
for every $z \in \mathbb{C}$,
`Complex.normSq (Complex.cosh (z / 2)) = Real.cos (z.im / 2) ^ 2 + Real.sinh (z.re / 2) ^ 2`. -/
theorem normSq_cosh_half (z : ℂ) :
    Complex.normSq (Complex.cosh (z / 2)) =
      Real.cos (z.im / 2) ^ 2 + Real.sinh (z.re / 2) ^ 2 := by
  have hz : z / 2 = ((z.re / 2 : ℝ) : ℂ) + ((z.im / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [hz, cosh_ofReal_add_mul_I, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_add, add_zero, mul_one, sub_zero]
  have hch := Real.cosh_sq (z.re / 2)
  have hpyth := Real.cos_sq_add_sin_sq (z.im / 2)
  nlinarith

/-- **Exact Norm-Square Formula for `Complex.cosh (z / 2) ^ 2`**:
for every $z \in \mathbb{C}$,
`Complex.normSq (Complex.cosh (z / 2) ^ 2) = (Real.cos (z.im / 2) ^ 2 + Real.sinh (z.re / 2) ^ 2) ^ 2`. -/
theorem normSq_cosh_half_sq (z : ℂ) :
    Complex.normSq (Complex.cosh (z / 2) ^ 2) =
      (Real.cos (z.im / 2) ^ 2 + Real.sinh (z.re / 2) ^ 2) ^ 2 := by
  rw [sq, map_mul, ← sq, normSq_cosh_half]

/-- **Exact Imaginary-Part Formula for `Complex.cosh (z / 2) ^ 2`**:
for every $z \in \mathbb{C}$,
`(Complex.cosh (z / 2) ^ 2).im = Real.sinh (z.re / 2) * Real.cosh (z.re / 2) * Real.sin z.im`. -/
theorem im_cosh_half_sq (z : ℂ) :
    (Complex.cosh (z / 2) ^ 2).im =
      Real.sinh (z.re / 2) * Real.cosh (z.re / 2) * Real.sin z.im := by
  have hz : z / 2 = ((z.re / 2 : ℝ) : ℂ) + ((z.im / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [hz, cosh_ofReal_add_mul_I, sq]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_add, add_zero, mul_one, sub_zero]
  have hsin := Real.sin_two_mul (z.im / 2)
  have h2 : 2 * (z.im / 2) = z.im := by ring
  rw [h2] at hsin
  rw [hsin]
  ring

/-- **Global Cosine Lower Bound for `(Complex.cosh (z / 2) ^ 2).re`**:
for every $z \in \mathbb{C}$ (with no strip restriction),
`Real.cos z.im * Complex.normSq (Complex.cosh (z / 2)) ≤ (Complex.cosh (z / 2) ^ 2).re`. -/
theorem cos_mul_normSq_cosh_half_le_re_cosh_half_sq (z : ℂ) :
    Real.cos z.im * Complex.normSq (Complex.cosh (z / 2)) ≤ (Complex.cosh (z / 2) ^ 2).re := by
  rw [normSq_cosh_half, re_cosh_half_sq]
  have hcos : Real.cos z.im ≤ 1 := Real.cos_le_one z.im
  have hsq : 0 ≤ Real.cos (z.im / 2) ^ 2 := sq_nonneg _
  nlinarith

/-- **Strip Sine Upper Bound for `|(Complex.cosh (z / 2) ^ 2).im|`**:
for every $z \in \mathbb{C}$ with $|\operatorname{Im} z| \le 5 / 4$,
`|(Complex.cosh (z / 2) ^ 2).im| ≤ |Real.sin z.im| * Complex.normSq (Complex.cosh (z / 2))`. -/
theorem abs_im_cosh_half_sq_le_abs_sin_mul_normSq_cosh_half
    {z : ℂ} (hz : |z.im| ≤ 5 / 4) :
    |(Complex.cosh (z / 2) ^ 2).im| ≤
      |Real.sin z.im| * Complex.normSq (Complex.cosh (z / 2)) := by
  have hcos_pos : 0 ≤ Real.cos z.im := (cos_pos_of_abs_le_five_fourths hz).le
  have hns_nonneg : 0 ≤ Complex.normSq (Complex.cosh (z / 2)) := Complex.normSq_nonneg _
  have hre_ge := cos_mul_normSq_cosh_half_le_re_cosh_half_sq z
  have hre_sq :
      (Real.cos z.im * Complex.normSq (Complex.cosh (z / 2))) ^ 2 ≤
        (Complex.cosh (z / 2) ^ 2).re ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hcos_pos hns_nonneg) hre_ge 2
  have hpyth_c :
      (Complex.cosh (z / 2) ^ 2).re ^ 2 + (Complex.cosh (z / 2) ^ 2).im ^ 2 =
        Complex.normSq (Complex.cosh (z / 2)) ^ 2 := by
    have h1 := Complex.normSq_apply (Complex.cosh (z / 2) ^ 2)
    have h2 : Complex.normSq (Complex.cosh (z / 2) ^ 2) =
        Complex.normSq (Complex.cosh (z / 2)) ^ 2 := by
      rw [sq, map_mul, ← sq]
    linarith
  have hpyth_r := Real.cos_sq_add_sin_sq z.im
  have him_sq :
      (Complex.cosh (z / 2) ^ 2).im ^ 2 ≤
        (|Real.sin z.im| * Complex.normSq (Complex.cosh (z / 2))) ^ 2 := by
    rw [mul_pow, sq_abs]
    nlinarith
  have h := sq_le_sq.mp him_sq
  rwa [abs_of_nonneg (mul_nonneg (abs_nonneg _) hns_nonneg)] at h

/-- **Exact Real-Part Formula for `specSq sechHalf z`**:
for every $z \in \mathbb{C}$,
`(specSq sechHalf z).re = (Real.cos (z.im / 2) ^ 2 + Real.sinh (z.re / 2) ^ 2 * Real.cos z.im) / (Real.cos (z.im / 2) ^ 2 + Real.sinh (z.re / 2) ^ 2) ^ 2`. -/
theorem re_specSq_sechHalf (z : ℂ) :
    (specSq sechHalf z).re =
      (Real.cos (z.im / 2) ^ 2 + Real.sinh (z.re / 2) ^ 2 * Real.cos z.im) /
        (Real.cos (z.im / 2) ^ 2 + Real.sinh (z.re / 2) ^ 2) ^ 2 := by
  rw [specSq_sechHalf_eq_inv_cosh_sq, Complex.inv_re, re_cosh_half_sq, normSq_cosh_half_sq]

/-- **Exact Imaginary-Part Formula for `specSq sechHalf z`**:
for every $z \in \mathbb{C}$,
`(specSq sechHalf z).im = -(Real.sinh (z.re / 2) * Real.cosh (z.re / 2) * Real.sin z.im) / (Real.cos (z.im / 2) ^ 2 + Real.sinh (z.re / 2) ^ 2) ^ 2`. -/
theorem im_specSq_sechHalf (z : ℂ) :
    (specSq sechHalf z).im =
      -(Real.sinh (z.re / 2) * Real.cosh (z.re / 2) * Real.sin z.im) /
        (Real.cos (z.im / 2) ^ 2 + Real.sinh (z.re / 2) ^ 2) ^ 2 := by
  rw [specSq_sechHalf_eq_inv_cosh_sq, Complex.inv_im, im_cosh_half_sq, normSq_cosh_half_sq]

/-- **Exact Norm Formula for `specSq sechHalf z`**:
for every $z \in \mathbb{C}$,
`‖specSq sechHalf z‖ = (Real.cos (z.im / 2) ^ 2 + Real.sinh (z.re / 2) ^ 2)⁻¹`. -/
theorem norm_specSq_sechHalf (z : ℂ) :
    ‖specSq sechHalf z‖ = (Real.cos (z.im / 2) ^ 2 + Real.sinh (z.re / 2) ^ 2)⁻¹ := by
  rw [specSq_sechHalf_eq_inv_cosh_sq, norm_inv, norm_pow, ← Complex.normSq_eq_norm_sq,
    normSq_cosh_half]

/-- **Global Cosine Lower Bound for `(specSq sechHalf z).re`**:
for every $z \in \mathbb{C}$,
`Real.cos z.im * ‖specSq sechHalf z‖ ≤ (specSq sechHalf z).re`. -/
theorem cos_mul_norm_le_re_specSq_sechHalf (z : ℂ) :
    Real.cos z.im * ‖specSq sechHalf z‖ ≤ (specSq sechHalf z).re := by
  rw [specSq_sechHalf_eq_inv_cosh_sq, Complex.inv_re, norm_inv, norm_pow,
    ← Complex.normSq_eq_norm_sq]
  have h1 := cos_mul_normSq_cosh_half_le_re_cosh_half_sq z
  have h2 : Complex.normSq (Complex.cosh (z / 2) ^ 2) =
      Complex.normSq (Complex.cosh (z / 2)) ^ 2 := by
    rw [sq, map_mul, ← sq]
  rw [h2]
  rcases eq_or_lt_of_le (Complex.normSq_nonneg (Complex.cosh (z / 2))) with h0 | hpos
  · rw [← h0]; simp
  · rw [← div_eq_mul_inv,
      show Real.cos z.im / Complex.normSq (Complex.cosh (z / 2)) =
        (Real.cos z.im * Complex.normSq (Complex.cosh (z / 2))) /
          Complex.normSq (Complex.cosh (z / 2)) ^ 2 by
        rw [sq, mul_div_mul_right _ _ hpos.ne']]
    exact div_le_div_of_nonneg_right h1 (sq_nonneg _)

/-- **Strip Sine Upper Bound for `|(specSq sechHalf z).im|`**:
for every $z \in \mathbb{C}$ with $|\operatorname{Im} z| \le 5 / 4$,
`|(specSq sechHalf z).im| ≤ |Real.sin z.im| * ‖specSq sechHalf z‖`. -/
theorem abs_im_specSq_sechHalf_le_abs_sin_mul_norm
    {z : ℂ} (hz : |z.im| ≤ 5 / 4) :
    |(specSq sechHalf z).im| ≤ |Real.sin z.im| * ‖specSq sechHalf z‖ := by
  rw [specSq_sechHalf_eq_inv_cosh_sq, Complex.inv_im, norm_inv, norm_pow,
    ← Complex.normSq_eq_norm_sq, abs_div, abs_neg,
    abs_of_nonneg (Complex.normSq_nonneg _)]
  have h1 := abs_im_cosh_half_sq_le_abs_sin_mul_normSq_cosh_half hz
  have h2 : Complex.normSq (Complex.cosh (z / 2) ^ 2) =
      Complex.normSq (Complex.cosh (z / 2)) ^ 2 := by
    rw [sq, map_mul, ← sq]
  rw [h2]
  rcases eq_or_lt_of_le (Complex.normSq_nonneg (Complex.cosh (z / 2))) with h0 | hpos
  · rw [← h0]; simp
  · rw [← div_eq_mul_inv,
      show |Real.sin z.im| / Complex.normSq (Complex.cosh (z / 2)) =
        (|Real.sin z.im| * Complex.normSq (Complex.cosh (z / 2))) /
          Complex.normSq (Complex.cosh (z / 2)) ^ 2 by
        rw [sq, mul_div_mul_right _ _ hpos.ne']]
    exact div_le_div_of_nonneg_right h1 (sq_nonneg _)

/-- **Exact Strip Sector Cone Inequality for `specSq sechHalf z`**:
for every $z \in \mathbb{C}$ in the strip $|\operatorname{Im} z| \le 5 / 4$,
`Real.cos z.im * |(specSq sechHalf z).im| ≤ |Real.sin z.im| * (specSq sechHalf z).re`. -/
theorem cos_mul_abs_im_specSq_sechHalf_le_abs_sin_mul_re
    {z : ℂ} (hz : |z.im| ≤ 5 / 4) :
    Real.cos z.im * |(specSq sechHalf z).im| ≤
      |Real.sin z.im| * (specSq sechHalf z).re := by
  have hcos : 0 ≤ Real.cos z.im := (cos_pos_of_abs_le_five_fourths hz).le
  have hre := cos_mul_norm_le_re_specSq_sechHalf z
  have him := abs_im_specSq_sechHalf_le_abs_sin_mul_norm hz
  calc
    Real.cos z.im * |(specSq sechHalf z).im|
      ≤ Real.cos z.im * (|Real.sin z.im| * ‖specSq sechHalf z‖) :=
        mul_le_mul_of_nonneg_left him hcos
    _ = |Real.sin z.im| * (Real.cos z.im * ‖specSq sechHalf z‖) := by ring
    _ ≤ |Real.sin z.im| * (specSq sechHalf z).re :=
        mul_le_mul_of_nonneg_left hre (abs_nonneg _)

/-! ## Section 2: Imaginary-Part Cross Weight, Lagrange Cauchy–Schwarz Bound for `complexTrigPacketWeight`, and Strip Sector Lower Bound -/

/-- The cross trigonometric wave-packet weight
`(∑ i, c_i cosh(t_i v) sin(t_i u)) (∑ i, c_i sinh(t_i v) cos(t_i u)) -
 (∑ i, c_i cosh(t_i v) cos(t_i u)) (∑ i, c_i sinh(t_i v) sin(t_i u))`. -/
def crossTrigPacketWeight {N : ℕ} (t c : Fin N → ℝ) (u v : ℝ) : ℝ :=
  (∑ i : Fin N, c i * Real.cosh (t i * v) * Real.sin (t i * u)) *
    (∑ i : Fin N, c i * Real.sinh (t i * v) * Real.cos (t i * u)) -
  (∑ i : Fin N, c i * Real.cosh (t i * v) * Real.cos (t i * u)) *
    (∑ i : Fin N, c i * Real.sinh (t i * v) * Real.sin (t i * u))

/-- **Exact Imaginary-Part Formula for `complexTrigPacketWeight`**:
for every $w \in \mathbb{C}$,
`(complexTrigPacketWeight t c w).im = 2 * crossTrigPacketWeight t c w.re w.im`. -/
theorem im_complexTrigPacketWeight_eq_two_mul_cross
    {N : ℕ} (t c : Fin N → ℝ) (w : ℂ) :
    (complexTrigPacketWeight t c w).im = 2 * crossTrigPacketWeight t c w.re w.im := by
  have hcos :
      (∑ i : Fin N, (c i : ℂ) * Complex.cos ((t i : ℂ) * w)) =
        ((∑ i : Fin N, c i * Real.cosh (t i * w.im) * Real.cos (t i * w.re) : ℝ) : ℂ) -
          ((∑ i : Fin N, c i * Real.sinh (t i * w.im) * Real.sin (t i * w.re) : ℝ) : ℂ) * I := by
    rw [Complex.ofReal_sum, Complex.ofReal_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hw : (t i : ℂ) * w = ((t i * w.re : ℝ) : ℂ) + ((t i * w.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    rw [hw, cos_ofReal_add_mul_I]
    push_cast
    ring
  have hsin :
      (∑ i : Fin N, (c i : ℂ) * Complex.sin ((t i : ℂ) * w)) =
        ((∑ i : Fin N, c i * Real.cosh (t i * w.im) * Real.sin (t i * w.re) : ℝ) : ℂ) +
          ((∑ i : Fin N, c i * Real.sinh (t i * w.im) * Real.cos (t i * w.re) : ℝ) : ℂ) * I := by
    rw [Complex.ofReal_sum, Complex.ofReal_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hw : (t i : ℂ) * w = ((t i * w.re : ℝ) : ℂ) + ((t i * w.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    rw [hw, sin_ofReal_add_mul_I]
    push_cast
    ring
  unfold complexTrigPacketWeight crossTrigPacketWeight
  rw [hcos, hsin, sq, sq]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.sub_im, Complex.add_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, add_zero, zero_add, mul_one, sub_zero]
  ring

/-- **Lagrange Cauchy–Schwarz Bound for `crossTrigPacketWeight`**:
for every $u, v \in \mathbb{R}$,
`crossTrigPacketWeight t c u v ^ 2 ≤ coshTrigPacketWeight t c u v * sinhTrigPacketWeight t c u v`. -/
theorem crossTrigPacketWeight_sq_le_cosh_mul_sinh
    {N : ℕ} (t c : Fin N → ℝ) (u v : ℝ) :
    crossTrigPacketWeight t c u v ^ 2 ≤
      coshTrigPacketWeight t c u v * sinhTrigPacketWeight t c u v := by
  unfold crossTrigPacketWeight coshTrigPacketWeight sinhTrigPacketWeight
  set Ac := ∑ i : Fin N, c i * Real.cosh (t i * v) * Real.cos (t i * u)
  set As := ∑ i : Fin N, c i * Real.cosh (t i * v) * Real.sin (t i * u)
  set Bc := ∑ i : Fin N, c i * Real.sinh (t i * v) * Real.cos (t i * u)
  set Bs := ∑ i : Fin N, c i * Real.sinh (t i * v) * Real.sin (t i * u)
  have hlagrange :
      (Ac ^ 2 + As ^ 2) * (Bc ^ 2 + Bs ^ 2) - (As * Bc - Ac * Bs) ^ 2 =
        (Ac * Bc + As * Bs) ^ 2 := by ring
  have hsq : 0 ≤ (Ac * Bc + As * Bs) ^ 2 := sq_nonneg _
  linarith

/-- **Imaginary-Part Cauchy–Schwarz Bound for `complexTrigPacketWeight`**:
for every $w \in \mathbb{C}$,
`(complexTrigPacketWeight t c w).im ^ 2 ≤ 4 * coshTrigPacketWeight t c w.re w.im * sinhTrigPacketWeight t c w.re w.im`. -/
theorem im_complexTrigPacketWeight_sq_le_four_mul_cosh_mul_sinh
    {N : ℕ} (t c : Fin N → ℝ) (w : ℂ) :
    (complexTrigPacketWeight t c w).im ^ 2 ≤
      4 * coshTrigPacketWeight t c w.re w.im * sinhTrigPacketWeight t c w.re w.im := by
  rw [im_complexTrigPacketWeight_eq_two_mul_cross]
  have h := crossTrigPacketWeight_sq_le_cosh_mul_sinh t c w.re w.im
  linarith

/-- **Pointwise Strip Sector Lower Bound for Wave-Packet Zero Summands**:
for every $z \in \mathbb{C}$ with $|\operatorname{Im} z| \le 5 / 4$,
`((complexTrigPacketWeight t c (rhoC z)).re -
  (|Real.sin z.im| / Real.cos z.im) * |(complexTrigPacketWeight t c (rhoC z)).im|) * (specSq sechHalf z).re ≤
  (complexTrigPacketWeight t c (rhoC z) * specSq sechHalf z).re`. -/
theorem re_complexTrigPacketWeight_mul_specSq_sechHalf_ge
    {N : ℕ} (t c : Fin N → ℝ) {z : ℂ} (hz : |z.im| ≤ 5 / 4) :
    ((complexTrigPacketWeight t c (rhoC z)).re -
        (|Real.sin z.im| / Real.cos z.im) * |(complexTrigPacketWeight t c (rhoC z)).im|) *
      (specSq sechHalf z).re ≤
      (complexTrigPacketWeight t c (rhoC z) * specSq sechHalf z).re := by
  rw [Complex.mul_re]
  have hcos : 0 < Real.cos z.im := cos_pos_of_abs_le_five_fourths hz
  have hcone := cos_mul_abs_im_specSq_sechHalf_le_abs_sin_mul_re hz
  have hcone_div :
      |(specSq sechHalf z).im| ≤
        (|Real.sin z.im| / Real.cos z.im) * (specSq sechHalf z).re := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hcos]
    linarith
  have hprod :
      (complexTrigPacketWeight t c (rhoC z)).im * (specSq sechHalf z).im ≤
        |(complexTrigPacketWeight t c (rhoC z)).im| * |(specSq sechHalf z).im| := by
    rw [← abs_mul]
    exact le_abs_self _
  have hbound :
      |(complexTrigPacketWeight t c (rhoC z)).im| * |(specSq sechHalf z).im| ≤
        |(complexTrigPacketWeight t c (rhoC z)).im| *
          ((|Real.sin z.im| / Real.cos z.im) * (specSq sechHalf z).re) :=
    mul_le_mul_of_nonneg_left hcone_div (abs_nonneg _)
  have hring :
      ((complexTrigPacketWeight t c (rhoC z)).re -
          (|Real.sin z.im| / Real.cos z.im) * |(complexTrigPacketWeight t c (rhoC z)).im|) *
        (specSq sechHalf z).re =
        (complexTrigPacketWeight t c (rhoC z)).re * (specSq sechHalf z).re -
          |(complexTrigPacketWeight t c (rhoC z)).im| *
            ((|Real.sin z.im| / Real.cos z.im) * (specSq sechHalf z).re) := by ring
  linarith

/-- **Zero-Side Sector Lower Bound at Every Nontrivial Zero `ρ`**:
for every nontrivial zero $\rho \in \operatorname{zetaZeroConfig.carrier}$ and every finite wave
packet $(t, c)$, the zero-side summand at $\gamma_\rho = \operatorname{gammaOf} \rho$ satisfies
the strip sector cone lower bound unconditionally. -/
theorem re_complexTrigPacketWeight_mul_specSq_sechHalf_gammaOf_ge
    {N : ℕ} (t c : Fin N → ℝ) (ρ : zetaZeroConfig.carrier) :
    ((complexTrigPacketWeight t c (rhoC (Zeta23.gammaOf ρ))).re -
        (|Real.sin (Zeta23.gammaOf (ρ : ℂ)).im| / Real.cos (Zeta23.gammaOf (ρ : ℂ)).im) *
          |(complexTrigPacketWeight t c (rhoC (Zeta23.gammaOf ρ))).im|) *
      (specSq sechHalf (Zeta23.gammaOf ρ)).re ≤
      (complexTrigPacketWeight t c (rhoC (Zeta23.gammaOf ρ)) *
        specSq sechHalf (Zeta23.gammaOf ρ)).re := by
  have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hIm : |(Zeta23.gammaOf (ρ : ℂ)).im| < 1 / 2 :=
    WeilEF.abs_gammaOf_im_lt ⟨hmem.2.1, hmem.2.2⟩
  exact re_complexTrigPacketWeight_mul_specSq_sechHalf_ge t c (by linarith)

/-! ## Section 3: Complexified 2-Point Half-Angle Square Factorizations and Wave-Packet Convolution Annihilation -/

/-- **Complexified 2-Point Difference Packet Weight**:
for every $y \in \mathbb{R}$ and $w \in \mathbb{C}$,
`complexTrigPacketWeight (twoPointShift y) twoPointDiffCoeff w = 2 * (1 - Complex.cos ((y : ℂ) * w))`. -/
theorem complexTrigPacketWeight_twoPointDiff (y : ℝ) (w : ℂ) :
    complexTrigPacketWeight (twoPointShift y) twoPointDiffCoeff w =
      2 * (1 - Complex.cos ((y : ℂ) * w)) := by
  rw [complexTrigPacketWeight_eq_sum_sum_cos]
  unfold twoPointShift twoPointDiffCoeff
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, sub_self, sub_zero,
    zero_sub, Complex.ofReal_zero, Complex.ofReal_neg, zero_mul, neg_mul,
    Complex.cos_zero, Complex.cos_neg]
  push_cast
  ring

/-- **Complexified Half-Angle Sine-Squared Form of the 2-Point Difference Packet Weight**:
for every $y \in \mathbb{R}$ and $w \in \mathbb{C}$,
`complexTrigPacketWeight (twoPointShift y) twoPointDiffCoeff w = 4 * Complex.sin ((y : ℂ) * w / 2) ^ 2`. -/
theorem complexTrigPacketWeight_twoPointDiff_eq_four_mul_sin_sq (y : ℝ) (w : ℂ) :
    complexTrigPacketWeight (twoPointShift y) twoPointDiffCoeff w =
      4 * Complex.sin ((y : ℂ) * w / 2) ^ 2 := by
  rw [complexTrigPacketWeight_twoPointDiff]
  have h := Complex.cos_two_mul ((y : ℂ) * w / 2)
  have h2 : 2 * ((y : ℂ) * w / 2) = (y : ℂ) * w := by ring
  rw [h2] at h
  have hpyth := Complex.cos_sq_add_sin_sq ((y : ℂ) * w / 2)
  rw [h]
  linear_combination -4 * hpyth

/-- **Complexified 2-Point Sum Packet Weight**:
for every $y \in \mathbb{R}$ and $w \in \mathbb{C}$,
`complexTrigPacketWeight (twoPointShift y) twoPointSumCoeff w = 2 * (1 + Complex.cos ((y : ℂ) * w))`. -/
theorem complexTrigPacketWeight_twoPointSum (y : ℝ) (w : ℂ) :
    complexTrigPacketWeight (twoPointShift y) twoPointSumCoeff w =
      2 * (1 + Complex.cos ((y : ℂ) * w)) := by
  rw [complexTrigPacketWeight_eq_sum_sum_cos]
  unfold twoPointShift twoPointSumCoeff
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, sub_self, sub_zero,
    zero_sub, Complex.ofReal_zero, Complex.ofReal_neg, zero_mul, neg_mul,
    Complex.cos_zero, Complex.cos_neg]
  push_cast
  ring

/-- **Complexified Half-Angle Cosine-Squared Form of the 2-Point Sum Packet Weight**:
for every $y \in \mathbb{R}$ and $w \in \mathbb{C}$,
`complexTrigPacketWeight (twoPointShift y) twoPointSumCoeff w = 4 * Complex.cos ((y : ℂ) * w / 2) ^ 2`. -/
theorem complexTrigPacketWeight_twoPointSum_eq_four_mul_cos_sq (y : ℝ) (w : ℂ) :
    complexTrigPacketWeight (twoPointShift y) twoPointSumCoeff w =
      4 * Complex.cos ((y : ℂ) * w / 2) ^ 2 := by
  rw [complexTrigPacketWeight_twoPointSum]
  have h := Complex.cos_two_mul ((y : ℂ) * w / 2)
  have h2 : 2 * ((y : ℂ) * w / 2) = (y : ℂ) * w := by ring
  rw [h2] at h
  rw [h]
  ring

/-- **Unconditional Zero-Side Half-Angle Sine-Square Series for `2 * (cosineShiftFn Λ sechHalf 0 - cosineShiftFn Λ sechHalf y)`**:
for every $y \in \mathbb{R}$,
`2 * (cosineShiftFn Λ sechHalf 0 - cosineShiftFn Λ sechHalf y) =
  ∑' ρ, m_ρ * (4 * Complex.sin ((y : ℂ) * rhoC (gammaOf ρ) / 2) ^ 2 * specSq sechHalf (gammaOf ρ)).re`. -/
theorem two_mul_cosineShiftFn_sechHalf_zero_sub_eq_tsum_four_sin_sq (y : ℝ) :
    2 * (cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf 0 -
      cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf y) =
      ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) *
          (4 * Complex.sin ((y : ℂ) * rhoC (Zeta23.gammaOf ρ) / 2) ^ 2 *
            specSq sechHalf (Zeta23.gammaOf ρ)).re := by
  rw [← sum_sum_twoPointDiff_cosineShiftFn,
    sum_sum_cosineShiftFn_sechHalf_vonMangoldt_eq_tsum_complexTrigPacketWeight]
  refine tsum_congr fun ρ => ?_
  rw [complexTrigPacketWeight_twoPointDiff_eq_four_mul_sin_sq]

/-- **Unconditional Zero-Side Half-Angle Cosine-Square Series for `2 * (cosineShiftFn Λ sechHalf 0 + cosineShiftFn Λ sechHalf y)`**:
for every $y \in \mathbb{R}$,
`2 * (cosineShiftFn Λ sechHalf 0 + cosineShiftFn Λ sechHalf y) =
  ∑' ρ, m_ρ * (4 * Complex.cos ((y : ℂ) * rhoC (gammaOf ρ) / 2) ^ 2 * specSq sechHalf (gammaOf ρ)).re`. -/
theorem two_mul_cosineShiftFn_sechHalf_zero_add_eq_tsum_four_cos_sq (y : ℝ) :
    2 * (cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf 0 +
      cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf y) =
      ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) *
          (4 * Complex.cos ((y : ℂ) * rhoC (Zeta23.gammaOf ρ) / 2) ^ 2 *
            specSq sechHalf (Zeta23.gammaOf ρ)).re := by
  rw [← sum_sum_twoPointSum_cosineShiftFn,
    sum_sum_cosineShiftFn_sechHalf_vonMangoldt_eq_tsum_complexTrigPacketWeight]
  refine tsum_congr fun ρ => ?_
  rw [complexTrigPacketWeight_twoPointSum_eq_four_mul_cos_sq]

/-- **Unconditional Wave-Packet Convolution Annihilation against `xiCoshHalf`**:
for every finite wave packet $(t_i, c_i)_{i \in \text{Fin } N}$, the Toeplitz quadratic combination
of the shifted ground-state convolution integrals of `cosineShiftFn Λ sechHalf` against
`stripTest (specSq (rhoLift xiCoshHalf))` vanishes identically. -/
theorem sum_sum_integral_cosShiftKernel_xiCoshHalf_mul_cosineShiftFn_sechHalf_vonMangoldt_eq_zero
    {N : ℕ} (t c : Fin N → ℝ) :
    (∑ i : Fin N, ∑ j : Fin N, c i * c j *
      ∫ u : ℝ, cosShiftKernel (stripTest (specSq (rhoLift xiCoshHalf))) (t j - t i) u *
        cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf u) = 0 := by
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rw [integral_cosShiftKernel_xiCoshHalf_mul_cosineShiftFn_sechHalf_vonMangoldt_eq_zero (t j - t i),
    mul_zero]

end RHTower.CHMDStage18

end
