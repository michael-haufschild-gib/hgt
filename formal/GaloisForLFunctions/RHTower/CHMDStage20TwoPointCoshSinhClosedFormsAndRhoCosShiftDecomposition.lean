import GaloisForLFunctions.RHTower.CHMDStage19ExactCoshSinhCompletedSquareAndStripCoshDominance

/-!
# Stage 20 of the Causal Hyperbolic–Modular Duality (CHMD) Route:
# Exact Real/Imaginary Decomposition of `rhoCosShift`, Closed-Form Cosh/Sinh/Cross Weights for
# 2-Point Wave Packets, and the 2-Squares-Minus-2-Squares Decomposition

This module establishes **Stage 20** of the Causal Hyperbolic–Modular Duality (CHMD) route:

1. **Exact Real and Imaginary Parts of `Complex.cos ((y : ℂ) * w)`, `Complex.sin ((y : ℂ) * w)`,
   and `rhoCosShift y Φ z`, with Two-Sided Strip Sector Bounds for `rhoCosShift y sechHalf z`
   (Section 1)**:
   - Proves `cos_ofReal_mul`, `re_cos_ofReal_mul`, `im_cos_ofReal_mul`, `sin_ofReal_mul`,
     `re_sin_ofReal_mul`, and `im_sin_ofReal_mul` for all $y \in \mathbb{R}$ and $w \in \mathbb{C}$.
   - Proves the exact real and imaginary part decompositions of `rhoCosShift y Φ z`:
     `(rhoCosShift y Φ z).re = cos(y (rhoC z).re) cosh(y (rhoC z).im) (specSq Φ z).re +
       sin(y (rhoC z).re) sinh(y (rhoC z).im) (specSq Φ z).im` (`re_rhoCosShift_eq`)
     and `im_rhoCosShift_eq`.
   - Combines `re_rhoCosShift_eq` with the Strip Sector Cone Inequality of `CHMDStage18` to prove
     both the lower and upper strip sector bounds for `(rhoCosShift y sechHalf z).re` on
     `|z.im| ≤ 5 / 4` (`re_rhoCosShift_sechHalf_ge`, `re_rhoCosShift_sechHalf_le`).

2. **Closed-Form Formulas for `coshTrigPacketWeight`, `sinhTrigPacketWeight`, and
   `crossTrigPacketWeight` of the 2-Point Sum and Difference Wave Packets (Section 2)**:
   - Proves that for both the 2-point sum packet (`twoPointSumCoeff = ![1, 1]`) and the 2-point
     difference packet (`twoPointDiffCoeff = ![1, -1]`) with shift `twoPointShift y = ![0, y]`,
     the hyperbolic `sinh` weight is **independent of the real frequency $u$**:
     `sinhTrigPacketWeight (twoPointShift y) twoPointSumCoeff u v = Real.sinh (y * v) ^ 2`
     (`sinhTrigPacketWeight_twoPointSum`) and
     `sinhTrigPacketWeight (twoPointShift y) twoPointDiffCoeff u v = Real.sinh (y * v) ^ 2`
     (`sinhTrigPacketWeight_twoPointDiff`).
   - Proves the closed forms `coshTrigPacketWeight_twoPointSum`, `coshTrigPacketWeight_twoPointDiff`,
     `crossTrigPacketWeight_twoPointSum`, `crossTrigPacketWeight_twoPointDiff`, the phase-independent
     lower bounds `(Real.cosh (y * v) - 1) ^ 2 ≤ coshTrigPacketWeight (twoPointShift y) ... u v`
     (`cosh_sub_one_sq_le_coshTrigPacketWeight_twoPointSum`,
     `cosh_sub_one_sq_le_coshTrigPacketWeight_twoPointDiff`), and the real-part formulas
     `re_complexTrigPacketWeight_twoPointSum` and `re_complexTrigPacketWeight_twoPointDiff`.

3. **Exact 2-Squares-Minus-2-Squares Decomposition of `(complexTrigPacketWeight t c w * conj (cosh(z/2)²)).re`
   (Section 3)**:
   - Defines `posSqTrigPacketWeight t c u v Cr Ci` and `negSqTrigPacketWeight t c u v Cr Ci`
     (`posSqTrigPacketWeight_nonneg`, `negSqTrigPacketWeight_nonneg`) and proves the exact
     polynomial identity (`re_complexTrigPacketWeight_mul_conj_cosh_half_sq_eq_posSq_sub_negSq`,
     `re_complexTrigPacketWeight_mul_specSq_sechHalf_eq_posSq_sub_negSq`).
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped Real ComplexConjugate Nat

noncomputable section

namespace RHTower.CHMDStage20

open WeilOneSided WeilSpectral RHTower.EvenSector RHTower.WeilPolarMajorant
open RHTower.CHMDStage1 RHTower.CHMDStage2 RHTower.CHMDStage3 RHTower.CHMDStage4
open RHTower.CHMDStage11 RHTower.CHMDStage12 RHTower.CHMDStage13 RHTower.CHMDStage14
open RHTower.CHMDStage15 RHTower.CHMDStage16 RHTower.CHMDStage17 RHTower.CHMDStage18
open RHTower.CHMDStage19
open GaloisForLFunctions.HTGeometry

/-! ## Section 1: Exact Real/Imaginary Decomposition of `Complex.cos ((y : ℂ) * w)` and `rhoCosShift y Φ z` -/

/-- Decomposition of `Complex.cos ((y : ℂ) * w)` into real and imaginary parts for $y \in \mathbb{R}$
and $w \in \mathbb{C}$. -/
theorem cos_ofReal_mul (y : ℝ) (w : ℂ) :
    Complex.cos ((y : ℂ) * w) =
      ((Real.cos (y * w.re) * Real.cosh (y * w.im) : ℝ) : ℂ) -
        ((Real.sin (y * w.re) * Real.sinh (y * w.im) : ℝ) : ℂ) * I := by
  have hw : (y : ℂ) * w = ((y * w.re : ℝ) : ℂ) + ((y * w.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  rw [hw, cos_ofReal_add_mul_I]

theorem re_cos_ofReal_mul (y : ℝ) (w : ℂ) :
    (Complex.cos ((y : ℂ) * w)).re = Real.cos (y * w.re) * Real.cosh (y * w.im) := by
  rw [cos_ofReal_mul]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

theorem im_cos_ofReal_mul (y : ℝ) (w : ℂ) :
    (Complex.cos ((y : ℂ) * w)).im = -(Real.sin (y * w.re) * Real.sinh (y * w.im)) := by
  rw [cos_ofReal_mul]
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

/-- Decomposition of `Complex.sin ((y : ℂ) * w)` into real and imaginary parts for $y \in \mathbb{R}$
and $w \in \mathbb{C}$. -/
theorem sin_ofReal_mul (y : ℝ) (w : ℂ) :
    Complex.sin ((y : ℂ) * w) =
      ((Real.sin (y * w.re) * Real.cosh (y * w.im) : ℝ) : ℂ) +
        ((Real.cos (y * w.re) * Real.sinh (y * w.im) : ℝ) : ℂ) * I := by
  have hw : (y : ℂ) * w = ((y * w.re : ℝ) : ℂ) + ((y * w.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  rw [hw, sin_ofReal_add_mul_I]

theorem re_sin_ofReal_mul (y : ℝ) (w : ℂ) :
    (Complex.sin ((y : ℂ) * w)).re = Real.sin (y * w.re) * Real.cosh (y * w.im) := by
  rw [sin_ofReal_mul]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

theorem im_sin_ofReal_mul (y : ℝ) (w : ℂ) :
    (Complex.sin ((y : ℂ) * w)).im = Real.cos (y * w.re) * Real.sinh (y * w.im) := by
  rw [sin_ofReal_mul]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

/-- **Exact Real-Part Decomposition of `rhoCosShift y Φ z`**:
for every $y \in \mathbb{R}$, $\Phi : \mathbb{C} \to \mathbb{C}$, and $z \in \mathbb{C}$,
`(rhoCosShift y Φ z).re =
  Real.cos (y * (rhoC z).re) * Real.cosh (y * (rhoC z).im) * (specSq Φ z).re +
  Real.sin (y * (rhoC z).re) * Real.sinh (y * (rhoC z).im) * (specSq Φ z).im`. -/
theorem re_rhoCosShift_eq (y : ℝ) (Φ : ℂ → ℂ) (z : ℂ) :
    (rhoCosShift y Φ z).re =
      Real.cos (y * (rhoC z).re) * Real.cosh (y * (rhoC z).im) * (specSq Φ z).re +
        Real.sin (y * (rhoC z).re) * Real.sinh (y * (rhoC z).im) * (specSq Φ z).im := by
  unfold rhoCosShift
  rw [Complex.mul_re, re_cos_ofReal_mul, im_cos_ofReal_mul]
  ring

/-- **Exact Imaginary-Part Decomposition of `rhoCosShift y Φ z`**:
for every $y \in \mathbb{R}$, $\Phi : \mathbb{C} \to \mathbb{C}$, and $z \in \mathbb{C}$,
`(rhoCosShift y Φ z).im =
  Real.cos (y * (rhoC z).re) * Real.cosh (y * (rhoC z).im) * (specSq Φ z).im -
  Real.sin (y * (rhoC z).re) * Real.sinh (y * (rhoC z).im) * (specSq Φ z).re`. -/
theorem im_rhoCosShift_eq (y : ℝ) (Φ : ℂ → ℂ) (z : ℂ) :
    (rhoCosShift y Φ z).im =
      Real.cos (y * (rhoC z).re) * Real.cosh (y * (rhoC z).im) * (specSq Φ z).im -
        Real.sin (y * (rhoC z).re) * Real.sinh (y * (rhoC z).im) * (specSq Φ z).re := by
  unfold rhoCosShift
  rw [Complex.mul_im, re_cos_ofReal_mul, im_cos_ofReal_mul]
  ring

/-- **Pointwise Strip Sector Lower Bound for `(rhoCosShift y sechHalf z).re`**:
for every $z \in \mathbb{C}$ with $|\operatorname{Im} z| \le 5 / 4$ and every $y \in \mathbb{R}$,
`(Real.cos (y * (rhoC z).re) * Real.cosh (y * (rhoC z).im) -
  (|Real.sin z.im| / Real.cos z.im) * |Real.sin (y * (rhoC z).re) * Real.sinh (y * (rhoC z).im)|) *
  (specSq sechHalf z).re ≤ (rhoCosShift y sechHalf z).re`. -/
theorem re_rhoCosShift_sechHalf_ge {z : ℂ} (hz : |z.im| ≤ 5 / 4) (y : ℝ) :
    (Real.cos (y * (rhoC z).re) * Real.cosh (y * (rhoC z).im) -
        (|Real.sin z.im| / Real.cos z.im) *
          |Real.sin (y * (rhoC z).re) * Real.sinh (y * (rhoC z).im)|) *
      (specSq sechHalf z).re ≤
      (rhoCosShift y sechHalf z).re := by
  rw [re_rhoCosShift_eq]
  have hcos : 0 < Real.cos z.im := cos_pos_of_abs_le_five_fourths hz
  have hcone := cos_mul_abs_im_specSq_sechHalf_le_abs_sin_mul_re hz
  have hcone_div :
      |(specSq sechHalf z).im| ≤
        (|Real.sin z.im| / Real.cos z.im) * (specSq sechHalf z).re := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hcos]
    linarith
  set S := Real.sin (y * (rhoC z).re) * Real.sinh (y * (rhoC z).im)
  have hprod : -S * (specSq sechHalf z).im ≤ |S| * |(specSq sechHalf z).im| := by
    calc -S * (specSq sechHalf z).im ≤ |-S * (specSq sechHalf z).im| := le_abs_self _
      _ = |S| * |(specSq sechHalf z).im| := by rw [abs_mul, abs_neg]
  have hbound :
      |S| * |(specSq sechHalf z).im| ≤
        |S| * ((|Real.sin z.im| / Real.cos z.im) * (specSq sechHalf z).re) :=
    mul_le_mul_of_nonneg_left hcone_div (abs_nonneg _)
  have hring :
      (Real.cos (y * (rhoC z).re) * Real.cosh (y * (rhoC z).im) -
          (|Real.sin z.im| / Real.cos z.im) * |S|) * (specSq sechHalf z).re =
        Real.cos (y * (rhoC z).re) * Real.cosh (y * (rhoC z).im) * (specSq sechHalf z).re -
          |S| * ((|Real.sin z.im| / Real.cos z.im) * (specSq sechHalf z).re) := by ring
  linarith

/-- **Pointwise Strip Sector Upper Bound for `(rhoCosShift y sechHalf z).re`**:
for every $z \in \mathbb{C}$ with $|\operatorname{Im} z| \le 5 / 4$ and every $y \in \mathbb{R}$,
`(rhoCosShift y sechHalf z).re ≤
  (Real.cos (y * (rhoC z).re) * Real.cosh (y * (rhoC z).im) +
    (|Real.sin z.im| / Real.cos z.im) * |Real.sin (y * (rhoC z).re) * Real.sinh (y * (rhoC z).im)|) *
    (specSq sechHalf z).re`. -/
theorem re_rhoCosShift_sechHalf_le {z : ℂ} (hz : |z.im| ≤ 5 / 4) (y : ℝ) :
    (rhoCosShift y sechHalf z).re ≤
      (Real.cos (y * (rhoC z).re) * Real.cosh (y * (rhoC z).im) +
          (|Real.sin z.im| / Real.cos z.im) *
            |Real.sin (y * (rhoC z).re) * Real.sinh (y * (rhoC z).im)|) *
        (specSq sechHalf z).re := by
  rw [re_rhoCosShift_eq]
  have hcos : 0 < Real.cos z.im := cos_pos_of_abs_le_five_fourths hz
  have hcone := cos_mul_abs_im_specSq_sechHalf_le_abs_sin_mul_re hz
  have hcone_div :
      |(specSq sechHalf z).im| ≤
        (|Real.sin z.im| / Real.cos z.im) * (specSq sechHalf z).re := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hcos]
    linarith
  set S := Real.sin (y * (rhoC z).re) * Real.sinh (y * (rhoC z).im)
  have hprod : S * (specSq sechHalf z).im ≤ |S| * |(specSq sechHalf z).im| := by
    rw [← abs_mul]
    exact le_abs_self _
  have hbound :
      |S| * |(specSq sechHalf z).im| ≤
        |S| * ((|Real.sin z.im| / Real.cos z.im) * (specSq sechHalf z).re) :=
    mul_le_mul_of_nonneg_left hcone_div (abs_nonneg _)
  have hring :
      (Real.cos (y * (rhoC z).re) * Real.cosh (y * (rhoC z).im) +
          (|Real.sin z.im| / Real.cos z.im) * |S|) * (specSq sechHalf z).re =
        Real.cos (y * (rhoC z).re) * Real.cosh (y * (rhoC z).im) * (specSq sechHalf z).re +
          |S| * ((|Real.sin z.im| / Real.cos z.im) * (specSq sechHalf z).re) := by ring
  linarith

/-! ## Section 2: Closed-Form Cosh, Sinh, and Cross Weights for the 2-Point Sum and Difference Wave Packets -/

/-- **Closed Form of `coshTrigPacketWeight` for the 2-Point Sum Packet**:
for every $y, u, v \in \mathbb{R}$,
`coshTrigPacketWeight (twoPointShift y) twoPointSumCoeff u v =
  1 + 2 * Real.cosh (y * v) * Real.cos (y * u) + Real.cosh (y * v) ^ 2`. -/
theorem coshTrigPacketWeight_twoPointSum (y u v : ℝ) :
    coshTrigPacketWeight (twoPointShift y) twoPointSumCoeff u v =
      1 + 2 * Real.cosh (y * v) * Real.cos (y * u) + Real.cosh (y * v) ^ 2 := by
  unfold coshTrigPacketWeight twoPointShift twoPointSumCoeff
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    zero_mul, Real.cosh_zero, Real.cos_zero, Real.sin_zero, mul_one, mul_zero, zero_add, one_mul]
  have hpyth := Real.cos_sq_add_sin_sq (y * u)
  nlinarith

/-- **Closed Form of `coshTrigPacketWeight` for the 2-Point Difference Packet**:
for every $y, u, v \in \mathbb{R}$,
`coshTrigPacketWeight (twoPointShift y) twoPointDiffCoeff u v =
  1 - 2 * Real.cosh (y * v) * Real.cos (y * u) + Real.cosh (y * v) ^ 2`. -/
theorem coshTrigPacketWeight_twoPointDiff (y u v : ℝ) :
    coshTrigPacketWeight (twoPointShift y) twoPointDiffCoeff u v =
      1 - 2 * Real.cosh (y * v) * Real.cos (y * u) + Real.cosh (y * v) ^ 2 := by
  unfold coshTrigPacketWeight twoPointShift twoPointDiffCoeff
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    zero_mul, Real.cosh_zero, Real.cos_zero, Real.sin_zero, mul_one, mul_zero, zero_add,
    neg_one_mul]
  have hpyth := Real.cos_sq_add_sin_sq (y * u)
  nlinarith

/-- **Phase-Independent Closed Form of `sinhTrigPacketWeight` for the 2-Point Sum Packet**:
for every $y, u, v \in \mathbb{R}$,
`sinhTrigPacketWeight (twoPointShift y) twoPointSumCoeff u v = Real.sinh (y * v) ^ 2`. -/
theorem sinhTrigPacketWeight_twoPointSum (y u v : ℝ) :
    sinhTrigPacketWeight (twoPointShift y) twoPointSumCoeff u v =
      Real.sinh (y * v) ^ 2 := by
  unfold sinhTrigPacketWeight twoPointShift twoPointSumCoeff
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    zero_mul, Real.sinh_zero, Real.cos_zero, Real.sin_zero, mul_one, mul_zero, zero_add, one_mul]
  have hpyth := Real.cos_sq_add_sin_sq (y * u)
  nlinarith

/-- **Phase-Independent Closed Form of `sinhTrigPacketWeight` for the 2-Point Difference Packet**:
for every $y, u, v \in \mathbb{R}$,
`sinhTrigPacketWeight (twoPointShift y) twoPointDiffCoeff u v = Real.sinh (y * v) ^ 2`. -/
theorem sinhTrigPacketWeight_twoPointDiff (y u v : ℝ) :
    sinhTrigPacketWeight (twoPointShift y) twoPointDiffCoeff u v =
      Real.sinh (y * v) ^ 2 := by
  unfold sinhTrigPacketWeight twoPointShift twoPointDiffCoeff
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    zero_mul, Real.sinh_zero, Real.cos_zero, Real.sin_zero, mul_one, mul_zero, zero_add,
    neg_one_mul]
  have hpyth := Real.cos_sq_add_sin_sq (y * u)
  nlinarith

/-- **Closed Form of `crossTrigPacketWeight` for the 2-Point Sum Packet**:
for every $y, u, v \in \mathbb{R}$,
`crossTrigPacketWeight (twoPointShift y) twoPointSumCoeff u v = -(Real.sin (y * u) * Real.sinh (y * v))`. -/
theorem crossTrigPacketWeight_twoPointSum (y u v : ℝ) :
    crossTrigPacketWeight (twoPointShift y) twoPointSumCoeff u v =
      -(Real.sin (y * u) * Real.sinh (y * v)) := by
  unfold crossTrigPacketWeight twoPointShift twoPointSumCoeff
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    zero_mul, Real.cosh_zero, Real.sinh_zero, Real.cos_zero, Real.sin_zero,
    mul_one, mul_zero, zero_add, one_mul]
  ring

/-- **Closed Form of `crossTrigPacketWeight` for the 2-Point Difference Packet**:
for every $y, u, v \in \mathbb{R}$,
`crossTrigPacketWeight (twoPointShift y) twoPointDiffCoeff u v = Real.sin (y * u) * Real.sinh (y * v)`. -/
theorem crossTrigPacketWeight_twoPointDiff (y u v : ℝ) :
    crossTrigPacketWeight (twoPointShift y) twoPointDiffCoeff u v =
      Real.sin (y * u) * Real.sinh (y * v) := by
  unfold crossTrigPacketWeight twoPointShift twoPointDiffCoeff
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    zero_mul, Real.cosh_zero, Real.sinh_zero, Real.cos_zero, Real.sin_zero,
    mul_one, mul_zero, zero_add, neg_one_mul]
  ring

/-- Phase-independent lower bound `(Real.cosh (y * v) - 1) ^ 2 ≤ coshTrigPacketWeight (twoPointShift y) twoPointSumCoeff u v`. -/
theorem cosh_sub_one_sq_le_coshTrigPacketWeight_twoPointSum (y u v : ℝ) :
    (Real.cosh (y * v) - 1) ^ 2 ≤
      coshTrigPacketWeight (twoPointShift y) twoPointSumCoeff u v := by
  rw [coshTrigPacketWeight_twoPointSum]
  have hcos : -1 ≤ Real.cos (y * u) := Real.neg_one_le_cos (y * u)
  have hch : 0 ≤ Real.cosh (y * v) := (Real.cosh_pos (y * v)).le
  nlinarith

/-- Phase-independent lower bound `(Real.cosh (y * v) - 1) ^ 2 ≤ coshTrigPacketWeight (twoPointShift y) twoPointDiffCoeff u v`. -/
theorem cosh_sub_one_sq_le_coshTrigPacketWeight_twoPointDiff (y u v : ℝ) :
    (Real.cosh (y * v) - 1) ^ 2 ≤
      coshTrigPacketWeight (twoPointShift y) twoPointDiffCoeff u v := by
  rw [coshTrigPacketWeight_twoPointDiff]
  have hcos : Real.cos (y * u) ≤ 1 := Real.cos_le_one (y * u)
  have hch : 0 ≤ Real.cosh (y * v) := (Real.cosh_pos (y * v)).le
  nlinarith

/-- Real part of `complexTrigPacketWeight (twoPointShift y) twoPointSumCoeff w`. -/
theorem re_complexTrigPacketWeight_twoPointSum (y : ℝ) (w : ℂ) :
    (complexTrigPacketWeight (twoPointShift y) twoPointSumCoeff w).re =
      2 * (1 + Real.cos (y * w.re) * Real.cosh (y * w.im)) := by
  rw [complexTrigPacketWeight_twoPointSum]
  simp only [Complex.mul_re, Complex.add_re, Complex.re_ofNat, Complex.im_ofNat,
    Complex.one_re, re_cos_ofReal_mul]
  ring

/-- Real part of `complexTrigPacketWeight (twoPointShift y) twoPointDiffCoeff w`. -/
theorem re_complexTrigPacketWeight_twoPointDiff (y : ℝ) (w : ℂ) :
    (complexTrigPacketWeight (twoPointShift y) twoPointDiffCoeff w).re =
      2 * (1 - Real.cos (y * w.re) * Real.cosh (y * w.im)) := by
  rw [complexTrigPacketWeight_twoPointDiff]
  simp only [Complex.mul_re, Complex.sub_re, Complex.re_ofNat, Complex.im_ofNat,
    Complex.one_re, re_cos_ofReal_mul]
  ring

/-! ## Section 3: Exact 2-Squares-Minus-2-Squares Decomposition of `(complexTrigPacketWeight t c w * conj (cosh(z/2)²)).re` -/

/-- The positive 2-square part `(A_c C_r - B_s C_i)² + (A_s C_r + B_c C_i)²` of
`(complexTrigPacketWeight t c w * conj (cosh(z/2)²)).re`. -/
def posSqTrigPacketWeight {N : ℕ} (t c : Fin N → ℝ) (u v Cr Ci : ℝ) : ℝ :=
  ((∑ i : Fin N, c i * Real.cosh (t i * v) * Real.cos (t i * u)) * Cr -
      (∑ i : Fin N, c i * Real.sinh (t i * v) * Real.sin (t i * u)) * Ci) ^ 2 +
    ((∑ i : Fin N, c i * Real.cosh (t i * v) * Real.sin (t i * u)) * Cr +
      (∑ i : Fin N, c i * Real.sinh (t i * v) * Real.cos (t i * u)) * Ci) ^ 2

/-- The negative 2-square part `(A_c C_i + B_s C_r)² + (B_c C_r - A_s C_i)²` of
`(complexTrigPacketWeight t c w * conj (cosh(z/2)²)).re`. -/
def negSqTrigPacketWeight {N : ℕ} (t c : Fin N → ℝ) (u v Cr Ci : ℝ) : ℝ :=
  ((∑ i : Fin N, c i * Real.cosh (t i * v) * Real.cos (t i * u)) * Ci +
      (∑ i : Fin N, c i * Real.sinh (t i * v) * Real.sin (t i * u)) * Cr) ^ 2 +
    ((∑ i : Fin N, c i * Real.sinh (t i * v) * Real.cos (t i * u)) * Cr -
      (∑ i : Fin N, c i * Real.cosh (t i * v) * Real.sin (t i * u)) * Ci) ^ 2

theorem posSqTrigPacketWeight_nonneg {N : ℕ} (t c : Fin N → ℝ) (u v Cr Ci : ℝ) :
    0 ≤ posSqTrigPacketWeight t c u v Cr Ci :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem negSqTrigPacketWeight_nonneg {N : ℕ} (t c : Fin N → ℝ) (u v Cr Ci : ℝ) :
    0 ≤ negSqTrigPacketWeight t c u v Cr Ci :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- **Exact 2-Squares-Minus-2-Squares Identity**:
for every $w, z \in \mathbb{C}$,
`(complexTrigPacketWeight t c w * conj (Complex.cosh (z / 2) ^ 2)).re =
  posSqTrigPacketWeight t c w.re w.im (coshHalfRe z) (coshHalfIm z) -
  negSqTrigPacketWeight t c w.re w.im (coshHalfRe z) (coshHalfIm z)`. -/
theorem re_complexTrigPacketWeight_mul_conj_cosh_half_sq_eq_posSq_sub_negSq
    {N : ℕ} (t c : Fin N → ℝ) (w z : ℂ) :
    (complexTrigPacketWeight t c w * conj (Complex.cosh (z / 2) ^ 2)).re =
      posSqTrigPacketWeight t c w.re w.im (coshHalfRe z) (coshHalfIm z) -
        negSqTrigPacketWeight t c w.re w.im (coshHalfRe z) (coshHalfIm z) := by
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im,
    re_complexTrigPacketWeight_eq_cosh_sub_sinh, im_complexTrigPacketWeight_eq_two_mul_cross,
    re_cosh_half_sq_eq_sq_sub_sq, im_cosh_half_sq_eq_two_mul]
  unfold coshTrigPacketWeight sinhTrigPacketWeight crossTrigPacketWeight
    posSqTrigPacketWeight negSqTrigPacketWeight
  ring

/-- **Exact Rational 2-Squares-Minus-2-Squares Formula for `(complexTrigPacketWeight t c w * specSq sechHalf z).re`**:
for every $w, z \in \mathbb{C}$,
`(complexTrigPacketWeight t c w * specSq sechHalf z).re =
  (posSqTrigPacketWeight t c w.re w.im (coshHalfRe z) (coshHalfIm z) -
    negSqTrigPacketWeight t c w.re w.im (coshHalfRe z) (coshHalfIm z)) /
  Complex.normSq (Complex.cosh (z / 2)) ^ 2`. -/
theorem re_complexTrigPacketWeight_mul_specSq_sechHalf_eq_posSq_sub_negSq
    {N : ℕ} (t c : Fin N → ℝ) (w z : ℂ) :
    (complexTrigPacketWeight t c w * specSq sechHalf z).re =
      (posSqTrigPacketWeight t c w.re w.im (coshHalfRe z) (coshHalfIm z) -
        negSqTrigPacketWeight t c w.re w.im (coshHalfRe z) (coshHalfIm z)) /
      Complex.normSq (Complex.cosh (z / 2)) ^ 2 := by
  rw [re_complexTrigPacketWeight_mul_specSq_sechHalf_eq_completedSq,
    ← re_complexTrigPacketWeight_mul_conj_cosh_half_sq_eq,
    re_complexTrigPacketWeight_mul_conj_cosh_half_sq_eq_posSq_sub_negSq]

end RHTower.CHMDStage20

end
