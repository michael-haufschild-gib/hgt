import GaloisForLFunctions.RHTower.CHMDStage18StripSectorConeAndTwoPointSquareFactorization

/-!
# Stage 19 of the Causal Hyperbolic–Modular Duality (CHMD) Route:
# Exact Completed-Square Identity for `complexTrigPacketWeight * star (cosh(z/2)²)`,
# Rational-Hyperbolic Cosh–Sinh Dominance on the Critical Strip, and Pointwise Zero-Side
# Sufficiency Criteria for the Decisive Toeplitz Sign

This module establishes **Stage 19** of the Causal Hyperbolic–Modular Duality (CHMD) route by
replacing square-root / Cauchy–Schwarz estimates on the imaginary part of `complexTrigPacketWeight`
with an **exact polynomial completed-square identity**:

1. **Exact Half-Angle Decomposition of `Complex.cosh (z / 2)` and Master Completed-Square Identity
   (Section 1)**:
   - Defines `coshHalfRe z = cosh(z.re / 2) * cos(z.im / 2)` and
     `coshHalfIm z = sinh(z.re / 2) * sin(z.im / 2)`, proving
     `Complex.cosh (z / 2) = coshHalfRe z + coshHalfIm z * I` (`cosh_half_eq`),
     `Complex.normSq (Complex.cosh (z / 2)) = coshHalfRe z ^ 2 + coshHalfIm z ^ 2`
     (`normSq_cosh_half_eq_sq_add_sq`),
     `(Complex.cosh (z / 2) ^ 2).re = coshHalfRe z ^ 2 - coshHalfIm z ^ 2`
     (`re_cosh_half_sq_eq_sq_sub_sq`), and
     `(Complex.cosh (z / 2) ^ 2).im = 2 * coshHalfRe z * coshHalfIm z`
     (`im_cosh_half_sq_eq_two_mul`).
   - Defines the nonnegative completed-square remainder
     `completedSqTrigPacketRemainder t c u v Cr Ci` (`completedSqTrigPacketRemainder_nonneg`) and
     proves the **Master Polynomial Completed-Square Identity**
     (`re_complexTrigPacketWeight_mul_conj_cosh_half_sq_eq`):
     for every $w, z \in \mathbb{C}$,
     `(complexTrigPacketWeight t c w * conj (Complex.cosh (z / 2) ^ 2)).re =
       coshTrigPacketWeight t c w.re w.im * (coshHalfRe z ^ 2 - 3 * coshHalfIm z ^ 2) -
       sinhTrigPacketWeight t c w.re w.im * (3 * coshHalfRe z ^ 2 - coshHalfIm z ^ 2) +
       completedSqTrigPacketRemainder t c w.re w.im (coshHalfRe z) (coshHalfIm z)`.
   - Dividing by `Complex.normSq (Complex.cosh (z / 2) ^ 2)` yields the exact rational-hyperbolic
     identity (`re_complexTrigPacketWeight_mul_specSq_sechHalf_eq_completedSq`) and lower bound
     (`re_complexTrigPacketWeight_mul_specSq_sechHalf_ge_coshHalfRe_sub_three_coshHalfIm`) on all of
     $\mathbb{C}$.

2. **Exact Trigonometric–Hyperbolic Formulas for `coshHalfRe z ^ 2 - 3 * coshHalfIm z ^ 2` and
   Global Norm-Multiplied Cosh–Sinh Dominance Lower Bound (Section 2)**:
   - Proves for all $z \in \mathbb{C}$:
     `coshHalfRe z ^ 2 - 3 * coshHalfIm z ^ 2 = Real.cos (z.im / 2) ^ 2 + Real.sinh (z.re / 2) ^ 2 * (2 * Real.cos z.im - 1)`
     (`coshHalfRe_sq_sub_three_coshHalfIm_sq`) and
     `3 * coshHalfRe z ^ 2 - coshHalfIm z ^ 2 = 3 * Real.cos (z.im / 2) ^ 2 + Real.sinh (z.re / 2) ^ 2 * (2 * Real.cos z.im + 1)`
     (`three_coshHalfRe_sq_sub_coshHalfIm_sq`).
   - Proves the global comparisons
     `(2 * Real.cos z.im - 1) * Complex.normSq (Complex.cosh (z / 2)) ≤ coshHalfRe z ^ 2 - 3 * coshHalfIm z ^ 2`
     (`two_mul_cos_sub_one_mul_normSq_le_coshHalfRe_sq_sub_three_coshHalfIm_sq`) and
     `3 * coshHalfRe z ^ 2 - coshHalfIm z ^ 2 ≤ 3 * Complex.normSq (Complex.cosh (z / 2))`
     (`three_coshHalfRe_sq_sub_coshHalfIm_sq_le_three_mul_normSq`), deducing for all $w, z \in \mathbb{C}$
     with **zero hypotheses**:
     `((2 * Real.cos z.im - 1) * coshTrigPacketWeight t c w.re w.im -
       3 * sinhTrigPacketWeight t c w.re w.im) * ‖specSq sechHalf z‖ ≤
       (complexTrigPacketWeight t c w * specSq sechHalf z).re`
     (`re_complexTrigPacketWeight_mul_specSq_sechHalf_ge_norm_mul`).
   - Proves `1 / 2 < Real.cos y` and `0 < 2 * Real.cos y - 1` on `|y| ≤ 1`
     (`half_lt_cos_of_abs_le_one`, `zero_lt_two_mul_cos_sub_one_of_abs_le_one`), establishing
     strict positivity of `2 * Real.cos (gammaOf ρ).im - 1` and `coshHalfRe (gammaOf ρ) ^ 2 - 3 * coshHalfIm (gammaOf ρ) ^ 2`
     at every nontrivial zero `ρ : zetaZeroConfig.carrier`.

3. **Cosh–Sinh Dominance Sufficiency Criteria for the Decisive Toeplitz Sign and `RiemannHypothesis`
   (Section 3)**:
   - Establishes `re_complexTrigPacketWeight_mul_specSq_sechHalf_gammaOf_nonneg_of_sinh_le`,
     `sum_sum_cosineShiftFn_sechHalf_vonMangoldt_nonneg_of_forall_sinh_le`, and
     `riemannHypothesis_of_forall_sinhTrigPacketWeight_le`.
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped Real ComplexConjugate Nat

noncomputable section

namespace RHTower.CHMDStage19

open WeilOneSided WeilSpectral RHTower.EvenSector RHTower.WeilPolarMajorant
open RHTower.CHMDStage1 RHTower.CHMDStage2 RHTower.CHMDStage3 RHTower.CHMDStage4
open RHTower.CHMDStage11 RHTower.CHMDStage12 RHTower.CHMDStage13 RHTower.CHMDStage14
open RHTower.CHMDStage15 RHTower.CHMDStage16 RHTower.CHMDStage17 RHTower.CHMDStage18
open GaloisForLFunctions.HTGeometry

/-! ## Section 1: Exact Half-Angle Decomposition of `Complex.cosh (z / 2)` and Master Completed-Square Identity -/

/-- The real part `cosh(z.re / 2) * cos(z.im / 2)` of `Complex.cosh (z / 2)`. -/
def coshHalfRe (z : ℂ) : ℝ :=
  Real.cosh (z.re / 2) * Real.cos (z.im / 2)

/-- The imaginary part `sinh(z.re / 2) * sin(z.im / 2)` of `Complex.cosh (z / 2)`. -/
def coshHalfIm (z : ℂ) : ℝ :=
  Real.sinh (z.re / 2) * Real.sin (z.im / 2)

/-- For every $z \in \mathbb{C}$, `Complex.cosh (z / 2) = coshHalfRe z + coshHalfIm z * I`. -/
theorem cosh_half_eq (z : ℂ) :
    Complex.cosh (z / 2) = (coshHalfRe z : ℂ) + (coshHalfIm z : ℂ) * I := by
  have hz : z / 2 = ((z.re / 2 : ℝ) : ℂ) + ((z.im / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [hz, cosh_ofReal_add_mul_I]
  unfold coshHalfRe coshHalfIm
  push_cast
  rfl

theorem re_cosh_half (z : ℂ) : (Complex.cosh (z / 2)).re = coshHalfRe z := by
  rw [cosh_half_eq]
  simp

theorem im_cosh_half (z : ℂ) : (Complex.cosh (z / 2)).im = coshHalfIm z := by
  rw [cosh_half_eq]
  simp

theorem normSq_cosh_half_eq_sq_add_sq (z : ℂ) :
    Complex.normSq (Complex.cosh (z / 2)) = coshHalfRe z ^ 2 + coshHalfIm z ^ 2 := by
  rw [Complex.normSq_apply, re_cosh_half, im_cosh_half]
  ring

theorem re_cosh_half_sq_eq_sq_sub_sq (z : ℂ) :
    (Complex.cosh (z / 2) ^ 2).re = coshHalfRe z ^ 2 - coshHalfIm z ^ 2 := by
  rw [sq, Complex.mul_re, re_cosh_half, im_cosh_half]
  ring

theorem im_cosh_half_sq_eq_two_mul (z : ℂ) :
    (Complex.cosh (z / 2) ^ 2).im = 2 * coshHalfRe z * coshHalfIm z := by
  rw [sq, Complex.mul_im, re_cosh_half, im_cosh_half]
  ring

/-- The nonnegative completed-square remainder
`2 * (A_c C_i - B_s C_r)² + 2 * (A_s C_i + B_c C_r)²`
in the polynomial decomposition of `(complexTrigPacketWeight t c w * conj (cosh(z/2)²)).re`. -/
def completedSqTrigPacketRemainder {N : ℕ} (t c : Fin N → ℝ) (u v Cr Ci : ℝ) : ℝ :=
  2 * ((∑ i : Fin N, c i * Real.cosh (t i * v) * Real.cos (t i * u)) * Ci -
      (∑ i : Fin N, c i * Real.sinh (t i * v) * Real.sin (t i * u)) * Cr) ^ 2 +
    2 * ((∑ i : Fin N, c i * Real.cosh (t i * v) * Real.sin (t i * u)) * Ci +
      (∑ i : Fin N, c i * Real.sinh (t i * v) * Real.cos (t i * u)) * Cr) ^ 2

theorem completedSqTrigPacketRemainder_nonneg {N : ℕ} (t c : Fin N → ℝ) (u v Cr Ci : ℝ) :
    0 ≤ completedSqTrigPacketRemainder t c u v Cr Ci :=
  add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (mul_nonneg (by norm_num) (sq_nonneg _))

/-- **Master Polynomial Completed-Square Identity**:
for every $w, z \in \mathbb{C}$,
`(complexTrigPacketWeight t c w * conj (Complex.cosh (z / 2) ^ 2)).re =
  coshTrigPacketWeight t c w.re w.im * (coshHalfRe z ^ 2 - 3 * coshHalfIm z ^ 2) -
  sinhTrigPacketWeight t c w.re w.im * (3 * coshHalfRe z ^ 2 - coshHalfIm z ^ 2) +
  completedSqTrigPacketRemainder t c w.re w.im (coshHalfRe z) (coshHalfIm z)`. -/
theorem re_complexTrigPacketWeight_mul_conj_cosh_half_sq_eq
    {N : ℕ} (t c : Fin N → ℝ) (w z : ℂ) :
    (complexTrigPacketWeight t c w * conj (Complex.cosh (z / 2) ^ 2)).re =
      coshTrigPacketWeight t c w.re w.im * (coshHalfRe z ^ 2 - 3 * coshHalfIm z ^ 2) -
        sinhTrigPacketWeight t c w.re w.im * (3 * coshHalfRe z ^ 2 - coshHalfIm z ^ 2) +
        completedSqTrigPacketRemainder t c w.re w.im (coshHalfRe z) (coshHalfIm z) := by
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im,
    re_complexTrigPacketWeight_eq_cosh_sub_sinh, im_complexTrigPacketWeight_eq_two_mul_cross,
    re_cosh_half_sq_eq_sq_sub_sq, im_cosh_half_sq_eq_two_mul]
  unfold coshTrigPacketWeight sinhTrigPacketWeight crossTrigPacketWeight
    completedSqTrigPacketRemainder
  ring

/-- **Completed-Square Lower Bound for `(complexTrigPacketWeight t c w * conj (Complex.cosh (z / 2) ^ 2)).re`**:
for every $w, z \in \mathbb{C}$,
`coshTrigPacketWeight t c w.re w.im * (coshHalfRe z ^ 2 - 3 * coshHalfIm z ^ 2) -
  sinhTrigPacketWeight t c w.re w.im * (3 * coshHalfRe z ^ 2 - coshHalfIm z ^ 2) ≤
  (complexTrigPacketWeight t c w * conj (Complex.cosh (z / 2) ^ 2)).re`. -/
theorem re_complexTrigPacketWeight_mul_conj_cosh_half_sq_ge
    {N : ℕ} (t c : Fin N → ℝ) (w z : ℂ) :
    coshTrigPacketWeight t c w.re w.im * (coshHalfRe z ^ 2 - 3 * coshHalfIm z ^ 2) -
      sinhTrigPacketWeight t c w.re w.im * (3 * coshHalfRe z ^ 2 - coshHalfIm z ^ 2) ≤
      (complexTrigPacketWeight t c w * conj (Complex.cosh (z / 2) ^ 2)).re := by
  rw [re_complexTrigPacketWeight_mul_conj_cosh_half_sq_eq]
  linarith [completedSqTrigPacketRemainder_nonneg t c w.re w.im (coshHalfRe z) (coshHalfIm z)]

/-- **Exact Rational–Hyperbolic Completed-Square Formula for `(complexTrigPacketWeight t c w * specSq sechHalf z).re`**:
for every $w, z \in \mathbb{C}$,
`(complexTrigPacketWeight t c w * specSq sechHalf z).re =
  (coshTrigPacketWeight t c w.re w.im * (coshHalfRe z ^ 2 - 3 * coshHalfIm z ^ 2) -
    sinhTrigPacketWeight t c w.re w.im * (3 * coshHalfRe z ^ 2 - coshHalfIm z ^ 2) +
    completedSqTrigPacketRemainder t c w.re w.im (coshHalfRe z) (coshHalfIm z)) /
  Complex.normSq (Complex.cosh (z / 2)) ^ 2`. -/
theorem re_complexTrigPacketWeight_mul_specSq_sechHalf_eq_completedSq
    {N : ℕ} (t c : Fin N → ℝ) (w z : ℂ) :
    (complexTrigPacketWeight t c w * specSq sechHalf z).re =
      (coshTrigPacketWeight t c w.re w.im * (coshHalfRe z ^ 2 - 3 * coshHalfIm z ^ 2) -
        sinhTrigPacketWeight t c w.re w.im * (3 * coshHalfRe z ^ 2 - coshHalfIm z ^ 2) +
        completedSqTrigPacketRemainder t c w.re w.im (coshHalfRe z) (coshHalfIm z)) /
      Complex.normSq (Complex.cosh (z / 2)) ^ 2 := by
  have hconj := re_complexTrigPacketWeight_mul_conj_cosh_half_sq_eq t c w z
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im] at hconj
  rw [specSq_sechHalf_eq_inv_cosh_sq, Complex.mul_re, Complex.inv_re, Complex.inv_im]
  have hns : Complex.normSq (Complex.cosh (z / 2) ^ 2) =
      Complex.normSq (Complex.cosh (z / 2)) ^ 2 := by
    rw [sq, map_mul, ← sq]
  rw [hns, ← hconj]
  ring

/-- **Global Rational–Hyperbolic Lower Bound for `(complexTrigPacketWeight t c w * specSq sechHalf z).re`**:
holds for all $w, z \in \mathbb{C}$ with zero hypotheses. -/
theorem re_complexTrigPacketWeight_mul_specSq_sechHalf_ge_coshHalfRe_sub_three_coshHalfIm
    {N : ℕ} (t c : Fin N → ℝ) (w z : ℂ) :
    (coshTrigPacketWeight t c w.re w.im * (coshHalfRe z ^ 2 - 3 * coshHalfIm z ^ 2) -
      sinhTrigPacketWeight t c w.re w.im * (3 * coshHalfRe z ^ 2 - coshHalfIm z ^ 2)) /
      Complex.normSq (Complex.cosh (z / 2)) ^ 2 ≤
      (complexTrigPacketWeight t c w * specSq sechHalf z).re := by
  rw [re_complexTrigPacketWeight_mul_specSq_sechHalf_eq_completedSq]
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
  linarith [completedSqTrigPacketRemainder_nonneg t c w.re w.im (coshHalfRe z) (coshHalfIm z)]

/-! ## Section 2: Exact Formulas and Strip Positivity of `coshHalfRe z ^ 2 - 3 * coshHalfIm z ^ 2` -/

/-- **Exact Trigonometric–Hyperbolic Formula for `coshHalfRe z ^ 2 - 3 * coshHalfIm z ^ 2`**:
for every $z \in \mathbb{C}$,
`coshHalfRe z ^ 2 - 3 * coshHalfIm z ^ 2 = Real.cos (z.im / 2) ^ 2 + Real.sinh (z.re / 2) ^ 2 * (2 * Real.cos z.im - 1)`. -/
theorem coshHalfRe_sq_sub_three_coshHalfIm_sq (z : ℂ) :
    coshHalfRe z ^ 2 - 3 * coshHalfIm z ^ 2 =
      Real.cos (z.im / 2) ^ 2 + Real.sinh (z.re / 2) ^ 2 * (2 * Real.cos z.im - 1) := by
  unfold coshHalfRe coshHalfIm
  have hch := Real.cosh_sq (z.re / 2)
  have hcos := Real.cos_two_mul (z.im / 2)
  have h2 : 2 * (z.im / 2) = z.im := by ring
  rw [h2] at hcos
  have hpyth := Real.cos_sq_add_sin_sq (z.im / 2)
  nlinarith

/-- **Exact Trigonometric–Hyperbolic Formula for `3 * coshHalfRe z ^ 2 - coshHalfIm z ^ 2`**:
for every $z \in \mathbb{C}$,
`3 * coshHalfRe z ^ 2 - coshHalfIm z ^ 2 = 3 * Real.cos (z.im / 2) ^ 2 + Real.sinh (z.re / 2) ^ 2 * (2 * Real.cos z.im + 1)`. -/
theorem three_coshHalfRe_sq_sub_coshHalfIm_sq (z : ℂ) :
    3 * coshHalfRe z ^ 2 - coshHalfIm z ^ 2 =
      3 * Real.cos (z.im / 2) ^ 2 + Real.sinh (z.re / 2) ^ 2 * (2 * Real.cos z.im + 1) := by
  unfold coshHalfRe coshHalfIm
  have hch := Real.cosh_sq (z.re / 2)
  have hcos := Real.cos_two_mul (z.im / 2)
  have h2 : 2 * (z.im / 2) = z.im := by ring
  rw [h2] at hcos
  have hpyth := Real.cos_sq_add_sin_sq (z.im / 2)
  nlinarith

/-- For every $z \in \mathbb{C}$,
`(2 * Real.cos z.im - 1) * Complex.normSq (Complex.cosh (z / 2)) ≤ coshHalfRe z ^ 2 - 3 * coshHalfIm z ^ 2`. -/
theorem two_mul_cos_sub_one_mul_normSq_le_coshHalfRe_sq_sub_three_coshHalfIm_sq (z : ℂ) :
    (2 * Real.cos z.im - 1) * Complex.normSq (Complex.cosh (z / 2)) ≤
      coshHalfRe z ^ 2 - 3 * coshHalfIm z ^ 2 := by
  rw [normSq_cosh_half, coshHalfRe_sq_sub_three_coshHalfIm_sq]
  have hcos : Real.cos z.im ≤ 1 := Real.cos_le_one z.im
  have hsq : 0 ≤ Real.cos (z.im / 2) ^ 2 := sq_nonneg _
  nlinarith

/-- For every $z \in \mathbb{C}$,
`3 * coshHalfRe z ^ 2 - coshHalfIm z ^ 2 ≤ 3 * Complex.normSq (Complex.cosh (z / 2))`. -/
theorem three_coshHalfRe_sq_sub_coshHalfIm_sq_le_three_mul_normSq (z : ℂ) :
    3 * coshHalfRe z ^ 2 - coshHalfIm z ^ 2 ≤
      3 * Complex.normSq (Complex.cosh (z / 2)) := by
  rw [normSq_cosh_half_eq_sq_add_sq]
  have hsq : 0 ≤ coshHalfIm z ^ 2 := sq_nonneg _
  linarith

/-- **Global Norm-Multiplied Cosh–Sinh Dominance Lower Bound**:
for every $w, z \in \mathbb{C}$ (with zero hypotheses on $w$ or $z$),
`((2 * Real.cos z.im - 1) * coshTrigPacketWeight t c w.re w.im -
  3 * sinhTrigPacketWeight t c w.re w.im) * ‖specSq sechHalf z‖ ≤
  (complexTrigPacketWeight t c w * specSq sechHalf z).re`. -/
theorem re_complexTrigPacketWeight_mul_specSq_sechHalf_ge_norm_mul
    {N : ℕ} (t c : Fin N → ℝ) (w z : ℂ) :
    ((2 * Real.cos z.im - 1) * coshTrigPacketWeight t c w.re w.im -
        3 * sinhTrigPacketWeight t c w.re w.im) * ‖specSq sechHalf z‖ ≤
      (complexTrigPacketWeight t c w * specSq sechHalf z).re := by
  refine le_trans ?_
    (re_complexTrigPacketWeight_mul_specSq_sechHalf_ge_coshHalfRe_sub_three_coshHalfIm t c w z)
  rw [norm_specSq_sechHalf, ← normSq_cosh_half]
  rcases eq_or_lt_of_le (Complex.normSq_nonneg (Complex.cosh (z / 2))) with h0 | hpos
  · rw [← h0]; simp
  · rw [← div_eq_mul_inv,
      show ((2 * Real.cos z.im - 1) * coshTrigPacketWeight t c w.re w.im -
          3 * sinhTrigPacketWeight t c w.re w.im) /
          Complex.normSq (Complex.cosh (z / 2)) =
        (((2 * Real.cos z.im - 1) * coshTrigPacketWeight t c w.re w.im -
            3 * sinhTrigPacketWeight t c w.re w.im) *
          Complex.normSq (Complex.cosh (z / 2))) /
          Complex.normSq (Complex.cosh (z / 2)) ^ 2 by
        rw [sq, mul_div_mul_right _ _ hpos.ne']]
    refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
    have h1 := two_mul_cos_sub_one_mul_normSq_le_coshHalfRe_sq_sub_three_coshHalfIm_sq z
    have h2 := three_coshHalfRe_sq_sub_coshHalfIm_sq_le_three_mul_normSq z
    have hc := coshTrigPacketWeight_nonneg t c w.re w.im
    have hs := sinhTrigPacketWeight_nonneg t c w.re w.im
    nlinarith

/-- On `|y| ≤ 1`, `1 / 2 < Real.cos y`. -/
theorem half_lt_cos_of_abs_le_one {y : ℝ} (hy : |y| ≤ 1) :
    1 / 2 < Real.cos y := by
  rw [← Real.cos_abs, ← Real.cos_pi_div_three]
  exact Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg y) (by linarith [Real.pi_gt_three])
    (by linarith [Real.pi_gt_three])

/-- On `|y| ≤ 1`, `0 < 2 * Real.cos y - 1`. -/
theorem zero_lt_two_mul_cos_sub_one_of_abs_le_one {y : ℝ} (hy : |y| ≤ 1) :
    0 < 2 * Real.cos y - 1 := by
  have h := half_lt_cos_of_abs_le_one hy
  linarith

/-- On `|z.im| ≤ 1`, `0 < coshHalfRe z ^ 2 - 3 * coshHalfIm z ^ 2`. -/
theorem coshHalfRe_sq_sub_three_coshHalfIm_sq_pos_of_abs_im_le_one
    {z : ℂ} (hz : |z.im| ≤ 1) :
    0 < coshHalfRe z ^ 2 - 3 * coshHalfIm z ^ 2 := by
  rw [coshHalfRe_sq_sub_three_coshHalfIm_sq]
  have hc : 0 < Real.cos (z.im / 2) := cos_half_pos (by linarith)
  have h2c : 0 ≤ 2 * Real.cos z.im - 1 := (zero_lt_two_mul_cos_sub_one_of_abs_le_one hz).le
  have hsh : 0 ≤ Real.sinh (z.re / 2) ^ 2 := sq_nonneg _
  linarith [sq_pos_of_pos hc, mul_nonneg hsh h2c]

/-- At every nontrivial zero `ρ : zetaZeroConfig.carrier`,
`0 < 2 * Real.cos (gammaOf ρ).im - 1`. -/
theorem zero_lt_two_mul_cos_im_gammaOf_sub_one (ρ : zetaZeroConfig.carrier) :
    0 < 2 * Real.cos (Zeta23.gammaOf (ρ : ℂ)).im - 1 := by
  have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hIm : |(Zeta23.gammaOf (ρ : ℂ)).im| < 1 / 2 :=
    WeilEF.abs_gammaOf_im_lt ⟨hmem.2.1, hmem.2.2⟩
  exact zero_lt_two_mul_cos_sub_one_of_abs_le_one (by linarith)

/-! ## Section 3: Cosh–Sinh Dominance Sufficiency Criteria for the Decisive Toeplitz Sign and `RiemannHypothesis` -/

/-- **Pointwise Zero-Side Nonnegativity from Cosh–Sinh Dominance**:
if at a nontrivial zero `ρ : zetaZeroConfig.carrier`,
`3 * sinhTrigPacketWeight t c (rhoC (gammaOf ρ)).re (rhoC (gammaOf ρ)).im ≤
  (2 * Real.cos (gammaOf ρ).im - 1) * coshTrigPacketWeight t c (rhoC (gammaOf ρ)).re (rhoC (gammaOf ρ)).im`,
then the wave-packet zero summand `(complexTrigPacketWeight t c (rhoC (gammaOf ρ)) * specSq sechHalf (gammaOf ρ)).re`
is nonnegative. -/
theorem re_complexTrigPacketWeight_mul_specSq_sechHalf_gammaOf_nonneg_of_sinh_le
    {N : ℕ} (t c : Fin N → ℝ) (ρ : zetaZeroConfig.carrier)
    (hdom : 3 * sinhTrigPacketWeight t c (rhoC (Zeta23.gammaOf ρ)).re (rhoC (Zeta23.gammaOf ρ)).im ≤
      (2 * Real.cos (Zeta23.gammaOf (ρ : ℂ)).im - 1) *
        coshTrigPacketWeight t c (rhoC (Zeta23.gammaOf ρ)).re (rhoC (Zeta23.gammaOf ρ)).im) :
    0 ≤ (complexTrigPacketWeight t c (rhoC (Zeta23.gammaOf ρ)) *
      specSq sechHalf (Zeta23.gammaOf ρ)).re := by
  refine le_trans ?_
    (re_complexTrigPacketWeight_mul_specSq_sechHalf_ge_norm_mul t c
      (rhoC (Zeta23.gammaOf ρ)) (Zeta23.gammaOf ρ))
  exact mul_nonneg (by linarith) (norm_nonneg _)

/-- **Wave-Packet Toeplitz Nonnegativity from Pointwise Cosh–Sinh Dominance**:
for a given finite wave packet `(t, c)`, if `3 * sinhTrigPacketWeight ≤ (2 * cos(Im γ_ρ) - 1) * coshTrigPacketWeight`
at every nontrivial zero `ρ : zetaZeroConfig.carrier`, then
`0 ≤ ∑ i, ∑ j, c i * c j * cosineShiftFn Λ sechHalf (t j - t i)`. -/
theorem sum_sum_cosineShiftFn_sechHalf_vonMangoldt_nonneg_of_forall_sinh_le
    {N : ℕ} (t c : Fin N → ℝ)
    (hdom : ∀ ρ : zetaZeroConfig.carrier,
      3 * sinhTrigPacketWeight t c (rhoC (Zeta23.gammaOf ρ)).re (rhoC (Zeta23.gammaOf ρ)).im ≤
        (2 * Real.cos (Zeta23.gammaOf (ρ : ℂ)).im - 1) *
          coshTrigPacketWeight t c (rhoC (Zeta23.gammaOf ρ)).re (rhoC (Zeta23.gammaOf ρ)).im) :
    0 ≤ ∑ i : Fin N, ∑ j : Fin N, c i * c j *
      cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf (t j - t i) := by
  rw [sum_sum_cosineShiftFn_sechHalf_vonMangoldt_eq_tsum_complexTrigPacketWeight]
  exact tsum_nonneg fun ρ => mul_nonneg (Nat.cast_nonneg _)
    (re_complexTrigPacketWeight_mul_specSq_sechHalf_gammaOf_nonneg_of_sinh_le t c ρ (hdom ρ))

/-- **Cosh–Sinh Dominance Sufficiency Criterion for `RiemannHypothesis`**:
if every finite wave packet `(t, c)` satisfies `3 * sinhTrigPacketWeight ≤ (2 * cos(Im γ_ρ) - 1) * coshTrigPacketWeight`
at every nontrivial zero `ρ : zetaZeroConfig.carrier`, then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_forall_sinhTrigPacketWeight_le
    (hdom : ∀ (N : ℕ) (t c : Fin N → ℝ) (ρ : zetaZeroConfig.carrier),
      3 * sinhTrigPacketWeight t c (rhoC (Zeta23.gammaOf ρ)).re (rhoC (Zeta23.gammaOf ρ)).im ≤
        (2 * Real.cos (Zeta23.gammaOf (ρ : ℂ)).im - 1) *
          coshTrigPacketWeight t c (rhoC (Zeta23.gammaOf ρ)).re (rhoC (Zeta23.gammaOf ρ)).im) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_forall_sum_sum_cosineShiftFn_sechHalf_nonneg]
  intro N t c
  exact sum_sum_cosineShiftFn_sechHalf_vonMangoldt_nonneg_of_forall_sinh_le t c (hdom N t c)

end RHTower.CHMDStage19

end
