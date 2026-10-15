import GaloisForLFunctions.RHTower.CHMDStage20TwoPointCoshSinhClosedFormsAndRhoCosShiftDecomposition

/-!
# Stage 21 of the Causal Hyperbolic–Modular Duality (CHMD) Route:
# Dual Sinh-Reduced and Cosh-Reduced Exact Square Identities, Two-Sided Strip Sandwich Bounds,
# and Exact Zero-Side Nonnegativity Equivalence

This module establishes **Stage 21** of the Causal Hyperbolic–Modular Duality (CHMD) route:

1. **Universal Dual Sinh-Reduced and Cosh-Reduced Exact Square Identities (Section 1)**:
   - Defines the nonnegative 2-square weights `sinhReducedSqWeight t c u v Dr Di` and
     `coshReducedSqWeight t c u v Dr Di` (`sinhReducedSqWeight_nonneg`,
     `coshReducedSqWeight_nonneg`).
   - Proves the **Sinh-Reduced Polynomial Identity**
     (`re_mul_re_complexTrigPacketWeight_mul_conj_eq_sinhReduced`):
     for every $w, D \in \mathbb{C}$,
     `D.re * (complexTrigPacketWeight t c w * conj D).re =
       sinhReducedSqWeight t c w.re w.im D.re D.im -
       Complex.normSq D * sinhTrigPacketWeight t c w.re w.im`.
   - Proves the **Cosh-Reduced Polynomial Identity**
     (`re_mul_re_complexTrigPacketWeight_mul_conj_eq_coshReduced`):
     for every $w, D \in \mathbb{C}$,
     `D.re * (complexTrigPacketWeight t c w * conj D).re =
       Complex.normSq D * coshTrigPacketWeight t c w.re w.im -
       coshReducedSqWeight t c w.re w.im D.re D.im`.

2. **Exact Specialization to `specSq sechHalf z` and Two-Sided Strip Sandwich Bounds (Section 2)**:
   - Proves for all $w, z \in \mathbb{C}$ (with zero hypotheses on $w$ or $z$):
     `(Complex.cosh (z / 2) ^ 2).re * (complexTrigPacketWeight t c w * specSq sechHalf z).re =
       sinhReducedSqWeight t c w.re w.im (Complex.cosh (z / 2) ^ 2).re (Complex.cosh (z / 2) ^ 2).im /
         Complex.normSq (Complex.cosh (z / 2)) ^ 2 -
       sinhTrigPacketWeight t c w.re w.im`
     (`re_cosh_half_sq_mul_re_complexTrigPacketWeight_mul_specSq_sechHalf_eq_sinhReduced`)
     and the dual identity
     `(Complex.cosh (z / 2) ^ 2).re * (complexTrigPacketWeight t c w * specSq sechHalf z).re =
       coshTrigPacketWeight t c w.re w.im -
       coshReducedSqWeight t c w.re w.im (Complex.cosh (z / 2) ^ 2).re (Complex.cosh (z / 2) ^ 2).im /
         Complex.normSq (Complex.cosh (z / 2)) ^ 2`
     (`re_cosh_half_sq_mul_re_complexTrigPacketWeight_mul_specSq_sechHalf_eq_coshReduced`).
   - Deduces the global two-sided sandwich bounds on $\mathbb{C}$
     (`neg_sinhTrigPacketWeight_le_re_cosh_half_sq_mul_re_specSq`,
     `re_cosh_half_sq_mul_re_specSq_le_coshTrigPacketWeight`) and on the strip `|z.im| ≤ 5 / 4`:
     `- (sinhTrigPacketWeight t c w.re w.im / (Complex.cosh (z / 2) ^ 2).re) ≤
       (complexTrigPacketWeight t c w * specSq sechHalf z).re ≤
       coshTrigPacketWeight t c w.re w.im / (Complex.cosh (z / 2) ^ 2).re`
     (`neg_sinhTrigPacketWeight_div_le_re_complexTrigPacketWeight_mul_specSq_sechHalf`,
     `re_complexTrigPacketWeight_mul_specSq_sechHalf_le_coshTrigPacketWeight_div`).

3. **Exact Zero-Side Summand Nonnegativity Equivalence and 2-Point Phase-Independent Lower Bounds
   (Section 3)**:
   - Proves that at every $z$ with `|z.im| ≤ 5 / 4` (and in particular at every nontrivial zero
     `z = gammaOf ρ`), `(complexTrigPacketWeight t c w * specSq sechHalf z).re ≥ 0` holds **if and
     only if**
     `sinhTrigPacketWeight t c w.re w.im * Complex.normSq (Complex.cosh (z / 2)) ^ 2 ≤
       sinhReducedSqWeight t c w.re w.im (Complex.cosh (z / 2) ^ 2).re (Complex.cosh (z / 2) ^ 2).im`
     (`re_complexTrigPacketWeight_mul_specSq_sechHalf_nonneg_iff`,
     `re_complexTrigPacketWeight_mul_specSq_sechHalf_gammaOf_nonneg_iff`).
   - Specializes the strip lower bound to the 2-point sum and difference packets, proving the
     phase-independent lower bounds `- (Real.sinh (y * (rhoC z).im) ^ 2 / (Complex.cosh (z / 2) ^ 2).re)`
     for both `(4 * Complex.cos ((y : ℂ) * rhoC z / 2) ^ 2 * specSq sechHalf z).re` and
     `(4 * Complex.sin ((y : ℂ) * rhoC z / 2) ^ 2 * specSq sechHalf z).re`.
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped Real ComplexConjugate Nat

noncomputable section

namespace RHTower.CHMDStage21

open WeilOneSided WeilSpectral RHTower.EvenSector RHTower.WeilPolarMajorant
open RHTower.CHMDStage1 RHTower.CHMDStage2 RHTower.CHMDStage3 RHTower.CHMDStage4
open RHTower.CHMDStage11 RHTower.CHMDStage12 RHTower.CHMDStage13 RHTower.CHMDStage14
open RHTower.CHMDStage15 RHTower.CHMDStage16 RHTower.CHMDStage17 RHTower.CHMDStage18
open RHTower.CHMDStage19 RHTower.CHMDStage20
open GaloisForLFunctions.HTGeometry

/-! ## Section 1: Universal Dual Sinh-Reduced and Cosh-Reduced Exact Square Identities -/

/-- The Sinh-reduced 2-square weight
`(D_r A_c - D_i B_s)² + (D_r A_s + D_i B_c)²`. -/
def sinhReducedSqWeight {N : ℕ} (t c : Fin N → ℝ) (u v Dr Di : ℝ) : ℝ :=
  (Dr * (∑ i : Fin N, c i * Real.cosh (t i * v) * Real.cos (t i * u)) -
      Di * (∑ i : Fin N, c i * Real.sinh (t i * v) * Real.sin (t i * u))) ^ 2 +
    (Dr * (∑ i : Fin N, c i * Real.cosh (t i * v) * Real.sin (t i * u)) +
      Di * (∑ i : Fin N, c i * Real.sinh (t i * v) * Real.cos (t i * u))) ^ 2

/-- The Cosh-reduced 2-square weight
`(D_i A_c + D_r B_s)² + (D_i A_s - D_r B_c)²`. -/
def coshReducedSqWeight {N : ℕ} (t c : Fin N → ℝ) (u v Dr Di : ℝ) : ℝ :=
  (Di * (∑ i : Fin N, c i * Real.cosh (t i * v) * Real.cos (t i * u)) +
      Dr * (∑ i : Fin N, c i * Real.sinh (t i * v) * Real.sin (t i * u))) ^ 2 +
    (Di * (∑ i : Fin N, c i * Real.cosh (t i * v) * Real.sin (t i * u)) -
      Dr * (∑ i : Fin N, c i * Real.sinh (t i * v) * Real.cos (t i * u))) ^ 2

theorem sinhReducedSqWeight_nonneg {N : ℕ} (t c : Fin N → ℝ) (u v Dr Di : ℝ) :
    0 ≤ sinhReducedSqWeight t c u v Dr Di :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem coshReducedSqWeight_nonneg {N : ℕ} (t c : Fin N → ℝ) (u v Dr Di : ℝ) :
    0 ≤ coshReducedSqWeight t c u v Dr Di :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- **Universal Sinh-Reduced Polynomial Identity**:
for every $w, D \in \mathbb{C}$,
`D.re * (complexTrigPacketWeight t c w * conj D).re =
  sinhReducedSqWeight t c w.re w.im D.re D.im -
  Complex.normSq D * sinhTrigPacketWeight t c w.re w.im`. -/
theorem re_mul_re_complexTrigPacketWeight_mul_conj_eq_sinhReduced
    {N : ℕ} (t c : Fin N → ℝ) (w D : ℂ) :
    D.re * (complexTrigPacketWeight t c w * conj D).re =
      sinhReducedSqWeight t c w.re w.im D.re D.im -
        Complex.normSq D * sinhTrigPacketWeight t c w.re w.im := by
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply,
    re_complexTrigPacketWeight_eq_cosh_sub_sinh, im_complexTrigPacketWeight_eq_two_mul_cross]
  unfold coshTrigPacketWeight sinhTrigPacketWeight crossTrigPacketWeight sinhReducedSqWeight
  ring

/-- **Universal Cosh-Reduced Polynomial Identity**:
for every $w, D \in \mathbb{C}$,
`D.re * (complexTrigPacketWeight t c w * conj D).re =
  Complex.normSq D * coshTrigPacketWeight t c w.re w.im -
  coshReducedSqWeight t c w.re w.im D.re D.im`. -/
theorem re_mul_re_complexTrigPacketWeight_mul_conj_eq_coshReduced
    {N : ℕ} (t c : Fin N → ℝ) (w D : ℂ) :
    D.re * (complexTrigPacketWeight t c w * conj D).re =
      Complex.normSq D * coshTrigPacketWeight t c w.re w.im -
        coshReducedSqWeight t c w.re w.im D.re D.im := by
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply,
    re_complexTrigPacketWeight_eq_cosh_sub_sinh, im_complexTrigPacketWeight_eq_two_mul_cross]
  unfold coshTrigPacketWeight sinhTrigPacketWeight crossTrigPacketWeight coshReducedSqWeight
  ring

/-! ## Section 2: Specialization to `specSq sechHalf z` and Two-Sided Strip Sandwich Bounds -/

/-- **Global Sinh-Reduced Rational Identity for `specSq sechHalf z`**:
for every $w, z \in \mathbb{C}$ (with zero hypotheses on $w$ or $z$),
`(Complex.cosh (z / 2) ^ 2).re * (complexTrigPacketWeight t c w * specSq sechHalf z).re =
  (sinhReducedSqWeight t c w.re w.im (Complex.cosh (z / 2) ^ 2).re (Complex.cosh (z / 2) ^ 2).im -
    Complex.normSq (Complex.cosh (z / 2)) ^ 2 * sinhTrigPacketWeight t c w.re w.im) /
    Complex.normSq (Complex.cosh (z / 2)) ^ 2`. -/
theorem re_cosh_half_sq_mul_re_complexTrigPacketWeight_mul_specSq_sechHalf_eq_sinhReduced_div
    {N : ℕ} (t c : Fin N → ℝ) (w z : ℂ) :
    (Complex.cosh (z / 2) ^ 2).re * (complexTrigPacketWeight t c w * specSq sechHalf z).re =
      (sinhReducedSqWeight t c w.re w.im (Complex.cosh (z / 2) ^ 2).re
          (Complex.cosh (z / 2) ^ 2).im -
        Complex.normSq (Complex.cosh (z / 2)) ^ 2 * sinhTrigPacketWeight t c w.re w.im) /
        Complex.normSq (Complex.cosh (z / 2)) ^ 2 := by
  have hns : Complex.normSq (Complex.cosh (z / 2) ^ 2) =
      Complex.normSq (Complex.cosh (z / 2)) ^ 2 := by
    rw [sq, map_mul, ← sq]
  have hconj := re_mul_re_complexTrigPacketWeight_mul_conj_eq_sinhReduced t c w
    (Complex.cosh (z / 2) ^ 2)
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, hns] at hconj
  rw [specSq_sechHalf_eq_inv_cosh_sq, Complex.mul_re, Complex.inv_re, Complex.inv_im, hns, ← hconj]
  ring

/-- **Strip Sinh-Reduced Identity for `specSq sechHalf z`**:
for every $w \in \mathbb{C}$ and $z \in \mathbb{C}$ with $|\operatorname{Im} z| \le 9 / 4$,
`(Complex.cosh (z / 2) ^ 2).re * (complexTrigPacketWeight t c w * specSq sechHalf z).re =
  sinhReducedSqWeight t c w.re w.im (Complex.cosh (z / 2) ^ 2).re (Complex.cosh (z / 2) ^ 2).im /
    Complex.normSq (Complex.cosh (z / 2)) ^ 2 -
  sinhTrigPacketWeight t c w.re w.im`. -/
theorem re_cosh_half_sq_mul_re_complexTrigPacketWeight_mul_specSq_sechHalf_eq_sinhReduced
    {N : ℕ} (t c : Fin N → ℝ) (w : ℂ) {z : ℂ} (hz : |z.im| ≤ 9 / 4) :
    (Complex.cosh (z / 2) ^ 2).re * (complexTrigPacketWeight t c w * specSq sechHalf z).re =
      sinhReducedSqWeight t c w.re w.im (Complex.cosh (z / 2) ^ 2).re
          (Complex.cosh (z / 2) ^ 2).im /
        Complex.normSq (Complex.cosh (z / 2)) ^ 2 -
      sinhTrigPacketWeight t c w.re w.im := by
  have hne : Complex.cosh (z / 2) ≠ 0 := cosh_half_ne_zero hz
  have hns : 0 < Complex.normSq (Complex.cosh (z / 2)) ^ 2 :=
    sq_pos_of_pos (Complex.normSq_pos.mpr hne)
  rw [re_cosh_half_sq_mul_re_complexTrigPacketWeight_mul_specSq_sechHalf_eq_sinhReduced_div,
    sub_div, mul_div_cancel_left₀ _ hns.ne']

/-- **Global Cosh-Reduced Rational Identity for `specSq sechHalf z`**:
for every $w, z \in \mathbb{C}$ (with zero hypotheses on $w$ or $z$),
`(Complex.cosh (z / 2) ^ 2).re * (complexTrigPacketWeight t c w * specSq sechHalf z).re =
  (Complex.normSq (Complex.cosh (z / 2)) ^ 2 * coshTrigPacketWeight t c w.re w.im -
    coshReducedSqWeight t c w.re w.im (Complex.cosh (z / 2) ^ 2).re (Complex.cosh (z / 2) ^ 2).im) /
    Complex.normSq (Complex.cosh (z / 2)) ^ 2`. -/
theorem re_cosh_half_sq_mul_re_complexTrigPacketWeight_mul_specSq_sechHalf_eq_coshReduced_div
    {N : ℕ} (t c : Fin N → ℝ) (w z : ℂ) :
    (Complex.cosh (z / 2) ^ 2).re * (complexTrigPacketWeight t c w * specSq sechHalf z).re =
      (Complex.normSq (Complex.cosh (z / 2)) ^ 2 * coshTrigPacketWeight t c w.re w.im -
        coshReducedSqWeight t c w.re w.im (Complex.cosh (z / 2) ^ 2).re
          (Complex.cosh (z / 2) ^ 2).im) /
        Complex.normSq (Complex.cosh (z / 2)) ^ 2 := by
  have hns : Complex.normSq (Complex.cosh (z / 2) ^ 2) =
      Complex.normSq (Complex.cosh (z / 2)) ^ 2 := by
    rw [sq, map_mul, ← sq]
  have hconj := re_mul_re_complexTrigPacketWeight_mul_conj_eq_coshReduced t c w
    (Complex.cosh (z / 2) ^ 2)
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, hns] at hconj
  rw [specSq_sechHalf_eq_inv_cosh_sq, Complex.mul_re, Complex.inv_re, Complex.inv_im, hns, ← hconj]
  ring

/-- **Strip Cosh-Reduced Identity for `specSq sechHalf z`**:
for every $w \in \mathbb{C}$ and $z \in \mathbb{C}$ with $|\operatorname{Im} z| \le 9 / 4$,
`(Complex.cosh (z / 2) ^ 2).re * (complexTrigPacketWeight t c w * specSq sechHalf z).re =
  coshTrigPacketWeight t c w.re w.im -
  coshReducedSqWeight t c w.re w.im (Complex.cosh (z / 2) ^ 2).re (Complex.cosh (z / 2) ^ 2).im /
    Complex.normSq (Complex.cosh (z / 2)) ^ 2`. -/
theorem re_cosh_half_sq_mul_re_complexTrigPacketWeight_mul_specSq_sechHalf_eq_coshReduced
    {N : ℕ} (t c : Fin N → ℝ) (w : ℂ) {z : ℂ} (hz : |z.im| ≤ 9 / 4) :
    (Complex.cosh (z / 2) ^ 2).re * (complexTrigPacketWeight t c w * specSq sechHalf z).re =
      coshTrigPacketWeight t c w.re w.im -
        coshReducedSqWeight t c w.re w.im (Complex.cosh (z / 2) ^ 2).re
            (Complex.cosh (z / 2) ^ 2).im /
          Complex.normSq (Complex.cosh (z / 2)) ^ 2 := by
  have hne : Complex.cosh (z / 2) ≠ 0 := cosh_half_ne_zero hz
  have hns : 0 < Complex.normSq (Complex.cosh (z / 2)) ^ 2 :=
    sq_pos_of_pos (Complex.normSq_pos.mpr hne)
  rw [re_cosh_half_sq_mul_re_complexTrigPacketWeight_mul_specSq_sechHalf_eq_coshReduced_div,
    sub_div, mul_div_cancel_left₀ _ hns.ne']

/-- **Global Sinh Lower Bound**:
for every $w, z \in \mathbb{C}$,
`- sinhTrigPacketWeight t c w.re w.im ≤
  (Complex.cosh (z / 2) ^ 2).re * (complexTrigPacketWeight t c w * specSq sechHalf z).re`. -/
theorem neg_sinhTrigPacketWeight_le_re_cosh_half_sq_mul_re_specSq
    {N : ℕ} (t c : Fin N → ℝ) (w z : ℂ) :
    -sinhTrigPacketWeight t c w.re w.im ≤
      (Complex.cosh (z / 2) ^ 2).re * (complexTrigPacketWeight t c w * specSq sechHalf z).re := by
  rw [re_cosh_half_sq_mul_re_complexTrigPacketWeight_mul_specSq_sechHalf_eq_sinhReduced_div]
  rcases eq_or_lt_of_le (sq_nonneg (Complex.normSq (Complex.cosh (z / 2)))) with h0 | hpos
  · rw [← h0, div_zero]
    linarith [sinhTrigPacketWeight_nonneg t c w.re w.im]
  · rw [sub_div, mul_div_cancel_left₀ _ hpos.ne']
    have hnonneg :
        0 ≤ sinhReducedSqWeight t c w.re w.im (Complex.cosh (z / 2) ^ 2).re
              (Complex.cosh (z / 2) ^ 2).im /
            Complex.normSq (Complex.cosh (z / 2)) ^ 2 :=
      div_nonneg (sinhReducedSqWeight_nonneg _ _ _ _ _ _) (sq_nonneg _)
    linarith

/-- **Global Cosh Upper Bound**:
for every $w, z \in \mathbb{C}$,
`(Complex.cosh (z / 2) ^ 2).re * (complexTrigPacketWeight t c w * specSq sechHalf z).re ≤
  coshTrigPacketWeight t c w.re w.im`. -/
theorem re_cosh_half_sq_mul_re_specSq_le_coshTrigPacketWeight
    {N : ℕ} (t c : Fin N → ℝ) (w z : ℂ) :
    (Complex.cosh (z / 2) ^ 2).re * (complexTrigPacketWeight t c w * specSq sechHalf z).re ≤
      coshTrigPacketWeight t c w.re w.im := by
  rw [re_cosh_half_sq_mul_re_complexTrigPacketWeight_mul_specSq_sechHalf_eq_coshReduced_div]
  rcases eq_or_lt_of_le (sq_nonneg (Complex.normSq (Complex.cosh (z / 2)))) with h0 | hpos
  · rw [← h0, div_zero]
    exact coshTrigPacketWeight_nonneg t c w.re w.im
  · rw [sub_div, mul_div_cancel_left₀ _ hpos.ne']
    have hnonneg :
        0 ≤ coshReducedSqWeight t c w.re w.im (Complex.cosh (z / 2) ^ 2).re
              (Complex.cosh (z / 2) ^ 2).im /
            Complex.normSq (Complex.cosh (z / 2)) ^ 2 :=
      div_nonneg (coshReducedSqWeight_nonneg _ _ _ _ _ _) (sq_nonneg _)
    linarith

/-- **Strip Sinh Lower Bound**:
for every $z \in \mathbb{C}$ with $|\operatorname{Im} z| \le 5 / 4$ and every $w \in \mathbb{C}$,
`- (sinhTrigPacketWeight t c w.re w.im / (Complex.cosh (z / 2) ^ 2).re) ≤
  (complexTrigPacketWeight t c w * specSq sechHalf z).re`. -/
theorem neg_sinhTrigPacketWeight_div_le_re_complexTrigPacketWeight_mul_specSq_sechHalf
    {N : ℕ} (t c : Fin N → ℝ) (w : ℂ) {z : ℂ} (hz : |z.im| ≤ 5 / 4) :
    -(sinhTrigPacketWeight t c w.re w.im / (Complex.cosh (z / 2) ^ 2).re) ≤
      (complexTrigPacketWeight t c w * specSq sechHalf z).re := by
  have hre : 0 < (Complex.cosh (z / 2) ^ 2).re := re_cosh_half_sq_pos hz
  rw [← neg_div, div_le_iff₀ hre, mul_comm]
  exact neg_sinhTrigPacketWeight_le_re_cosh_half_sq_mul_re_specSq t c w z

/-- **Strip Cosh Upper Bound**:
for every $z \in \mathbb{C}$ with $|\operatorname{Im} z| \le 5 / 4$ and every $w \in \mathbb{C}$,
`(complexTrigPacketWeight t c w * specSq sechHalf z).re ≤
  coshTrigPacketWeight t c w.re w.im / (Complex.cosh (z / 2) ^ 2).re`. -/
theorem re_complexTrigPacketWeight_mul_specSq_sechHalf_le_coshTrigPacketWeight_div
    {N : ℕ} (t c : Fin N → ℝ) (w : ℂ) {z : ℂ} (hz : |z.im| ≤ 5 / 4) :
    (complexTrigPacketWeight t c w * specSq sechHalf z).re ≤
      coshTrigPacketWeight t c w.re w.im / (Complex.cosh (z / 2) ^ 2).re := by
  have hre : 0 < (Complex.cosh (z / 2) ^ 2).re := re_cosh_half_sq_pos hz
  rw [le_div_iff₀ hre, mul_comm]
  exact re_cosh_half_sq_mul_re_specSq_le_coshTrigPacketWeight t c w z

/-! ## Section 3: Exact Zero-Side Summand Nonnegativity Equivalence and 2-Point Phase-Independent Lower Bounds -/

/-- **Exact Strip Nonnegativity Equivalence**:
for every $z \in \mathbb{C}$ with $|\operatorname{Im} z| \le 5 / 4$ and every $w \in \mathbb{C}$,
`0 ≤ (complexTrigPacketWeight t c w * specSq sechHalf z).re` holds **if and only if**
`sinhTrigPacketWeight t c w.re w.im * Complex.normSq (Complex.cosh (z / 2)) ^ 2 ≤
  sinhReducedSqWeight t c w.re w.im (Complex.cosh (z / 2) ^ 2).re (Complex.cosh (z / 2) ^ 2).im`. -/
theorem re_complexTrigPacketWeight_mul_specSq_sechHalf_nonneg_iff
    {N : ℕ} (t c : Fin N → ℝ) (w : ℂ) {z : ℂ} (hz : |z.im| ≤ 5 / 4) :
    0 ≤ (complexTrigPacketWeight t c w * specSq sechHalf z).re ↔
      sinhTrigPacketWeight t c w.re w.im * Complex.normSq (Complex.cosh (z / 2)) ^ 2 ≤
        sinhReducedSqWeight t c w.re w.im (Complex.cosh (z / 2) ^ 2).re
          (Complex.cosh (z / 2) ^ 2).im := by
  have hre : 0 < (Complex.cosh (z / 2) ^ 2).re := re_cosh_half_sq_pos hz
  have hne : Complex.cosh (z / 2) ≠ 0 := cosh_half_ne_zero (by linarith)
  have hns : 0 < Complex.normSq (Complex.cosh (z / 2)) ^ 2 :=
    sq_pos_of_pos (Complex.normSq_pos.mpr hne)
  rw [← mul_nonneg_iff_of_pos_left hre,
    re_cosh_half_sq_mul_re_complexTrigPacketWeight_mul_specSq_sechHalf_eq_sinhReduced t c w
      (by linarith),
    sub_nonneg, le_div_iff₀ hns]

/-- **Exact Zero-Side Summand Nonnegativity Equivalence at Every Nontrivial Zero `ρ`**:
for every nontrivial zero `ρ : zetaZeroConfig.carrier`, the wave-packet zero summand at
`gammaOf ρ` is nonnegative if and only if the `sinhReducedSqWeight` dominates
`sinhTrigPacketWeight * normSq(cosh(γ_ρ / 2))²`. -/
theorem re_complexTrigPacketWeight_mul_specSq_sechHalf_gammaOf_nonneg_iff
    {N : ℕ} (t c : Fin N → ℝ) (ρ : zetaZeroConfig.carrier) :
    0 ≤ (complexTrigPacketWeight t c (rhoC (Zeta23.gammaOf ρ)) *
        specSq sechHalf (Zeta23.gammaOf ρ)).re ↔
      sinhTrigPacketWeight t c (rhoC (Zeta23.gammaOf ρ)).re (rhoC (Zeta23.gammaOf ρ)).im *
          Complex.normSq (Complex.cosh (Zeta23.gammaOf (ρ : ℂ) / 2)) ^ 2 ≤
        sinhReducedSqWeight t c (rhoC (Zeta23.gammaOf ρ)).re (rhoC (Zeta23.gammaOf ρ)).im
          (Complex.cosh (Zeta23.gammaOf (ρ : ℂ) / 2) ^ 2).re
          (Complex.cosh (Zeta23.gammaOf (ρ : ℂ) / 2) ^ 2).im := by
  have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hIm : |(Zeta23.gammaOf (ρ : ℂ)).im| < 1 / 2 :=
    WeilEF.abs_gammaOf_im_lt ⟨hmem.2.1, hmem.2.2⟩
  exact re_complexTrigPacketWeight_mul_specSq_sechHalf_nonneg_iff t c
    (rhoC (Zeta23.gammaOf ρ)) (by linarith)

/-- **Phase-Independent Strip Lower Bound for the 2-Point Sum Packet**:
for every $z \in \mathbb{C}$ with $|\operatorname{Im} z| \le 5 / 4$ and every $y \in \mathbb{R}$,
`- (Real.sinh (y * (rhoC z).im) ^ 2 / (Complex.cosh (z / 2) ^ 2).re) ≤
  (4 * Complex.cos ((y : ℂ) * rhoC z / 2) ^ 2 * specSq sechHalf z).re`. -/
theorem neg_sinh_sq_div_le_re_four_cos_sq_mul_specSq_sechHalf
    {z : ℂ} (hz : |z.im| ≤ 5 / 4) (y : ℝ) :
    -(Real.sinh (y * (rhoC z).im) ^ 2 / (Complex.cosh (z / 2) ^ 2).re) ≤
      (4 * Complex.cos ((y : ℂ) * rhoC z / 2) ^ 2 * specSq sechHalf z).re := by
  rw [← complexTrigPacketWeight_twoPointSum_eq_four_mul_cos_sq,
    ← sinhTrigPacketWeight_twoPointSum y (rhoC z).re (rhoC z).im]
  exact neg_sinhTrigPacketWeight_div_le_re_complexTrigPacketWeight_mul_specSq_sechHalf
    (twoPointShift y) twoPointSumCoeff (rhoC z) hz

/-- **Phase-Independent Strip Lower Bound for the 2-Point Difference Packet**:
for every $z \in \mathbb{C}$ with $|\operatorname{Im} z| \le 5 / 4$ and every $y \in \mathbb{R}$,
`- (Real.sinh (y * (rhoC z).im) ^ 2 / (Complex.cosh (z / 2) ^ 2).re) ≤
  (4 * Complex.sin ((y : ℂ) * rhoC z / 2) ^ 2 * specSq sechHalf z).re`. -/
theorem neg_sinh_sq_div_le_re_four_sin_sq_mul_specSq_sechHalf
    {z : ℂ} (hz : |z.im| ≤ 5 / 4) (y : ℝ) :
    -(Real.sinh (y * (rhoC z).im) ^ 2 / (Complex.cosh (z / 2) ^ 2).re) ≤
      (4 * Complex.sin ((y : ℂ) * rhoC z / 2) ^ 2 * specSq sechHalf z).re := by
  rw [← complexTrigPacketWeight_twoPointDiff_eq_four_mul_sin_sq,
    ← sinhTrigPacketWeight_twoPointDiff y (rhoC z).re (rhoC z).im]
  exact neg_sinhTrigPacketWeight_div_le_re_complexTrigPacketWeight_mul_specSq_sechHalf
    (twoPointShift y) twoPointDiffCoeff (rhoC z) hz

end RHTower.CHMDStage21

end
