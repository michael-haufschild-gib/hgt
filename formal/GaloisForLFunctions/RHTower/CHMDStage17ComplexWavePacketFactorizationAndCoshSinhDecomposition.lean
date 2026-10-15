import GaloisForLFunctions.RHTower.CHMDStage16ZeroSideSymmetriesAndXiConvolutionAnnihilation

/-!
# CHMD Stage 17: Complexified Wave-Packet Factorization, Hyperbolic Cosh–Sinh Norm-Square Decomposition, and Strip Kinematics of `rhoC`

This module establishes **Stage 17** of the Causal Hyperbolic–Modular Duality (CHMD) route:

1. **Section 1 (The Complexified Wave-Packet Weight `complexTrigPacketWeight` and Its Exact Algebraic Identities):**
   - For any finite wave packet `t, c : Fin N → ℝ` and any complex frequency $w \in \mathbb{C}$, we
     define
     `complexTrigPacketWeight t c w = (∑ i, c i cos(t_i w))² + (∑ i, c i sin(t_i w))²`.
   - We prove that `complexTrigPacketWeight t c` restricts on `ℝ` to `trigPacketWeight t c`
     (`complexTrigPacketWeight_ofReal`), is even (`complexTrigPacketWeight_neg`) and Schwarz
     reflection-symmetric (`complexTrigPacketWeight_conj`), expands as the double cosine sum
     `∑ i, ∑ j, c i * c j * Complex.cos ((t j - t i) * w)`
     (`complexTrigPacketWeight_eq_sum_sum_cos`), and factors across the entire complex plane into
     the product of opposite Laplace–Fourier exponential sums:
     `complexTrigPacketWeight t c w = (∑ i, c i exp(I t_i w)) * (∑ j, c j exp(-I t_j w))`
     (`complexTrigPacketWeight_eq_exp_mul_exp`).

2. **Section 2 (Exact Factorization of `specSq (cosComb t c Φ) + specSq (sinComb t c Φ)` on `|z.im| < √2` and at All Nontrivial Zeros):**
   - On the strip `|z.im| < √2`, the combined wave-packet spectral square factors cleanly into the
     wave-packet factor `complexTrigPacketWeight t c (rhoC z)` times the single template square
     `specSq Φ z` (`specSq_cosComb_add_specSq_sinComb_eq_complexTrigPacketWeight_mul`,
     `specSq_cosComb_add_specSq_sinComb_gammaOf_eq_complexTrigPacketWeight_mul`).
   - Substituting this factorization into the unconditional zero-side formula of `CHMDStage15`
     expresses every finite Toeplitz quadratic form of `cosineShiftFn Λ Φ` directly as the zero-side
     series of `complexTrigPacketWeight t c (rhoC (gammaOf ρ)) * specSq Φ (gammaOf ρ)`
     (`sum_sum_cosineShiftFn_vonMangoldt_eq_tsum_complexTrigPacketWeight`,
     `sum_sum_cosineShiftFn_sechHalf_vonMangoldt_eq_tsum_complexTrigPacketWeight`).

3. **Section 3 (Exact Hyperbolic Cosh–Sinh Norm-Square Decomposition of `Re (complexTrigPacketWeight t c w)` and Strip Kinematics of `rhoC`):**
   - Decomposing $w = u + i v$ into real and imaginary parts, we define the nonnegative hyperbolic
     wave-packet norms
     `coshTrigPacketWeight t c u v = (∑ i, c i cosh(t_i v) cos(t_i u))² + (∑ i, c i cosh(t_i v) sin(t_i u))²`
     and
     `sinhTrigPacketWeight t c u v = (∑ i, c i sinh(t_i v) cos(t_i u))² + (∑ i, c i sinh(t_i v) sin(t_i u))²`,
     and prove the **Exact Hyperbolic Cosh–Sinh Norm-Square Identity**
     `(complexTrigPacketWeight t c w).re = coshTrigPacketWeight t c w.re w.im - sinhTrigPacketWeight t c w.re w.im`
     (`re_complexTrigPacketWeight_eq_cosh_sub_sinh`).
   - Finally, we establish the exact strip kinematics of `rhoC z = √(z² + 2)`:
     `(rhoC z).re ^ 2 - (rhoC z).im ^ 2 = z.re ^ 2 - z.im ^ 2 + 2`,
     `(rhoC z).re * (rhoC z).im = z.re * z.im`,
     `z.re ^ 2 + 7 / 4 ≤ (rhoC z).re ^ 2` on `|z.im| ≤ 1 / 2`, and
     `|(rhoC (gammaOf ρ)).im| < 1 / 2` for every nontrivial zero `ρ : zetaZeroConfig.carrier`
     (`re_rhoC_sq_sub_im_rhoC_sq`, `re_rhoC_mul_im_rhoC`,
     `seven_fourths_le_re_rhoC_sq_of_abs_im_le_half`, `abs_im_rhoC_lt_half_of_zero`).
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped Real ComplexConjugate Nat

noncomputable section

namespace RHTower.CHMDStage17

open WeilOneSided WeilSpectral RHTower.EvenSector RHTower.WeilPolarMajorant
open RHTower.CHMDStage1 RHTower.CHMDStage2 RHTower.CHMDStage3 RHTower.CHMDStage4
open RHTower.CHMDStage11 RHTower.CHMDStage12 RHTower.CHMDStage13 RHTower.CHMDStage14
open RHTower.CHMDStage15 RHTower.CHMDStage16
open GaloisForLFunctions.HTGeometry

/-! ## Section 1: The Complexified Wave-Packet Weight `complexTrigPacketWeight` -/

/-- The complexified trigonometric wave-packet weight
`complexTrigPacketWeight t c w = (∑ i, c i cos(t_i w))² + (∑ i, c i sin(t_i w))²`
for $w \in \mathbb{C}$. -/
def complexTrigPacketWeight {N : ℕ} (t c : Fin N → ℝ) (w : ℂ) : ℂ :=
  (∑ i : Fin N, (c i : ℂ) * Complex.cos ((t i : ℂ) * w)) ^ 2 +
    (∑ i : Fin N, (c i : ℂ) * Complex.sin ((t i : ℂ) * w)) ^ 2

/-- On the real line $\rho \in \mathbb{R}$, `complexTrigPacketWeight t c ρ` equals
`(trigPacketWeight t c ρ : ℂ)`. -/
theorem complexTrigPacketWeight_ofReal {N : ℕ} (t c : Fin N → ℝ) (ρ : ℝ) :
    complexTrigPacketWeight t c (ρ : ℂ) = (trigPacketWeight t c ρ : ℂ) := by
  unfold complexTrigPacketWeight trigPacketWeight
  push_cast
  rfl

/-- `complexTrigPacketWeight t c` is an even function on $\mathbb{C}$. -/
theorem complexTrigPacketWeight_neg {N : ℕ} (t c : Fin N → ℝ) (w : ℂ) :
    complexTrigPacketWeight t c (-w) = complexTrigPacketWeight t c w := by
  unfold complexTrigPacketWeight
  have hcos :
      (∑ i : Fin N, (c i : ℂ) * Complex.cos ((t i : ℂ) * -w)) =
        ∑ i : Fin N, (c i : ℂ) * Complex.cos ((t i : ℂ) * w) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_neg, Complex.cos_neg]
  have hsin :
      (∑ i : Fin N, (c i : ℂ) * Complex.sin ((t i : ℂ) * -w)) =
        -(∑ i : Fin N, (c i : ℂ) * Complex.sin ((t i : ℂ) * w)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_neg, Complex.sin_neg, mul_neg]
  rw [hcos, hsin, neg_sq]

/-- `complexTrigPacketWeight t c` is Schwarz reflection-symmetric on $\mathbb{C}$:
`complexTrigPacketWeight t c (conj w) = conj (complexTrigPacketWeight t c w)`. -/
theorem complexTrigPacketWeight_conj {N : ℕ} (t c : Fin N → ℝ) (w : ℂ) :
    complexTrigPacketWeight t c (conj w) = conj (complexTrigPacketWeight t c w) := by
  unfold complexTrigPacketWeight
  rw [map_add, map_pow, map_pow, map_sum, map_sum]
  congr 1 <;> congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_
  · rw [map_mul, Complex.conj_ofReal, ← Complex.cos_conj, map_mul, Complex.conj_ofReal]
  · rw [map_mul, Complex.conj_ofReal, ← Complex.sin_conj, map_mul, Complex.conj_ofReal]

/-- At $w = 0$, `complexTrigPacketWeight t c 0 = ((∑ i, c i) ^ 2 : ℂ)`. -/
theorem complexTrigPacketWeight_zero {N : ℕ} (t c : Fin N → ℝ) :
    complexTrigPacketWeight t c 0 = (((∑ i : Fin N, c i) ^ 2 : ℝ) : ℂ) := by
  rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp, complexTrigPacketWeight_ofReal, trigPacketWeight_zero]

/-- **Double-Sum Cosine Identity on $\mathbb{C}$**:
for every $w \in \mathbb{C}$,
`complexTrigPacketWeight t c w = ∑ i, ∑ j, (c i * c j : ℂ) * Complex.cos ((t j - t i) * w)`. -/
theorem complexTrigPacketWeight_eq_sum_sum_cos {N : ℕ} (t c : Fin N → ℝ) (w : ℂ) :
    complexTrigPacketWeight t c w =
      ∑ i : Fin N, ∑ j : Fin N,
        ((c i * c j : ℝ) : ℂ) * Complex.cos (((t j - t i : ℝ) : ℂ) * w) := by
  unfold complexTrigPacketWeight
  rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hsub : ((t j - t i : ℝ) : ℂ) * w = (t j : ℂ) * w - (t i : ℂ) * w := by
    push_cast; ring
  rw [hsub, Complex.cos_sub]
  push_cast
  ring

/-- **Opposite-Exponential Product Factorization on $\mathbb{C}$**:
for every $w \in \mathbb{C}$,
`complexTrigPacketWeight t c w = (∑ i, c i exp(t_i w I)) * (∑ j, c j exp(-(t_j w I)))`. -/
theorem complexTrigPacketWeight_eq_exp_mul_exp {N : ℕ} (t c : Fin N → ℝ) (w : ℂ) :
    complexTrigPacketWeight t c w =
      (∑ i : Fin N, (c i : ℂ) * Complex.exp (((t i : ℂ) * w) * I)) *
        (∑ j : Fin N, (c j : ℂ) * Complex.exp (-(((t j : ℂ) * w) * I))) := by
  have hpos :
      (∑ i : Fin N, (c i : ℂ) * Complex.exp (((t i : ℂ) * w) * I)) =
        (∑ i : Fin N, (c i : ℂ) * Complex.cos ((t i : ℂ) * w)) +
          I * (∑ i : Fin N, (c i : ℂ) * Complex.sin ((t i : ℂ) * w)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.exp_mul_I]
    ring
  have hneg :
      (∑ j : Fin N, (c j : ℂ) * Complex.exp (-(((t j : ℂ) * w) * I))) =
        (∑ j : Fin N, (c j : ℂ) * Complex.cos ((t j : ℂ) * w)) -
          I * (∑ j : Fin N, (c j : ℂ) * Complex.sin ((t j : ℂ) * w)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show -(((t j : ℂ) * w) * I) = (-(t j * w)) * I by ring, Complex.exp_mul_I,
      Complex.cos_neg, Complex.sin_neg]
    ring
  rw [hpos, hneg]
  unfold complexTrigPacketWeight
  linear_combination
    (∑ i : Fin N, (c i : ℂ) * Complex.sin ((t i : ℂ) * w)) ^ 2 * Complex.I_sq

/-! ## Section 2: Exact Factorization of `specSq (cosComb t c Φ) + specSq (sinComb t c Φ)` on `|z.im| < √2` and at All Zeros -/

/-- **Exact Strip Factorization of `specSq (cosComb t c Φ) + specSq (sinComb t c Φ)`**:
for every $\Phi : \mathbb{C} \to \mathbb{C}$ and every $z \in \mathbb{C}$ with $|z.\text{im}| < \sqrt{2}$,
`specSq (cosComb t c Φ) z + specSq (sinComb t c Φ) z = complexTrigPacketWeight t c (rhoC z) * specSq Φ z`. -/
theorem specSq_cosComb_add_specSq_sinComb_eq_complexTrigPacketWeight_mul
    {N : ℕ} (t c : Fin N → ℝ) (Φ : ℂ → ℂ) {z : ℂ} (hz : |z.im| < Real.sqrt 2) :
    specSq (cosComb t c Φ) z + specSq (sinComb t c Φ) z =
      complexTrigPacketWeight t c (rhoC z) * specSq Φ z := by
  rw [specSq_cosComb_add_specSq_sinComb t c Φ hz,
    complexTrigPacketWeight_eq_sum_sum_cos, Finset.sum_product, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold rhoCosShift
  ring

/-- **Exact Zero-Side Summand Factorization at Every Nontrivial Zero**:
for every $\Phi : \mathbb{C} \to \mathbb{C}$ and every nontrivial zero `ρ : zetaZeroConfig.carrier`
(on or off the critical line),
`specSq (cosComb t c Φ) (gammaOf ρ) + specSq (sinComb t c Φ) (gammaOf ρ) = complexTrigPacketWeight t c (rhoC (gammaOf ρ)) * specSq Φ (gammaOf ρ)`. -/
theorem specSq_cosComb_add_specSq_sinComb_gammaOf_eq_complexTrigPacketWeight_mul
    {N : ℕ} (t c : Fin N → ℝ) (Φ : ℂ → ℂ) (ρ : zetaZeroConfig.carrier) :
    specSq (cosComb t c Φ) (Zeta23.gammaOf ρ) + specSq (sinComb t c Φ) (Zeta23.gammaOf ρ) =
      complexTrigPacketWeight t c (rhoC (Zeta23.gammaOf ρ)) * specSq Φ (Zeta23.gammaOf ρ) := by
  have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hIm : |(Zeta23.gammaOf (ρ : ℂ)).im| < 1 / 2 :=
    WeilEF.abs_gammaOf_im_lt ⟨hmem.2.1, hmem.2.2⟩
  have h54 : |(Zeta23.gammaOf (ρ : ℂ)).im| ≤ 5 / 4 := by linarith
  exact specSq_cosComb_add_specSq_sinComb_eq_complexTrigPacketWeight_mul t c Φ
    (abs_im_lt_sqrt_two h54)

/-- **Unconditional Zero-Side Factored Series for the Toeplitz Quadratic Form of Any `EvenStrip Φ`**:
for every `EvenStrip Φ` and every finite wave packet `(t, c)`,
`∑ i, ∑ j, c i * c j * cosineShiftFn Λ Φ (t j - t i) = ∑' ρ, m_ρ * (complexTrigPacketWeight t c (rhoC (gammaOf ρ)) * specSq Φ (gammaOf ρ)).re`. -/
theorem sum_sum_cosineShiftFn_vonMangoldt_eq_tsum_complexTrigPacketWeight
    {Φ : ℂ → ℂ} (hΦ : EvenStrip Φ) {N : ℕ} (t c : Fin N → ℝ) :
    (∑ i, ∑ j, c i * c j *
        cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) Φ (t j - t i)) =
      ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) *
          (complexTrigPacketWeight t c (rhoC (Zeta23.gammaOf ρ)) *
            specSq Φ (Zeta23.gammaOf ρ)).re := by
  rw [sum_sum_cosineShiftFn_vonMangoldt_eq_tsum_re hΦ t c]
  refine tsum_congr fun ρ => ?_
  rw [specSq_cosComb_add_specSq_sinComb_gammaOf_eq_complexTrigPacketWeight_mul]

/-- **Unconditional Zero-Side Factored Series for the Decisive `sechHalf` Toeplitz Quadratic Form**:
for every finite wave packet `(t, c)`,
`∑ i, ∑ j, c i * c j * cosineShiftFn Λ sechHalf (t j - t i) = ∑' ρ, m_ρ * (complexTrigPacketWeight t c (rhoC (gammaOf ρ)) * specSq sechHalf (gammaOf ρ)).re`. -/
theorem sum_sum_cosineShiftFn_sechHalf_vonMangoldt_eq_tsum_complexTrigPacketWeight
    {N : ℕ} (t c : Fin N → ℝ) :
    (∑ i, ∑ j, c i * c j *
        cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf (t j - t i)) =
      ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) *
          (complexTrigPacketWeight t c (rhoC (Zeta23.gammaOf ρ)) *
            specSq sechHalf (Zeta23.gammaOf ρ)).re :=
  sum_sum_cosineShiftFn_vonMangoldt_eq_tsum_complexTrigPacketWeight evenStrip_sechHalf t c

/-! ## Section 3: Exact Hyperbolic Cosh–Sinh Norm-Square Decomposition and Strip Kinematics of `rhoC` -/

/-- The nonnegative hyperbolic `cosh`-weighted wave-packet norm square
`coshTrigPacketWeight t c u v = (∑ i, c i cosh(t_i v) cos(t_i u))² + (∑ i, c i cosh(t_i v) sin(t_i u))²`. -/
def coshTrigPacketWeight {N : ℕ} (t c : Fin N → ℝ) (u v : ℝ) : ℝ :=
  (∑ i : Fin N, c i * Real.cosh (t i * v) * Real.cos (t i * u)) ^ 2 +
    (∑ i : Fin N, c i * Real.cosh (t i * v) * Real.sin (t i * u)) ^ 2

/-- The nonnegative hyperbolic `sinh`-weighted wave-packet norm square
`sinhTrigPacketWeight t c u v = (∑ i, c i sinh(t_i v) cos(t_i u))² + (∑ i, c i sinh(t_i v) sin(t_i u))²`. -/
def sinhTrigPacketWeight {N : ℕ} (t c : Fin N → ℝ) (u v : ℝ) : ℝ :=
  (∑ i : Fin N, c i * Real.sinh (t i * v) * Real.cos (t i * u)) ^ 2 +
    (∑ i : Fin N, c i * Real.sinh (t i * v) * Real.sin (t i * u)) ^ 2

theorem coshTrigPacketWeight_nonneg {N : ℕ} (t c : Fin N → ℝ) (u v : ℝ) :
    0 ≤ coshTrigPacketWeight t c u v :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem sinhTrigPacketWeight_nonneg {N : ℕ} (t c : Fin N → ℝ) (u v : ℝ) :
    0 ≤ sinhTrigPacketWeight t c u v :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem coshTrigPacketWeight_zero_right {N : ℕ} (t c : Fin N → ℝ) (u : ℝ) :
    coshTrigPacketWeight t c u 0 = trigPacketWeight t c u := by
  unfold coshTrigPacketWeight trigPacketWeight
  simp

theorem sinhTrigPacketWeight_zero_right {N : ℕ} (t c : Fin N → ℝ) (u : ℝ) :
    sinhTrigPacketWeight t c u 0 = 0 := by
  unfold sinhTrigPacketWeight
  simp

/-- Real and imaginary parts of `Complex.cos ((a : ℂ) + b * I)` for $a, b \in \mathbb{R}$. -/
theorem cos_ofReal_add_mul_I (a b : ℝ) :
    Complex.cos ((a : ℂ) + (b : ℂ) * I) =
      ((Real.cos a * Real.cosh b : ℝ) : ℂ) - ((Real.sin a * Real.sinh b : ℝ) : ℂ) * I := by
  rw [Complex.cos_add, Complex.cos_mul_I, Complex.sin_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  push_cast
  ring

/-- Real and imaginary parts of `Complex.sin ((a : ℂ) + b * I)` for $a, b \in \mathbb{R}$. -/
theorem sin_ofReal_add_mul_I (a b : ℝ) :
    Complex.sin ((a : ℂ) + (b : ℂ) * I) =
      ((Real.sin a * Real.cosh b : ℝ) : ℂ) + ((Real.cos a * Real.sinh b : ℝ) : ℂ) * I := by
  rw [Complex.sin_add, Complex.cos_mul_I, Complex.sin_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  push_cast
  ring

/-- **Exact Hyperbolic Cosh–Sinh Norm-Square Decomposition of `Re (complexTrigPacketWeight t c w)`**:
for every $w \in \mathbb{C}$,
`(complexTrigPacketWeight t c w).re = coshTrigPacketWeight t c w.re w.im - sinhTrigPacketWeight t c w.re w.im`. -/
theorem re_complexTrigPacketWeight_eq_cosh_sub_sinh {N : ℕ} (t c : Fin N → ℝ) (w : ℂ) :
    (complexTrigPacketWeight t c w).re =
      coshTrigPacketWeight t c w.re w.im - sinhTrigPacketWeight t c w.re w.im := by
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
  unfold complexTrigPacketWeight coshTrigPacketWeight sinhTrigPacketWeight
  rw [hcos, hsin, sq, sq]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.sub_im, Complex.add_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, add_zero, zero_add, mul_one, sub_zero]
  ring

/-- For every $z \in \mathbb{C}$,
`(rhoC z).re ^ 2 - (rhoC z).im ^ 2 = z.re ^ 2 - z.im ^ 2 + 2`. -/
theorem re_rhoC_sq_sub_im_rhoC_sq (z : ℂ) :
    (rhoC z).re ^ 2 - (rhoC z).im ^ 2 = z.re ^ 2 - z.im ^ 2 + 2 := by
  have h := congrArg Complex.re (rhoC_sq z)
  simp only [sq, Complex.mul_re, Complex.add_re, Complex.re_ofNat] at h ⊢
  linarith

/-- For every $z \in \mathbb{C}$,
`(rhoC z).re * (rhoC z).im = z.re * z.im`. -/
theorem re_rhoC_mul_im_rhoC (z : ℂ) :
    (rhoC z).re * (rhoC z).im = z.re * z.im := by
  have h := congrArg Complex.im (rhoC_sq z)
  simp only [sq, Complex.mul_im, Complex.add_im, Complex.im_ofNat] at h
  linarith

/-- On `|z.im| ≤ 1 / 2`, `z.re ^ 2 + 7 / 4 ≤ (rhoC z).re ^ 2`. -/
theorem seven_fourths_le_re_rhoC_sq_of_abs_im_le_half {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    z.re ^ 2 + 7 / 4 ≤ (rhoC z).re ^ 2 := by
  have hre := re_rhoC_sq_sub_im_rhoC_sq z
  have him : z.im ^ 2 ≤ 1 / 4 := by
    have := sq_abs z.im
    nlinarith [abs_nonneg z.im]
  have h0 : 0 ≤ (rhoC z).im ^ 2 := sq_nonneg _
  linarith

/-- For every nontrivial zero `ρ : zetaZeroConfig.carrier`,
`|(rhoC (gammaOf ρ)).im| < 1 / 2`. -/
theorem abs_im_rhoC_lt_half_of_zero (ρ : zetaZeroConfig.carrier) :
    |(rhoC (Zeta23.gammaOf ρ)).im| < 1 / 2 := by
  have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
  exact (abs_im_rhoC_le (Zeta23.gammaOf ρ)).trans_lt
    (WeilEF.abs_gammaOf_im_lt ⟨hmem.2.1, hmem.2.2⟩)

end RHTower.CHMDStage17

end
