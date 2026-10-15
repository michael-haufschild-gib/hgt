import GaloisForLFunctions.RHTower.CHMDStage12FourModeDigammaToeplitzCoercivity

/-!
# CHMD Stage 13: Pointwise `cosineShiftFn` Formula, 2-Point Toeplitz Packets, and Polar Node Elimination

This module establishes the thirteenth stage of the **Causal Hyperbolic–Modular Duality (CHMD)**
formalization in `RHTower`, deriving the exact pointwise spectral decomposition of
`cosineShiftFn lam sechHalf y`, the 2-point difference and sum Toeplitz wave packets, and the
polar node-elimination laws at the harmonic shifts $y_k = \frac{2\pi k}{\sqrt{7/4}}$ and
$y_{k+1/2} = \frac{\pi(2k+1)}{\sqrt{7/4}}$ ($k \in \mathbb{Z}$):

1. **Exact Pointwise Spectral Evaluation of `rhoCosShift y Φ` and `cosineShiftFn lam sechHalf y`**:
   - Proves that at the poles $z = \pm i/2$,
     $$\operatorname{evenPolePart}(\operatorname{rhoCosShift}\ y\ \Phi)
       = \cos\bigl(y\sqrt{7/4}\bigr)\,\operatorname{evenPolePart}(\operatorname{specSq}\ \Phi),$$
     and for `Φ = sechHalf`,
     $$\operatorname{evenPolePart}(\operatorname{rhoCosShift}\ y\ \operatorname{sechHalf})
       = \frac{2}{\cos^2(1/4)} \cos\bigl(y\sqrt{7/4}\bigr)$$
     (`evenPolePart_rhoCosShift`, `evenPolePart_rhoCosShift_sechHalf`).
   - Proves the exact pointwise formula for `(rhoCosShift y Φ r).re` on the real line and the
     resulting three-part and 4-mode shifted decompositions of `cosineShiftFn lam sechHalf y`
     (`rhoCosShift_ofReal_re`, `rhoCosShift_sechHalf_ofReal_re`, `cosineShiftFn_sechHalf_eq`,
     `cosineShiftFn_sechHalf_eq_fourModeShifted_parts`).

2. **2-Point Difference and Sum Toeplitz Wave Packets (`N = 2`)**:
   - Defines the 2-point shift vector `twoPointShift y := ![0, y]` and coefficient vectors
     `twoPointDiffCoeff := ![1, -1]` and `twoPointSumCoeff := ![1, 1]`.
   - Proves the exact trigonometric identities:
     $$\operatorname{trigPacketWeight}\ ![0, y]\ ![1, -1]\ \rho
       = 2(1 - \cos(y\rho)) = 4\sin^2(y\rho / 2),$$
     $$\operatorname{trigPacketWeight}\ ![0, y]\ ![1, 1]\ \rho
       = 2(1 + \cos(y\rho)) = 4\cos^2(y\rho / 2)$$
     (`trigPacketWeight_twoPointDiff`, `trigPacketWeight_twoPointDiff_eq_four_mul_sin_sq`,
     `trigPacketWeight_twoPointSum`, `trigPacketWeight_twoPointSum_eq_four_mul_cos_sq`).
   - Proves the exact Toeplitz quadratic form identities:
     $$\sum_{i, j \in \operatorname{Fin} 2} c^-_i c^-_j \operatorname{cosineShiftFn}\ \lambda\ \Phi\ (t_j - t_i)
       = 2\bigl(\operatorname{cosineShiftFn}\ \lambda\ \Phi\ 0 - \operatorname{cosineShiftFn}\ \lambda\ \Phi\ y\bigr),$$
     $$\sum_{i, j \in \operatorname{Fin} 2} c^+_i c^+_j \operatorname{cosineShiftFn}\ \lambda\ \Phi\ (t_j - t_i)
       = 2\bigl(\operatorname{cosineShiftFn}\ \lambda\ \Phi\ 0 + \operatorname{cosineShiftFn}\ \lambda\ \Phi\ y\bigr)$$
     (`sum_sum_twoPointDiff_cosineShiftFn`, `sum_sum_twoPointSum_cosineShiftFn`).

3. **Polar Node and Anti-Node Elimination Shifts (`polarNodeShift`, `polarAntiNodeShift`)**:
   - Defines `polarNodeShift (k : ℤ) : ℝ := 2 * Real.pi * k / Real.sqrt (7 / 4)` and
     `polarAntiNodeShift (k : ℤ) : ℝ := Real.pi * (2 * k + 1) / Real.sqrt (7 / 4)`.
   - Proves `Real.cos (polarNodeShift k * Real.sqrt (7 / 4)) = 1` and
     `Real.cos (polarAntiNodeShift k * Real.sqrt (7 / 4)) = -1`, so that
     `trigPacketWeight ![0, polarNodeShift k] ![1, -1] (Real.sqrt (7 / 4)) = 0` and
     `trigPacketWeight ![0, polarAntiNodeShift k] ![1, 1] (Real.sqrt (7 / 4)) = 0`.
   - Deduces the pole-cancelled difference and sum formulas at `polarNodeShift k` and
     `polarAntiNodeShift k`, as well as the general pole-free Toeplitz formula for any wave packet
     annihilating $\rho_{\text{pole}} = \sqrt{7/4}$ (`sum_sum_cosineShiftFn_sechHalf_of_pole_zero`,
     `cosineShiftFn_sechHalf_zero_sub_polarNodeShift_eq`,
     `cosineShiftFn_sechHalf_zero_add_polarAntiNodeShift_eq`).
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped BigOperators ComplexConjugate

noncomputable section

namespace RHTower.CHMDStage13

open WeilOneSided WeilSpectral GaloisForLFunctions.HTGeometry RHTower.EvenSector
open RHTower.CHMDStage1 RHTower.CHMDStage3 RHTower.CHMDStage4
open RHTower.CHMDStage11 RHTower.CHMDStage12

/-! ## Section 1: Pointwise Spectral Evaluation of `rhoCosShift y Φ` and `cosineShiftFn lam sechHalf y` -/

/-- At $z = \pm i/2$, `Complex.cos (y * rhoC (±I / 2))` equals `Real.cos (y * Real.sqrt (7 / 4))`. -/
theorem cos_mul_rhoC_I_div_two (y : ℝ) :
    Complex.cos (y * rhoC (I / 2)) = (Real.cos (y * Real.sqrt (7 / 4)) : ℂ) := by
  rw [rhoC_I_div_two, ← Complex.ofReal_mul, Complex.ofReal_cos]

theorem cos_mul_rhoC_neg_I_div_two (y : ℝ) :
    Complex.cos (y * rhoC (-I / 2)) = (Real.cos (y * Real.sqrt (7 / 4)) : ℂ) := by
  rw [rhoC_neg_I_div_two, ← Complex.ofReal_mul, Complex.ofReal_cos]

/-- **Pole Evaluation of `rhoCosShift y Φ`**:
for any `Φ : ℂ → ℂ` and `y ∈ ℝ`,
`evenPolePart (rhoCosShift y Φ) = Real.cos (y * Real.sqrt (7 / 4)) * evenPolePart (specSq Φ)`. -/
theorem evenPolePart_rhoCosShift (y : ℝ) (Φ : ℂ → ℂ) :
    evenPolePart (rhoCosShift y Φ) =
      Real.cos (y * Real.sqrt (7 / 4)) * evenPolePart (specSq Φ) := by
  unfold evenPolePart rhoCosShift
  rw [cos_mul_rhoC_I_div_two, cos_mul_rhoC_neg_I_div_two,
    ← mul_add, Complex.re_ofReal_mul]

/-- **Pole Evaluation of `rhoCosShift y sechHalf`**:
for every `y ∈ ℝ`,
`evenPolePart (rhoCosShift y sechHalf) = (2 / Real.cos (1 / 4) ^ 2) * Real.cos (y * Real.sqrt (7 / 4))`. -/
theorem evenPolePart_rhoCosShift_sechHalf (y : ℝ) :
    evenPolePart (rhoCosShift y sechHalf) =
      (2 / Real.cos (1 / 4 : ℝ) ^ 2) * Real.cos (y * Real.sqrt (7 / 4)) := by
  rw [evenPolePart_rhoCosShift, evenPolePart_specSq_sechHalf, mul_comm]

/-- On the real line $z = (r : \mathbb{C})$,
`(rhoCosShift y Φ r).re = Real.cos (y * Real.sqrt (r ^ 2 + 2)) * ‖Φ r‖ ^ 2`. -/
theorem rhoCosShift_ofReal_re (y : ℝ) (Φ : ℂ → ℂ) (r : ℝ) :
    (rhoCosShift y Φ r).re = Real.cos (y * Real.sqrt (r ^ 2 + 2)) * ‖Φ r‖ ^ 2 := by
  unfold rhoCosShift
  rw [re_cos_mul_ofReal, specSq_re_ofReal]

/-- On the real line $z = (r : \mathbb{C})$,
`(rhoCosShift y sechHalf r).re = Real.cos (y * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r`. -/
theorem rhoCosShift_sechHalf_ofReal_re (y r : ℝ) :
    (rhoCosShift y sechHalf r).re =
      Real.cos (y * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r := by
  rw [rhoCosShift_ofReal_re, norm_sechHalf_ofReal_sq]

/-- **Archimedean Part of `rhoCosShift y sechHalf`**:
`evenArchPart (rhoCosShift y sechHalf) = ∫ r, cos(y √(r² + 2)) * sechSqHalf r * EF.gammaBracket r`. -/
theorem evenArchPart_rhoCosShift_sechHalf (y : ℝ) :
    evenArchPart (rhoCosShift y sechHalf) =
      ∫ r : ℝ, Real.cos (y * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * EF.gammaBracket r := by
  unfold evenArchPart
  simp_rw [rhoCosShift_sechHalf_ofReal_re]

/-- **4-Mode Splitting of `evenArchPart (rhoCosShift y sechHalf)`**:
splits `evenArchPart (rhoCosShift y sechHalf)` into the `fourModeShiftedArchDensity` integral minus
the `fourModeGaussSpectralWeight` integral. -/
theorem evenArchPart_rhoCosShift_sechHalf_eq_fourModeShifted_sub_gauss (y : ℝ) :
    evenArchPart (rhoCosShift y sechHalf) =
      (∫ r : ℝ, Real.cos (y * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
        fourModeShiftedArchDensity r) -
      (∫ r : ℝ, Real.cos (y * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
        fourModeGaussSpectralWeight r) := by
  have h := evenArchPart_eq_fourModeShifted_sub_gauss (goodDensity_cosShift y evenStrip_sechHalf)
  simpa only [rhoCosShift_sechHalf_ofReal_re] using h

/-- **Prime Part of `rhoCosShift y sechHalf`**:
expresses `evenPrimePart lam (rhoCosShift y sechHalf)` in terms of `sechSqHalf`. -/
theorem evenPrimePart_rhoCosShift_sechHalf (lam : ℕ → ℝ) (y : ℝ) :
    evenPrimePart lam (rhoCosShift y sechHalf) =
      ∑' n : ℕ, (if 2 ≤ n then lam n / Real.sqrt n else 0) *
        (1 / Real.pi * ∫ r : ℝ,
          Real.cos (y * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * Real.cos (r * Real.log n)) := by
  unfold evenPrimePart
  simp_rw [rhoCosShift_sechHalf_ofReal_re]

/-- **Exact Pointwise Three-Part Spectral Formula for `cosineShiftFn lam sechHalf y`**:
for every `y ∈ ℝ`, `cosineShiftFn lam sechHalf y` decomposes into the pole cosine
`(2 / cos(1/4)²) * cos(y √(7/4))`, the archimedean integral, and the prime series. -/
theorem cosineShiftFn_sechHalf_eq (lam : ℕ → ℝ) (y : ℝ) :
    cosineShiftFn lam sechHalf y =
      (2 / Real.cos (1 / 4 : ℝ) ^ 2) * Real.cos (y * Real.sqrt (7 / 4)) +
        1 / (2 * Real.pi) *
          (∫ r : ℝ, Real.cos (y * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * EF.gammaBracket r) -
        ∑' n : ℕ, (if 2 ≤ n then lam n / Real.sqrt n else 0) *
          (1 / Real.pi * ∫ r : ℝ,
            Real.cos (y * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * Real.cos (r * Real.log n)) := by
  unfold cosineShiftFn
  rw [evenWeilDensity_eq_parts, evenPolePart_rhoCosShift_sechHalf,
    evenArchPart_rhoCosShift_sechHalf, evenPrimePart_rhoCosShift_sechHalf]

/-- **Exact Pointwise 4-Mode Decomposition for `cosineShiftFn lam sechHalf y`**:
for every `y ∈ ℝ`, `cosineShiftFn lam sechHalf y` decomposes into the pole cosine plus the
4-mode shifted archimedean integral minus the 4-mode Lorentzian integral and prime series. -/
theorem cosineShiftFn_sechHalf_eq_fourModeShifted_parts (lam : ℕ → ℝ) (y : ℝ) :
    cosineShiftFn lam sechHalf y =
      (2 / Real.cos (1 / 4 : ℝ) ^ 2) * Real.cos (y * Real.sqrt (7 / 4)) +
        1 / (2 * Real.pi) *
          (∫ r : ℝ, Real.cos (y * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
            fourModeShiftedArchDensity r) -
        (1 / (2 * Real.pi) *
          (∫ r : ℝ, Real.cos (y * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
            fourModeGaussSpectralWeight r) +
        ∑' n : ℕ, (if 2 ≤ n then lam n / Real.sqrt n else 0) *
          (1 / Real.pi * ∫ r : ℝ,
            Real.cos (y * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * Real.cos (r * Real.log n))) := by
  unfold cosineShiftFn
  rw [evenWeilDensity_eq_parts, evenPolePart_rhoCosShift_sechHalf,
    evenArchPart_rhoCosShift_sechHalf_eq_fourModeShifted_sub_gauss,
    evenPrimePart_rhoCosShift_sechHalf]
  ring

/-! ## Section 2: 2-Point Difference and Sum Toeplitz Wave Packets (`N = 2`) -/

/-- The 2-point shift vector `![0, y] : Fin 2 → ℝ`. -/
def twoPointShift (y : ℝ) : Fin 2 → ℝ := ![0, y]

/-- The 2-point difference coefficient vector `![1, -1] : Fin 2 → ℝ`. -/
def twoPointDiffCoeff : Fin 2 → ℝ := ![1, -1]

/-- The 2-point sum coefficient vector `![1, 1] : Fin 2 → ℝ`. -/
def twoPointSumCoeff : Fin 2 → ℝ := ![1, 1]

/-- **Spectral Weight of the 2-Point Difference Packet**:
`trigPacketWeight ![0, y] ![1, -1] ρ = 2 * (1 - Real.cos (y * ρ))`. -/
theorem trigPacketWeight_twoPointDiff (y ρ : ℝ) :
    trigPacketWeight (twoPointShift y) twoPointDiffCoeff ρ =
      2 * (1 - Real.cos (y * ρ)) := by
  unfold trigPacketWeight twoPointShift twoPointDiffCoeff
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    zero_mul, Real.cos_zero, Real.sin_zero, mul_one, mul_zero, zero_add, neg_one_mul]
  have hpyth := Real.cos_sq_add_sin_sq (y * ρ)
  linarith

/-- **Sine-Squared Form of the 2-Point Difference Packet Weight**:
`trigPacketWeight ![0, y] ![1, -1] ρ = 4 * Real.sin (y * ρ / 2) ^ 2`. -/
theorem trigPacketWeight_twoPointDiff_eq_four_mul_sin_sq (y ρ : ℝ) :
    trigPacketWeight (twoPointShift y) twoPointDiffCoeff ρ =
      4 * Real.sin (y * ρ / 2) ^ 2 := by
  rw [trigPacketWeight_twoPointDiff]
  have h := Real.cos_two_mul' (y * ρ / 2)
  have h2 : 2 * (y * ρ / 2) = y * ρ := by ring
  rw [h2] at h
  have hpyth := Real.cos_sq_add_sin_sq (y * ρ / 2)
  linarith

/-- **Spectral Weight of the 2-Point Sum Packet**:
`trigPacketWeight ![0, y] ![1, 1] ρ = 2 * (1 + Real.cos (y * ρ))`. -/
theorem trigPacketWeight_twoPointSum (y ρ : ℝ) :
    trigPacketWeight (twoPointShift y) twoPointSumCoeff ρ =
      2 * (1 + Real.cos (y * ρ)) := by
  unfold trigPacketWeight twoPointShift twoPointSumCoeff
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    zero_mul, Real.cos_zero, Real.sin_zero, mul_one, mul_zero, zero_add, one_mul]
  have hpyth := Real.cos_sq_add_sin_sq (y * ρ)
  linarith

/-- **Cosine-Squared Form of the 2-Point Sum Packet Weight**:
`trigPacketWeight ![0, y] ![1, 1] ρ = 4 * Real.cos (y * ρ / 2) ^ 2`. -/
theorem trigPacketWeight_twoPointSum_eq_four_mul_cos_sq (y ρ : ℝ) :
    trigPacketWeight (twoPointShift y) twoPointSumCoeff ρ =
      4 * Real.cos (y * ρ / 2) ^ 2 := by
  rw [trigPacketWeight_twoPointSum]
  have h := Real.cos_two_mul (y * ρ / 2)
  have h2 : 2 * (y * ρ / 2) = y * ρ := by ring
  rw [h2] at h
  linarith

/-- **Toeplitz Form of the 2-Point Difference Packet**:
for any `lam`, `Φ`, and `y ∈ ℝ`,
`∑ i, ∑ j, c⁻_i c⁻_j cosineShiftFn lam Φ (t_j - t_i) = 2 * (cosineShiftFn lam Φ 0 - cosineShiftFn lam Φ y)`. -/
theorem sum_sum_twoPointDiff_cosineShiftFn (lam : ℕ → ℝ) (Φ : ℂ → ℂ) (y : ℝ) :
    (∑ i, ∑ j, twoPointDiffCoeff i * twoPointDiffCoeff j *
      cosineShiftFn lam Φ (twoPointShift y j - twoPointShift y i)) =
      2 * (cosineShiftFn lam Φ 0 - cosineShiftFn lam Φ y) := by
  unfold twoPointShift twoPointDiffCoeff
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    sub_self, sub_zero, zero_sub, cosineShiftFn_neg]
  ring

/-- **Toeplitz Form of the 2-Point Sum Packet**:
for any `lam`, `Φ`, and `y ∈ ℝ`,
`∑ i, ∑ j, c⁺_i c⁺_j cosineShiftFn lam Φ (t_j - t_i) = 2 * (cosineShiftFn lam Φ 0 + cosineShiftFn lam Φ y)`. -/
theorem sum_sum_twoPointSum_cosineShiftFn (lam : ℕ → ℝ) (Φ : ℂ → ℂ) (y : ℝ) :
    (∑ i, ∑ j, twoPointSumCoeff i * twoPointSumCoeff j *
      cosineShiftFn lam Φ (twoPointShift y j - twoPointShift y i)) =
      2 * (cosineShiftFn lam Φ 0 + cosineShiftFn lam Φ y) := by
  unfold twoPointShift twoPointSumCoeff
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    sub_self, sub_zero, zero_sub, cosineShiftFn_neg]
  ring

/-- **Polarization Identity Expressing `cosineShiftFn lam Φ y` via 2-Point Sum and Difference Packets**:
`cosineShiftFn lam Φ y` is one-fourth of the 2-point sum Toeplitz form minus the 2-point difference
Toeplitz form. -/
theorem cosineShiftFn_eq_quarter_twoPointSum_sub_twoPointDiff (lam : ℕ → ℝ) (Φ : ℂ → ℂ) (y : ℝ) :
    cosineShiftFn lam Φ y =
      (1 / 4 : ℝ) *
        ((∑ i, ∑ j, twoPointSumCoeff i * twoPointSumCoeff j *
            cosineShiftFn lam Φ (twoPointShift y j - twoPointShift y i)) -
          (∑ i, ∑ j, twoPointDiffCoeff i * twoPointDiffCoeff j *
            cosineShiftFn lam Φ (twoPointShift y j - twoPointShift y i))) := by
  rw [sum_sum_twoPointSum_cosineShiftFn, sum_sum_twoPointDiff_cosineShiftFn]
  ring

/-! ## Section 3: Polar Node and Anti-Node Elimination Shifts (`polarNodeShift`, `polarAntiNodeShift`) -/

/-- **Polar Node-Elimination Shift** $y_k = \frac{2\pi k}{\sqrt{7/4}}$ ($k \in \mathbb{Z}$), at which
the pole frequency $\rho_{\text{pole}} = \sqrt{7/4}$ completes $k$ full periods so that
$1 - \cos(y_k \sqrt{7/4}) = 0$. -/
def polarNodeShift (k : ℤ) : ℝ := 2 * Real.pi * (k : ℝ) / Real.sqrt (7 / 4)

/-- **Polar Anti-Node Shift** $y_{k+1/2} = \frac{\pi(2k+1)}{\sqrt{7/4}}$ ($k \in \mathbb{Z}$), at which
$1 + \cos(y_{k+1/2} \sqrt{7/4}) = 0$. -/
def polarAntiNodeShift (k : ℤ) : ℝ := Real.pi * (2 * (k : ℝ) + 1) / Real.sqrt (7 / 4)

/-- `polarNodeShift k * Real.sqrt (7 / 4) = 2 * Real.pi * k`. -/
theorem polarNodeShift_mul_sqrt_seven_fourths (k : ℤ) :
    polarNodeShift k * Real.sqrt (7 / 4) = 2 * Real.pi * (k : ℝ) := by
  unfold polarNodeShift
  have hne : Real.sqrt (7 / 4 : ℝ) ≠ 0 := by positivity
  exact div_mul_cancel₀ _ hne

/-- `polarAntiNodeShift k * Real.sqrt (7 / 4) = Real.pi * (2 * k + 1)`. -/
theorem polarAntiNodeShift_mul_sqrt_seven_fourths (k : ℤ) :
    polarAntiNodeShift k * Real.sqrt (7 / 4) = Real.pi * (2 * (k : ℝ) + 1) := by
  unfold polarAntiNodeShift
  have hne : Real.sqrt (7 / 4 : ℝ) ≠ 0 := by positivity
  exact div_mul_cancel₀ _ hne

/-- At every polar node $y_k = \frac{2\pi k}{\sqrt{7/4}}$, $\cos(y_k \sqrt{7/4}) = 1$. -/
theorem cos_polarNodeShift_mul_sqrt_seven_fourths (k : ℤ) :
    Real.cos (polarNodeShift k * Real.sqrt (7 / 4)) = 1 := by
  rw [polarNodeShift_mul_sqrt_seven_fourths,
    show 2 * Real.pi * (k : ℝ) = (k : ℝ) * (2 * Real.pi) by ring,
    Real.cos_int_mul_two_pi]

/-- At every polar anti-node $y_{k+1/2} = \frac{\pi(2k+1)}{\sqrt{7/4}}$,
$\cos(y_{k+1/2} \sqrt{7/4}) = -1$. -/
theorem cos_polarAntiNodeShift_mul_sqrt_seven_fourths (k : ℤ) :
    Real.cos (polarAntiNodeShift k * Real.sqrt (7 / 4)) = -1 := by
  rw [polarAntiNodeShift_mul_sqrt_seven_fourths,
    show Real.pi * (2 * (k : ℝ) + 1) = Real.pi + (k : ℝ) * (2 * Real.pi) by ring,
    Real.cos_add_int_mul_two_pi, Real.cos_pi]

/-- **Exact Pole Annihilation of the 2-Point Difference Packet at `polarNodeShift k`**:
`trigPacketWeight ![0, polarNodeShift k] ![1, -1] (Real.sqrt (7 / 4)) = 0`. -/
theorem trigPacketWeight_twoPointDiff_polarNodeShift_eq_zero (k : ℤ) :
    trigPacketWeight (twoPointShift (polarNodeShift k)) twoPointDiffCoeff
      (Real.sqrt (7 / 4)) = 0 := by
  rw [trigPacketWeight_twoPointDiff, cos_polarNodeShift_mul_sqrt_seven_fourths]
  ring

/-- **Exact Pole Annihilation of the 2-Point Sum Packet at `polarAntiNodeShift k`**:
`trigPacketWeight ![0, polarAntiNodeShift k] ![1, 1] (Real.sqrt (7 / 4)) = 0`. -/
theorem trigPacketWeight_twoPointSum_polarAntiNodeShift_eq_zero (k : ℤ) :
    trigPacketWeight (twoPointShift (polarAntiNodeShift k)) twoPointSumCoeff
      (Real.sqrt (7 / 4)) = 0 := by
  rw [trigPacketWeight_twoPointSum, cos_polarAntiNodeShift_mul_sqrt_seven_fourths]
  ring

/-- At `polarNodeShift k`, `evenPolePart (rhoCosShift (polarNodeShift k) sechHalf)` equals the
unshifted pole constant `2 / Real.cos (1 / 4) ^ 2`. -/
theorem evenPolePart_rhoCosShift_polarNodeShift (k : ℤ) :
    evenPolePart (rhoCosShift (polarNodeShift k) sechHalf) =
      2 / Real.cos (1 / 4 : ℝ) ^ 2 := by
  rw [evenPolePart_rhoCosShift_sechHalf, cos_polarNodeShift_mul_sqrt_seven_fourths, mul_one]

/-- At `polarAntiNodeShift k`, `evenPolePart (rhoCosShift (polarAntiNodeShift k) sechHalf)` equals
`-(2 / Real.cos (1 / 4) ^ 2)`. -/
theorem evenPolePart_rhoCosShift_polarAntiNodeShift (k : ℤ) :
    evenPolePart (rhoCosShift (polarAntiNodeShift k) sechHalf) =
      -(2 / Real.cos (1 / 4 : ℝ) ^ 2) := by
  rw [evenPolePart_rhoCosShift_sechHalf, cos_polarAntiNodeShift_mul_sqrt_seven_fourths]
  ring

/-! ## Section 4: Pole-Free Toeplitz Formulas for General Pole-Annihilating Packets and Polar Nodes -/

/-- **General Pole-Free Toeplitz Formula for Pole-Annihilating Wave Packets**:
for any wave packet `(t, c)` satisfying `trigPacketWeight t c (Real.sqrt (7 / 4)) = 0`, the pole
term in the `sechHalf` Toeplitz quadratic form vanishes identically, leaving only the archimedean
integral minus the prime series. -/
theorem sum_sum_cosineShiftFn_sechHalf_of_pole_zero {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {N : ℕ}
    (t c : Fin N → ℝ) (hpole : trigPacketWeight t c (Real.sqrt (7 / 4)) = 0) :
    (∑ i, ∑ j, c i * c j * cosineShiftFn lam sechHalf (t j - t i)) =
      1 / (2 * Real.pi) *
          (∫ r : ℝ, trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
            EF.gammaBracket r) -
        ∑' n : ℕ, (if 2 ≤ n then lam n / Real.sqrt n else 0) *
          (1 / Real.pi * ∫ r : ℝ,
            trigPacketWeight t c (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
              Real.cos (r * Real.log n)) := by
  rw [sum_sum_cosineShiftFn_sechHalf_eq_trigPacketWeight_parts hg t c, hpole, mul_zero, zero_add]

/-- **General Pole-Free 4-Mode Decomposition for Pole-Annihilating Wave Packets**:
when `trigPacketWeight t c (Real.sqrt (7 / 4)) = 0`, the `sechHalf` Toeplitz quadratic form equals
the coercive `fourModeShiftedArchDensity` integral minus the `fourModeGaussSpectralWeight` integral
and prime series. -/
theorem sum_sum_cosineShiftFn_sechHalf_eq_fourModeShifted_of_pole_zero {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {N : ℕ}
    (t c : Fin N → ℝ) (hpole : trigPacketWeight t c (Real.sqrt (7 / 4)) = 0) :
    (∑ i, ∑ j, c i * c j * cosineShiftFn lam sechHalf (t j - t i)) =
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
  rw [sum_sum_cosineShiftFn_sechHalf_eq_fourModeShifted_parts hg t c, hpole, mul_zero, zero_add]

/-- **Pole-Cancelled Difference Formula at `polarNodeShift k`**:
at every polar node $y_k = \frac{2\pi k}{\sqrt{7/4}}$ ($k \in \mathbb{Z}$), the pole contribution in
`2 * (cosineShiftFn lam sechHalf 0 - cosineShiftFn lam sechHalf (polarNodeShift k))` vanishes
identically. -/
theorem two_mul_cosineShiftFn_sechHalf_zero_sub_polarNodeShift_eq {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) (k : ℤ) :
    2 * (cosineShiftFn lam sechHalf 0 - cosineShiftFn lam sechHalf (polarNodeShift k)) =
      1 / (2 * Real.pi) *
          (∫ r : ℝ,
            trigPacketWeight (twoPointShift (polarNodeShift k)) twoPointDiffCoeff
              (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * fourModeShiftedArchDensity r) -
        (1 / (2 * Real.pi) *
          (∫ r : ℝ,
            trigPacketWeight (twoPointShift (polarNodeShift k)) twoPointDiffCoeff
              (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * fourModeGaussSpectralWeight r) +
        ∑' n : ℕ, (if 2 ≤ n then lam n / Real.sqrt n else 0) *
          (1 / Real.pi * ∫ r : ℝ,
            trigPacketWeight (twoPointShift (polarNodeShift k)) twoPointDiffCoeff
              (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * Real.cos (r * Real.log n))) := by
  rw [← sum_sum_twoPointDiff_cosineShiftFn,
    sum_sum_cosineShiftFn_sechHalf_eq_fourModeShifted_of_pole_zero hg _ _
      (trigPacketWeight_twoPointDiff_polarNodeShift_eq_zero k)]

/-- **Pole-Cancelled Sum Formula at `polarAntiNodeShift k`**:
at every polar anti-node $y_{k+1/2} = \frac{\pi(2k+1)}{\sqrt{7/4}}$ ($k \in \mathbb{Z}$), the pole
contribution in `2 * (cosineShiftFn lam sechHalf 0 + cosineShiftFn lam sechHalf (polarAntiNodeShift k))`
vanishes identically. -/
theorem two_mul_cosineShiftFn_sechHalf_zero_add_polarAntiNodeShift_eq {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) (k : ℤ) :
    2 * (cosineShiftFn lam sechHalf 0 + cosineShiftFn lam sechHalf (polarAntiNodeShift k)) =
      1 / (2 * Real.pi) *
          (∫ r : ℝ,
            trigPacketWeight (twoPointShift (polarAntiNodeShift k)) twoPointSumCoeff
              (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * fourModeShiftedArchDensity r) -
        (1 / (2 * Real.pi) *
          (∫ r : ℝ,
            trigPacketWeight (twoPointShift (polarAntiNodeShift k)) twoPointSumCoeff
              (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * fourModeGaussSpectralWeight r) +
        ∑' n : ℕ, (if 2 ≤ n then lam n / Real.sqrt n else 0) *
          (1 / Real.pi * ∫ r : ℝ,
            trigPacketWeight (twoPointShift (polarAntiNodeShift k)) twoPointSumCoeff
              (Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * Real.cos (r * Real.log n))) := by
  rw [← sum_sum_twoPointSum_cosineShiftFn,
    sum_sum_cosineShiftFn_sechHalf_eq_fourModeShifted_of_pole_zero hg _ _
      (trigPacketWeight_twoPointSum_polarAntiNodeShift_eq_zero k)]

end RHTower.CHMDStage13

end
