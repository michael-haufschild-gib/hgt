import GaloisForLFunctions.RHTower.CHMDStage14UnconditionalZeroSideToeplitzFormula

/-!
# CHMD Stage 15: Unconditional Zero-Side Summability, Pointwise `cosineShiftFn` Zero-Side Series, and Strip Positivity of `specSq sechHalf`

This module establishes the fifteenth stage of the **Causal Hyperbolic–Modular Duality (CHMD)**
formalization in `RHTower`, proving three major unconditional structural theorems on the zero side:

1. **Unconditional Zero-Side Summability for Every `GoodDensity K`**:
   - For every `GoodDensity K`, the exponential strip decay $\|K(z)\| \le C e^{-\varepsilon |\operatorname{Re} z|}$
     on $|\operatorname{Im} z| \le 5/4$ implies $\|K(\gamma_\rho)\| \le \frac{M}{1 + |\gamma_\rho|^2}$
     at every nontrivial zero $\rho \in \operatorname{zetaZeroConfig.carrier}$. Combining this with
     `WeilEF.zero_sum_inv_sq zetaSeam` yields unconditional summability of both
     $$\sum_{\rho \in \operatorname{zetaZeroConfig.carrier}} (m_\rho : \mathbb{C})\,K(\gamma_\rho)
       \quad\text{and}\quad
       \sum_{\rho \in \operatorname{zetaZeroConfig.carrier}} m_\rho\,\operatorname{Re} K(\gamma_\rho)$$
     (`summable_zeroSide_of_goodDensity`, `summable_re_zeroSide_of_goodDensity`,
     `re_tsum_zeroSide_of_goodDensity`).
   - Consequently, for every `EvenStrip Φ` and every finite wave packet `(t, c)`, the two zero-side
     series for `cosComb t c Φ` and `sinComb t c Φ` combine into a single unconditionally convergent
     real series (`evenWeilDensity_specSq_vonMangoldt_eq_tsum_re`,
     `sum_sum_cosineShiftFn_vonMangoldt_eq_tsum_re`,
     `sum_sum_cosineShiftFn_sechHalf_vonMangoldt_eq_tsum_re`), and by 2-point polarization, for every
     $y \in \mathbb{R}$,
     $$\operatorname{cosineShiftFn}\ \Lambda\ \Phi\ y
       = \sum'_{\rho : \operatorname{zetaZeroConfig.carrier}}
           m_\rho\,\operatorname{Re}\bigl(\operatorname{rhoCosShift}\ y\ \Phi\ (\gamma_\rho)\bigr)$$
     unconditionally (`cosineShiftFn_vonMangoldt_eq_tsum_re`).

2. **Unconditional Strip Positivity of `Re(specSq sechHalf z) > 0` on $|\operatorname{Im} z| \le 5/4$**:
   - Proves the exact algebraic identity `specSq sechHalf z = (Complex.cosh (z / 2) ^ 2)⁻¹` for all
     $z \in \mathbb{C}$, and the exact real-part formula
     $$\operatorname{Re}\bigl(\cosh^2(z / 2)\bigr)
       = \cos^2\left(\frac{\operatorname{Im} z}{2}\right)
         + \sinh^2\left(\frac{\operatorname{Re} z}{2}\right)\cos(\operatorname{Im} z)$$
     (`specSq_sechHalf_eq_inv_cosh_sq`, `re_cosh_half_sq`).
   - Because $|\operatorname{Im} z| \le 5/4 < \pi/2$ implies $\cos(\operatorname{Im} z / 2) > 0$ and
     $\cos(\operatorname{Im} z) > 0$, we obtain
     $$\operatorname{Re}\bigl(\cosh^2(z / 2)\bigr) \ge \cos^2\left(\frac{\operatorname{Im} z}{2}\right) > 0
       \quad\text{and}\quad
       0 < \operatorname{Re}\bigl(\operatorname{specSq}\ \operatorname{sechHalf}\ z\bigr)$$
     throughout the closed strip $|\operatorname{Im} z| \le 5/4$ (`re_cosh_half_sq_pos`,
     `re_specSq_sechHalf_pos_of_abs_im_le`).

3. **Unconditional Positivity of Every Zero Summand at $y = 0$, `cosineShiftFn Λ sechHalf 0 ≥ 0`,
   and All $1 \times 1$ Toeplitz Forms**:
   - Because every nontrivial zero $\rho$ of $\zeta(s)$ satisfies $|\operatorname{Im}(\gamma_\rho)| < 1/2 \le 5/4$
     unconditionally (whether on or off the critical line), every zero summand at $y = 0$ satisfies
     `0 < (specSq sechHalf (gammaOf ρ)).re` (`re_specSq_sechHalf_gammaOf_pos`).
   - Summing over `zetaZeroConfig.carrier` yields **unconditionally**:
     $$0 \le \operatorname{evenWeilDensity}\ \Lambda\ (\operatorname{specSq}\ \operatorname{sechHalf})
       = \operatorname{cosineShiftFn}\ \Lambda\ \operatorname{sechHalf}\ 0,$$
     $$\sum_{n=2}^\infty \frac{\Lambda(n)}{\sqrt{n}}\frac{4\log n}{\sinh(\pi\log n)}
       \le \frac{2}{\cos^2(1/4)} + \frac{1}{2\pi}\int_{\mathbb{R}} \operatorname{sechSqHalf}(r)\operatorname{EF.gammaBracket}(r)\,dr,$$
     and $0 \le \sum_{i, j : \operatorname{Fin} 1} c_i c_j \operatorname{cosineShiftFn}\ \Lambda\ \operatorname{sechHalf}\ (t_j - t_i)$
     (`evenWeilDensity_specSq_sechHalf_vonMangoldt_nonneg`,
     `cosineShiftFn_sechHalf_vonMangoldt_zero_nonneg`,
     `prime_sechHalf_zero_le_pole_add_arch_vonMangoldt`,
     `sum_sum_fin_one_cosineShiftFn_sechHalf_vonMangoldt_nonneg`).
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped BigOperators ComplexConjugate

noncomputable section

namespace RHTower.CHMDStage15

open WeilOneSided WeilSpectral GaloisForLFunctions.HTGeometry RHTower.EvenSector
open RHTower.CHMDStage1 RHTower.CHMDStage3 RHTower.CHMDStage4
open RHTower.CHMDStage11 RHTower.CHMDStage12 RHTower.CHMDStage13 RHTower.CHMDStage14

/-! ## Section 1: Unconditional Zero-Side Summability for Every `GoodDensity K` -/

/-- Elementary exponential-to-quadratic bound: for any $\varepsilon > 0$ and $y \in \mathbb{R}$,
$e^{-\varepsilon |y|} \le \frac{1 + 2 / \varepsilon^2}{1 + y^2}$. -/
theorem exp_neg_mul_abs_le_inv_one_add_sq {ε : ℝ} (hε : 0 < ε) (y : ℝ) :
    Real.exp (-(ε * |y|)) ≤ (1 + 2 / ε ^ 2) / (1 + y ^ 2) := by
  have h1 : 0 ≤ ε * |y| := by positivity
  have hquad := Real.quadratic_le_exp_of_nonneg h1
  have hsq : (ε * |y|) ^ 2 = ε ^ 2 * y ^ 2 := by rw [mul_pow, sq_abs]
  have hexp_pos : 0 < Real.exp (ε * |y|) := Real.exp_pos _
  have hden_pos : 0 < 1 + y ^ 2 := by positivity
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ hexp_pos, div_mul_eq_mul_div, le_div_iff₀ hden_pos]
  have h2 : 1 + ε ^ 2 / 2 * y ^ 2 ≤ Real.exp (ε * |y|) := by linarith
  have h3 : 1 + y ^ 2 ≤ (1 + 2 / ε ^ 2) * (1 + ε ^ 2 / 2 * y ^ 2) := by
    have hε2 : ε ^ 2 ≠ 0 := by positivity
    calc 1 + y ^ 2
        = 1 + (2 / ε ^ 2) * (ε ^ 2 / 2 * y ^ 2) := by field_simp
      _ ≤ 1 + (2 / ε ^ 2) * (ε ^ 2 / 2 * y ^ 2) + (2 / ε ^ 2 + ε ^ 2 / 2 * y ^ 2) :=
          le_add_of_nonneg_right (by positivity)
      _ = (1 + 2 / ε ^ 2) * (1 + ε ^ 2 / 2 * y ^ 2) := by ring
  calc 1 * (1 + y ^ 2) = 1 + y ^ 2 := one_mul _
    _ ≤ (1 + 2 / ε ^ 2) * (1 + ε ^ 2 / 2 * y ^ 2) := h3
    _ ≤ (1 + 2 / ε ^ 2) * Real.exp (ε * |y|) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

/-- At every nontrivial zero `ρ : zetaZeroConfig.carrier`,
`1 + Complex.normSq (gammaOf ρ) ≤ (5 / 4) * (1 + (ρ : ℂ).im ^ 2)`. -/
theorem one_add_normSq_gammaOf_le (ρ : zetaZeroConfig.carrier) :
    1 + Complex.normSq (Zeta23.gammaOf (ρ : ℂ)) ≤ (5 / 4 : ℝ) * (1 + (ρ : ℂ).im ^ 2) := by
  have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hIm : |(Zeta23.gammaOf (ρ : ℂ)).im| < 1 / 2 :=
    WeilEF.abs_gammaOf_im_lt ⟨hmem.2.1, hmem.2.2⟩
  have hre : (Zeta23.gammaOf (ρ : ℂ)).re = (ρ : ℂ).im := WeilEF.gammaOf_re _
  rw [Complex.normSq_apply, hre]
  have him2 : (Zeta23.gammaOf (ρ : ℂ)).im ^ 2 ≤ 1 / 4 := by
    have := sq_abs (Zeta23.gammaOf (ρ : ℂ)).im
    nlinarith [abs_nonneg (Zeta23.gammaOf (ρ : ℂ)).im]
  nlinarith [sq_nonneg (ρ : ℂ).im]

/-- **Unconditional Zero-Side Summability for Any `GoodDensity K`**:
for every `GoodDensity K`, the complex zero-side series
`fun ρ : zetaZeroConfig.carrier => (zetaZeroConfig.mult ρ : ℂ) * K (gammaOf ρ)` is summable. -/
theorem summable_zeroSide_of_goodDensity {K : ℂ → ℂ} (hK : GoodDensity K) :
    Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℂ) * K (Zeta23.gammaOf ρ) := by
  obtain ⟨ε, C, hε, hs⟩ := hK.strip
  have hC : 0 ≤ C := hs.const_nonneg (by norm_num)
  have hsum : Summable (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf ρ))) := by
    have := WeilEF.zero_sum_inv_sq zetaSeam
    simpa [zetaZeroConfig] using this
  set M := (5 / 4 : ℝ) * C * (1 + 2 / ε ^ 2)
  refine Summable.of_norm_bounded (hsum.mul_left M) fun ρ => ?_
  have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hIm : |(Zeta23.gammaOf (ρ : ℂ)).im| < 1 / 2 :=
    WeilEF.abs_gammaOf_im_lt ⟨hmem.2.1, hmem.2.2⟩
  have hre : (Zeta23.gammaOf (ρ : ℂ)).re = (ρ : ℂ).im := WeilEF.gammaOf_re _
  have hb := hs.bound (Zeta23.gammaOf ρ) (by linarith)
  rw [hre] at hb
  have hexp := exp_neg_mul_abs_le_inv_one_add_sq hε (ρ : ℂ).im
  have hnormSq := one_add_normSq_gammaOf_le ρ
  have hpos1 : 0 < 1 + Complex.normSq (Zeta23.gammaOf (ρ : ℂ)) := by
    have := Complex.normSq_nonneg (Zeta23.gammaOf (ρ : ℂ)); linarith
  have hpos2 : 0 < 1 + (ρ : ℂ).im ^ 2 := by positivity
  have hdiv : 1 / (1 + (ρ : ℂ).im ^ 2) ≤
      (5 / 4 : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf (ρ : ℂ))) := by
    rw [div_le_div_iff₀ hpos2 hpos1]
    linarith
  rw [norm_mul, Complex.norm_natCast]
  calc (zetaZeroConfig.mult ρ : ℝ) * ‖K (Zeta23.gammaOf ρ)‖
      ≤ (zetaZeroConfig.mult ρ : ℝ) * (C * Real.exp (-(ε * |(ρ : ℂ).im|))) :=
        mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
    _ ≤ (zetaZeroConfig.mult ρ : ℝ) * (C * ((1 + 2 / ε ^ 2) * (1 / (1 + (ρ : ℂ).im ^ 2)))) := by
        gcongr
        simpa [div_eq_mul_inv] using hexp
    _ ≤ (zetaZeroConfig.mult ρ : ℝ) *
          (C * ((1 + 2 / ε ^ 2) * ((5 / 4 : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf (ρ : ℂ)))))) := by
        gcongr
    _ = M * ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf (ρ : ℂ)))) := by
        unfold M; ring

/-- **Unconditional Real Zero-Side Summability for Any `GoodDensity K`**:
for every `GoodDensity K`, the real zero-side series
`fun ρ : zetaZeroConfig.carrier => (zetaZeroConfig.mult ρ : ℝ) * (K (gammaOf ρ)).re` is summable. -/
theorem summable_re_zeroSide_of_goodDensity {K : ℂ → ℂ} (hK : GoodDensity K) :
    Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * (K (Zeta23.gammaOf ρ)).re := by
  have h := Complex.reCLM.summable (summable_zeroSide_of_goodDensity hK)
  refine h.congr fun ρ => ?_
  simp [Complex.mul_re]

/-- Commuting `.re` inside the zero-side `tsum` for any `GoodDensity K`. -/
theorem re_tsum_zeroSide_of_goodDensity {K : ℂ → ℂ} (hK : GoodDensity K) :
    (∑' ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℂ) * K (Zeta23.gammaOf ρ)).re =
      ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) * (K (Zeta23.gammaOf ρ)).re := by
  rw [Complex.re_tsum (summable_zeroSide_of_goodDensity hK)]
  refine tsum_congr fun ρ => ?_
  simp [Complex.mul_re]

/-- **Unconditional Real Zero-Side Series for `evenWeilDensity Λ (specSq Φ)`**:
for every `EvenStrip Φ`,
`evenWeilDensity Λ (specSq Φ) = ∑' ρ, (zetaZeroConfig.mult ρ : ℝ) * (specSq Φ (gammaOf ρ)).re`. -/
theorem evenWeilDensity_specSq_vonMangoldt_eq_tsum_re {Φ : ℂ → ℂ} (hΦ : EvenStrip Φ) :
    evenWeilDensity (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (specSq Φ) =
      ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) * (specSq Φ (Zeta23.gammaOf ρ)).re := by
  rw [evenWeilDensity_specSq_vonMangoldt_eq_re_tsum_specSq hΦ,
    re_tsum_zeroSide_of_goodDensity (goodDensity_specSq hΦ)]

/-- **Unconditional Combined Real Zero-Side Series for the Toeplitz Form**:
for every `EvenStrip Φ` and every finite wave packet `(t, c)`, the Toeplitz quadratic form equals a
single unconditionally convergent series over `zetaZeroConfig.carrier`. -/
theorem sum_sum_cosineShiftFn_vonMangoldt_eq_tsum_re {Φ : ℂ → ℂ} (hΦ : EvenStrip Φ)
    {N : ℕ} (t c : Fin N → ℝ) :
    (∑ i, ∑ j, c i * c j *
        cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) Φ (t j - t i)) =
      ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) *
          (specSq (cosComb t c Φ) (Zeta23.gammaOf ρ) +
            specSq (sinComb t c Φ) (Zeta23.gammaOf ρ)).re := by
  have hA := goodDensity_specSq (evenStrip_cosComb t c hΦ)
  have hB := goodDensity_specSq (evenStrip_sinComb t c hΦ)
  rw [sum_sum_cosineShiftFn_vonMangoldt_eq_re_tsum_add_re_tsum hΦ t c,
    re_tsum_zeroSide_of_goodDensity hA, re_tsum_zeroSide_of_goodDensity hB,
    ← (summable_re_zeroSide_of_goodDensity hA).tsum_add (summable_re_zeroSide_of_goodDensity hB)]
  refine tsum_congr fun ρ => ?_
  rw [Complex.add_re, mul_add]

/-- **Unconditional Single-Series Zero-Side Formula for the Decisive `sechHalf` Toeplitz Form**. -/
theorem sum_sum_cosineShiftFn_sechHalf_vonMangoldt_eq_tsum_re {N : ℕ} (t c : Fin N → ℝ) :
    (∑ i, ∑ j, c i * c j *
        cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf (t j - t i)) =
      ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) *
          (specSq (cosComb t c sechHalf) (Zeta23.gammaOf ρ) +
            specSq (sinComb t c sechHalf) (Zeta23.gammaOf ρ)).re :=
  sum_sum_cosineShiftFn_vonMangoldt_eq_tsum_re evenStrip_sechHalf t c

/-- **Unconditional Pointwise Zero-Side Series for `cosineShiftFn Λ Φ y` at Every $y \in \mathbb{R}$**:
by 2-point polarization, for every `EvenStrip Φ` and every $y \in \mathbb{R}$,
`cosineShiftFn Λ Φ y = ∑' ρ, (zetaZeroConfig.mult ρ : ℝ) * (rhoCosShift y Φ (gammaOf ρ)).re`. -/
theorem cosineShiftFn_vonMangoldt_eq_tsum_re {Φ : ℂ → ℂ} (hΦ : EvenStrip Φ) (y : ℝ) :
    cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) Φ y =
      ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) * (rhoCosShift y Φ (Zeta23.gammaOf ρ)).re := by
  have hS := goodDensity_specSq_cosComb_add_sinComb hΦ (twoPointShift y) twoPointSumCoeff
  have hD := goodDensity_specSq_cosComb_add_sinComb hΦ (twoPointShift y) twoPointDiffCoeff
  rw [cosineShiftFn_eq_quarter_twoPointSum_sub_twoPointDiff,
    sum_sum_cosineShiftFn_vonMangoldt_eq_tsum_re hΦ (twoPointShift y) twoPointSumCoeff,
    sum_sum_cosineShiftFn_vonMangoldt_eq_tsum_re hΦ (twoPointShift y) twoPointDiffCoeff,
    ← (summable_re_zeroSide_of_goodDensity hS).tsum_sub (summable_re_zeroSide_of_goodDensity hD),
    ← tsum_mul_left]
  refine tsum_congr fun ρ => ?_
  have hsum := specSq_cosComb_add_specSq_sinComb_gammaOf (twoPointShift y) twoPointSumCoeff Φ ρ
  have hdiff := specSq_cosComb_add_specSq_sinComb_gammaOf (twoPointShift y) twoPointDiffCoeff Φ ρ
  have hneg := congr_fun (cosShift_neg y Φ) (Zeta23.gammaOf ρ)
  change (1 / 4 : ℝ) *
      ((zetaZeroConfig.mult ρ : ℝ) *
          (specSq (cosComb (twoPointShift y) twoPointSumCoeff Φ) (Zeta23.gammaOf ρ) +
            specSq (sinComb (twoPointShift y) twoPointSumCoeff Φ) (Zeta23.gammaOf ρ)).re -
        (zetaZeroConfig.mult ρ : ℝ) *
          (specSq (cosComb (twoPointShift y) twoPointDiffCoeff Φ) (Zeta23.gammaOf ρ) +
            specSq (sinComb (twoPointShift y) twoPointDiffCoeff Φ) (Zeta23.gammaOf ρ)).re) =
    (zetaZeroConfig.mult ρ : ℝ) * (rhoCosShift y Φ (Zeta23.gammaOf ρ)).re
  rw [hsum, hdiff]
  unfold twoPointShift twoPointSumCoeff twoPointDiffCoeff
  simp only [Finset.sum_product, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    sub_self, sub_zero, zero_sub, hneg, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-! ## Section 2: Unconditional Strip Positivity of `(specSq sechHalf z).re > 0` on `|z.im| ≤ 5 / 4` -/

/-- For every $z \in \mathbb{C}$, `specSq sechHalf z = (Complex.cosh (z / 2) ^ 2)⁻¹`. -/
theorem specSq_sechHalf_eq_inv_cosh_sq (z : ℂ) :
    specSq sechHalf z = (Complex.cosh (z / 2) ^ 2)⁻¹ := by
  unfold specSq sechHalf
  rw [show conj z / 2 = conj (z / 2) by rw [map_div₀, map_ofNat],
    Complex.cosh_conj, ← map_inv₀, Complex.conj_conj, ← sq, inv_pow]

/-- **Exact Real-Part Formula for `Complex.cosh (z / 2) ^ 2`**:
for every $z \in \mathbb{C}$,
`(Complex.cosh (z / 2) ^ 2).re = Real.cos (z.im / 2) ^ 2 + Real.sinh (z.re / 2) ^ 2 * Real.cos z.im`. -/
theorem re_cosh_half_sq (z : ℂ) :
    (Complex.cosh (z / 2) ^ 2).re =
      Real.cos (z.im / 2) ^ 2 + Real.sinh (z.re / 2) ^ 2 * Real.cos z.im := by
  have hz : z / 2 = ((z.re / 2 : ℝ) : ℂ) + ((z.im / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [hz, cosh_ofReal_add_mul_I, sq]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_add, add_zero, mul_one, sub_zero]
  have hch := Real.cosh_sq (z.re / 2)
  have hcos := Real.cos_two_mul' (z.im / 2)
  have h2 : 2 * (z.im / 2) = z.im := by ring
  rw [h2] at hcos
  have hpyth := Real.cos_sq_add_sin_sq (z.im / 2)
  nlinarith

/-- On `|y| ≤ 5 / 4`, `0 < Real.cos y`. -/
theorem cos_pos_of_abs_le_five_fourths {y : ℝ} (hy : |y| ≤ 5 / 4) :
    0 < Real.cos y := by
  apply Real.cos_pos_of_mem_Ioo
  have h1 := abs_le.mp hy
  have hpi : (5 / 4 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
  constructor <;> linarith [h1.1, h1.2]

/-- **Strip Lower Bound for `(Complex.cosh (z / 2) ^ 2).re`**:
for every $z \in \mathbb{C}$ with $|\operatorname{Im} z| \le 5/4$,
`Real.cos (z.im / 2) ^ 2 ≤ (Complex.cosh (z / 2) ^ 2).re` and `0 < (Complex.cosh (z / 2) ^ 2).re`. -/
theorem cos_half_sq_le_re_cosh_half_sq {z : ℂ} (hz : |z.im| ≤ 5 / 4) :
    Real.cos (z.im / 2) ^ 2 ≤ (Complex.cosh (z / 2) ^ 2).re := by
  rw [re_cosh_half_sq]
  have hcos : 0 ≤ Real.cos z.im := (cos_pos_of_abs_le_five_fourths hz).le
  have hsh : 0 ≤ Real.sinh (z.re / 2) ^ 2 := sq_nonneg _
  linarith [mul_nonneg hsh hcos]

theorem re_cosh_half_sq_pos {z : ℂ} (hz : |z.im| ≤ 5 / 4) :
    0 < (Complex.cosh (z / 2) ^ 2).re := by
  have hc : 0 < Real.cos (z.im / 2) := cos_half_pos (by linarith)
  exact (sq_pos_of_pos hc).trans_le (cos_half_sq_le_re_cosh_half_sq hz)

/-- **Unconditional Strip Positivity of `(specSq sechHalf z).re` on `|z.im| ≤ 5 / 4`**:
for every $z \in \mathbb{C}$ in the strip $|\operatorname{Im} z| \le 5/4$,
`0 < (specSq sechHalf z).re`. -/
theorem re_specSq_sechHalf_pos_of_abs_im_le {z : ℂ} (hz : |z.im| ≤ 5 / 4) :
    0 < (specSq sechHalf z).re := by
  rw [specSq_sechHalf_eq_inv_cosh_sq, Complex.inv_re]
  have hre : 0 < (Complex.cosh (z / 2) ^ 2).re := re_cosh_half_sq_pos hz
  have hne : Complex.cosh (z / 2) ^ 2 ≠ 0 := pow_ne_zero 2 (cosh_half_ne_zero (by linarith))
  have hns : 0 < Complex.normSq (Complex.cosh (z / 2) ^ 2) := Complex.normSq_pos.mpr hne
  exact div_pos hre hns

/-! ## Section 3: Unconditional Positivity of Every Zero Summand at $y = 0$, `cosineShiftFn Λ sechHalf 0 ≥ 0`, and All $1 \times 1$ Toeplitz Forms -/

/-- **Unconditional Strict Positivity of `(specSq sechHalf (gammaOf ρ)).re` at Every Nontrivial Zero**:
for every nontrivial zero `ρ : zetaZeroConfig.carrier` (with zero assumption on whether `ρ` lies on
or off the critical line), `0 < (specSq sechHalf (gammaOf ρ)).re`. -/
theorem re_specSq_sechHalf_gammaOf_pos (ρ : zetaZeroConfig.carrier) :
    0 < (specSq sechHalf (Zeta23.gammaOf ρ)).re := by
  have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hIm : |(Zeta23.gammaOf (ρ : ℂ)).im| < 1 / 2 :=
    WeilEF.abs_gammaOf_im_lt ⟨hmem.2.1, hmem.2.2⟩
  exact re_specSq_sechHalf_pos_of_abs_im_le (by linarith)

/-- Unconditional nonnegativity of the weighted zero summand at $y = 0$ for every nontrivial zero
`ρ : zetaZeroConfig.carrier`. -/
theorem zeroSide_summand_sechHalf_nonneg (ρ : zetaZeroConfig.carrier) :
    0 ≤ (zetaZeroConfig.mult ρ : ℝ) * (specSq sechHalf (Zeta23.gammaOf ρ)).re :=
  mul_nonneg (Nat.cast_nonneg _) (re_specSq_sechHalf_gammaOf_pos ρ).le

/-- **Unconditional Nonnegativity of `evenWeilDensity Λ (specSq sechHalf)`**:
proved directly from the explicit formula and strip positivity of `specSq sechHalf` on
`|\operatorname{Im} z| \le 5/4`. -/
theorem evenWeilDensity_specSq_sechHalf_vonMangoldt_nonneg :
    0 ≤ evenWeilDensity (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (specSq sechHalf) := by
  rw [evenWeilDensity_specSq_vonMangoldt_eq_tsum_re evenStrip_sechHalf]
  exact tsum_nonneg zeroSide_summand_sechHalf_nonneg

/-- **Unconditional Nonnegativity of `cosineShiftFn Λ sechHalf 0` at the Origin $y = 0$**. -/
theorem cosineShiftFn_sechHalf_vonMangoldt_zero_nonneg :
    0 ≤ cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf 0 := by
  have h0 : rhoCosShift 0 sechHalf = specSq sechHalf := by
    funext z; unfold rhoCosShift; simp
  unfold cosineShiftFn
  rw [h0]
  exact evenWeilDensity_specSq_sechHalf_vonMangoldt_nonneg

/-- **Unconditional Prime-vs-(Pole + Archimedean) Inequality at $y = 0$**:
for the actual von Mangoldt source $\Lambda$,
$$\sum_{n=2}^\infty \frac{\Lambda(n)}{\sqrt{n}}\frac{4\log n}{\sinh(\pi\log n)}
  \le \frac{2}{\cos^2(1/4)} + \frac{1}{2\pi}\int_{\mathbb{R}} \operatorname{sechSqHalf}(r)\operatorname{EF.gammaBracket}(r)\,dr.$$ -/
theorem prime_sechHalf_zero_le_pole_add_arch_vonMangoldt :
    (∑' n : ℕ,
      (if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0) *
        (4 * Real.log n / Real.sinh (Real.pi * Real.log n))) ≤
      2 / Real.cos (1 / 4 : ℝ) ^ 2 +
        1 / (2 * Real.pi) * (∫ r : ℝ, sechSqHalf r * EF.gammaBracket r) := by
  have h := cosineShiftFn_sechHalf_vonMangoldt_zero_nonneg
  rw [cosineShiftFn_sechHalf_zero_eq, sub_nonneg] at h
  exact h

/-- **Unconditional Nonnegativity of Every $1 \times 1$ (`N = 1`) Toeplitz Form for `sechHalf` and `Λ`**:
for every $1$-point wave packet `t, c : Fin 1 → ℝ`,
`0 ≤ ∑ i : Fin 1, ∑ j : Fin 1, c i * c j * cosineShiftFn Λ sechHalf (t j - t i)`. -/
theorem sum_sum_fin_one_cosineShiftFn_sechHalf_vonMangoldt_nonneg
    (t c : Fin 1 → ℝ) :
    0 ≤ ∑ i : Fin 1, ∑ j : Fin 1,
      c i * c j *
        cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf (t j - t i) := by
  simp only [Fintype.sum_unique, sub_self]
  exact mul_nonneg (mul_self_nonneg (c 0)) cosineShiftFn_sechHalf_vonMangoldt_zero_nonneg

end RHTower.CHMDStage15

end
