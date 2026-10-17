import GaloisForLFunctions.BiScaleUncertainty.MultiCosetGramPackingAndNyquistDensity

/-!
# Pillar XII: Producer–Consumer Duality & the Nyman–Beurling / FZZ-P Bridge

This module develops **Pillar XII** of **Bi-Scale / Logarithmic-Grid Uncertainty Theory**,
addressing the second core requirement for overcoming **Wall 1** (`docs/reports/wall1.md`):
establishing the formal **Producer–Consumer Duality** between:
- **Consumer Routes (`BiScaleUncertainty` / Weil / Prime-Blind Correlations):** bounding the
  archimedean Lévy/chord energy or polar pairing of states $f$ orthogonal to the logarithmic grid
  generators ($\langle f, g_n\rangle = 0$ or $h_f(\log n) = 0$), and
- **Producer Routes (FZZ-P / Nyman–Beurling / Báez-Duarte):** approximating a polar target state
  $p$ (such as the $s = 1$ pole weight $\cosh(x/2)$ or $e^{-u/2}$) in $L^2$ by finite linear
  combinations $\sum_{n \in s} c_n g_n$ of arithmetic dilates/translates.

## Main Results

1. **`producer_consumer_inner_eq` & `consumer_polar_sq_le_producer_error`**:
   For any grid-blind consumer $f \in E$ ($\langle f, g_i\rangle = 0$ for $i \in s$) and any
   producer coefficient vector $c : \iota \to \mathbb{R}$,
   $$\langle f, p\rangle = \left\langle f,\, p - \sum_{i \in s} c_i g_i\right\rangle, \qquad \langle f, p\rangle^2 \;\le\; \|f\|^2 \, \left\|p - \sum_{i \in s} c_i g_i\right\|^2.$$
2. **`producer_consumer_defect_sq_le`**:
   Without assuming exact grid-blindness, for any $f, p \in E$ and producer $c$:
   $$\left(\langle f, p\rangle - \sum_{i \in s} c_i \langle f, g_i\rangle\right)^2 \;\le\; \|f\|^2 \, \left\|p - \sum_{i \in s} c_i g_i\right\|^2.$$
3. **`fzzp_nyman_beurling_orthogonal_duality_identity`**:
   Over an orthogonal clique $\{e_i\}_{i \in s}$ with $\langle e_i, e_i\rangle = R$, the producer
   approximation error decomposes into the consumer Bessel slack plus the squared distance to the
   optimal projection coefficients:
   $$R^2 \left\|p - \sum_{i \in s} c_i e_i\right\|^2 = R\left(R\|p\|^2 - \sum_{i \in s} \langle e_i, p\rangle^2\right) + R\sum_{i \in s} \bigl(R c_i - \langle e_i, p\rangle\bigr)^2.$$
4. **`intervalIntegral_cauchy_schwarz_sq_le`**:
   Division-free discriminant proof of the integral Cauchy–Schwarz inequality
   $$\left(\int_a^b F(x)\,G(x)\,dx\right)^2 \;\le\; \left(\int_a^b F(x)^2\,dx\right)\left(\int_a^b G(x)^2\,dx\right).$$
5. **`correlation_polar_producer_decomposition` & `correlation_producer_consumer_residual_sq_le`**:
   Couples any correlation polar functional $\int_a^b h_f(x) P(x)\,dx$ to any collar producer weight
   $W(x)$ via the residual $\int_a^b (P(x) - W(x))^2\,dx$.
6. **`dyadic_window_producer_consumer_duality_le_levy`**:
   Combines Producer–Consumer Duality on $[\log N, \log(2N)]$ with Pillar XI's Nyquist $L^2$
   compression to bound the polar-vs-collar discrepancy directly by
   $2 h_f(0)\,\operatorname{biScaleLevyEnergy}(f) \int_{\log N}^{\log(2N)} (\cosh(x/2) - W(x))^2\,dx$.
-/

namespace GaloisForLFunctions.BiScaleUncertainty

open MeasureTheory Set Filter
open scoped RealInnerProductSpace BigOperators

noncomputable section

/-! ## §1. Abstract Producer–Consumer Duality in Hilbert Space -/

section AbstractDuality

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [DecidableEq ι]

/-- **Producer–Consumer Defect Identity:**
For any target `p ∈ E`, generators `g : ι → E`, producer coefficients `c : ι → ℝ`, and consumer
`f ∈ E`,
`⟪f, p - ∑ i ∈ s, c i • g i⟫ = ⟪f, p⟫ - ∑ i ∈ s, c i * ⟪f, g i⟫`. -/
theorem producer_consumer_defect_eq (s : Finset ι) (g : ι → E) (c : ι → ℝ) (p f : E) :
    ⟪f, p - ∑ i ∈ s, c i • g i⟫ = ⟪f, p⟫ - ∑ i ∈ s, c i * ⟪f, g i⟫ := by
  rw [inner_sub_right, inner_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_right]

/-- **Grid-Blind Producer–Consumer Orthogonality Identity:**
If `f ∈ E` is orthogonal to the generator family `{g_i}_{i ∈ s}` (`⟪f, g_i⟫ = 0` for all `i ∈ s`),
then for every producer `c : ι → ℝ`,
`⟪f, p⟫ = ⟪f, p - ∑ i ∈ s, c i • g i⟫`. -/
theorem producer_consumer_inner_eq (s : Finset ι) (g : ι → E) (c : ι → ℝ) (p f : E)
    (hblind : ∀ i ∈ s, ⟪f, g i⟫ = 0) :
    ⟪f, p⟫ = ⟪f, p - ∑ i ∈ s, c i • g i⟫ := by
  rw [producer_consumer_defect_eq]
  have h0 : ∑ i ∈ s, c i * ⟪f, g i⟫ = 0 :=
    Finset.sum_eq_zero fun i hi => by rw [hblind i hi, mul_zero]
  linarith

/-- **General Producer–Consumer Duality Inequality:**
For any `f, p ∈ E` and producer `c : ι → ℝ`,
`(⟪f, p⟫ - ∑ i ∈ s, c i * ⟪f, g i⟫)² ≤ ‖f‖² * ‖p - ∑ i ∈ s, c i • g i‖²`. -/
theorem producer_consumer_defect_sq_le (s : Finset ι) (g : ι → E) (c : ι → ℝ) (p f : E) :
    (⟪f, p⟫ - ∑ i ∈ s, c i * ⟪f, g i⟫) ^ 2 ≤
      ‖f‖ ^ 2 * ‖p - ∑ i ∈ s, c i • g i‖ ^ 2 := by
  rw [← producer_consumer_defect_eq]
  set r := p - ∑ i ∈ s, c i • g i
  have hcs := abs_real_inner_le_norm f r
  have hsq : ⟪f, r⟫ ^ 2 ≤ (‖f‖ * ‖r‖) ^ 2 := by
    rw [← sq_abs ⟪f, r⟫]
    exact sq_le_sq.mpr (by
      rw [abs_abs, abs_of_nonneg (mul_nonneg (norm_nonneg f) (norm_nonneg r))]
      exact hcs)
  simpa only [mul_pow] using hsq

/-- **Grid-Blind Producer–Consumer Duality Bound:**
If `⟪f, g_i⟫ = 0` for all `i ∈ s`, then for every producer `c : ι → ℝ`,
`⟪f, p⟫² ≤ ‖f‖² * ‖p - ∑ i ∈ s, c i • g i‖²`.
Equivalently:
- Any producer approximation bound `‖p - ∑ c_i g_i‖ ≤ ε` forces `|⟪f, p⟫| ≤ ε ‖f‖` on all
  grid-blind consumers `f`.
- Any grid-blind consumer `f` provides the unconditional lower bound
  `⟪f, p⟫² ≤ ‖f‖² * ‖p - ∑ c_i g_i‖²` on all producers `c`. -/
theorem consumer_polar_sq_le_producer_error (s : Finset ι) (g : ι → E) (c : ι → ℝ) (p f : E)
    (hblind : ∀ i ∈ s, ⟪f, g i⟫ = 0) :
    ⟪f, p⟫ ^ 2 ≤ ‖f‖ ^ 2 * ‖p - ∑ i ∈ s, c i • g i‖ ^ 2 := by
  have h := producer_consumer_defect_sq_le s g c p f
  have h0 : ∑ i ∈ s, c i * ⟪f, g i⟫ = 0 :=
    Finset.sum_eq_zero fun i hi => by rw [hblind i hi, mul_zero]
  rw [h0, sub_zero] at h
  exact h

/-- **Exact FZZ-P / Nyman–Beurling Orthogonal Duality Identity:**
For any orthogonal frame `{e_i}_{i ∈ s}` with `⟪e_i, e_i⟫ = R`, target `p ∈ E`, and producer
coefficients `c : ι → ℝ`,
`R² ‖p - ∑ i ∈ s, c i • e i‖² = R (R ‖p‖² - ∑ i ∈ s, ⟪e_i, p⟫²) + R ∑ i ∈ s, (R c_i - ⟪e_i, p⟫)²`.
Thus the minimum-norm producer error over an orthogonal clique is identically equal to the consumer
Bessel slack `R ‖p‖² - ∑ i ∈ s, ⟪e_i, p⟫²`. -/
theorem fzzp_nyman_beurling_orthogonal_duality_identity (s : Finset ι) (e : ι → E) (R : ℝ)
    (hdiag : ∀ i ∈ s, ⟪e i, e i⟫ = R)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪e i, e j⟫ = 0)
    (c : ι → ℝ) (p : E) :
    R ^ 2 * ‖p - ∑ i ∈ s, c i • e i‖ ^ 2 =
      R * (R * ‖p‖ ^ 2 - ∑ i ∈ s, ⟪e i, p⟫ ^ 2) +
        R * ∑ i ∈ s, (R * c i - ⟪e i, p⟫) ^ 2 := by
  rw [norm_sq_sub_linearComb_eq]
  have hquad :
      (∑ i ∈ s, ∑ j ∈ s, c i * c j * ⟪e i, e j⟫) =
        R * ∑ i ∈ s, (c i) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_eq_single i]
    · rw [hdiag i hi]
      ring
    · intro j hj hji
      rw [horth i hi j hj hji.symm, mul_zero]
    · intro hi_not
      exact False.elim (hi_not hi)
  rw [hquad]
  have hsum_sq :
      (∑ i ∈ s, (R * c i - ⟪e i, p⟫) ^ 2) =
        R ^ 2 * (∑ i ∈ s, (c i) ^ 2) - 2 * R * (∑ i ∈ s, c i * ⟪e i, p⟫) +
          ∑ i ∈ s, ⟪e i, p⟫ ^ 2 := by
    have hpt :
        (∑ i ∈ s, (R * c i - ⟪e i, p⟫) ^ 2) =
          ∑ i ∈ s, (R ^ 2 * (c i) ^ 2 - 2 * R * (c i * ⟪e i, p⟫) + ⟪e i, p⟫ ^ 2) :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
  linarith

end AbstractDuality

/-! ## §2. Integral Cauchy–Schwarz & Correlation-Space Producer–Consumer Duality -/

/-- **Interval-Integral Cauchy–Schwarz Inequality:**
For any `a ≤ b` and continuous functions `F, G : ℝ → ℝ` on `Icc a b`,
`(∫ x in a..b, F x * G x)² ≤ (∫ x in a..b, (F x)²) * (∫ x in a..b, (G x)²)`. -/
theorem intervalIntegral_cauchy_schwarz_sq_le {F G : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Icc a b)) (hG : ContinuousOn G (Icc a b)) :
    (∫ x in a..b, F x * G x) ^ 2 ≤
      (∫ x in a..b, (F x) ^ 2) * (∫ x in a..b, (G x) ^ 2) := by
  set I_FF := ∫ x in a..b, (F x) ^ 2
  set I_GG := ∫ x in a..b, (G x) ^ 2
  set I_FG := ∫ x in a..b, F x * G x
  have hFF_int : IntervalIntegrable (fun x => (F x) ^ 2) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    exact hF.pow 2
  have hGG_int : IntervalIntegrable (fun x => (G x) ^ 2) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    exact hG.pow 2
  have hFG_int : IntervalIntegrable (fun x => F x * G x) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    exact hF.mul hG
  have hquad : ∀ t s : ℝ, 0 ≤ t ^ 2 * I_FF - 2 * t * s * I_FG + s ^ 2 * I_GG := by
    intro t s
    have hnonneg :
        0 ≤ ∫ x in a..b, (t * F x - s * G x) ^ 2 :=
      intervalIntegral.integral_nonneg hab fun x _ => sq_nonneg _
    have hexp :
        (fun x => (t * F x - s * G x) ^ 2) =
          fun x => t ^ 2 * (F x) ^ 2 - 2 * t * s * (F x * G x) + s ^ 2 * (G x) ^ 2 := by
      ext x; ring
    rw [hexp,
      intervalIntegral.integral_add
        ((hFF_int.const_mul (t ^ 2)).sub (hFG_int.const_mul (2 * t * s)))
        (hGG_int.const_mul (s ^ 2)),
      intervalIntegral.integral_sub
        (hFF_int.const_mul (t ^ 2)) (hFG_int.const_mul (2 * t * s)),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at hnonneg
    exact hnonneg
  have hGG_nonneg : 0 ≤ I_GG :=
    intervalIntegral.integral_nonneg hab fun x _ => sq_nonneg _
  rcases eq_or_lt_of_le hGG_nonneg with hGG0 | hGG_pos
  · have hFG0 : I_FG = 0 := by
      by_contra hne
      have h1 := hquad 1 ((I_FF + 1) / (2 * I_FG))
      rw [← hGG0] at h1
      have hmul : 2 * 1 * ((I_FF + 1) / (2 * I_FG)) * I_FG = I_FF + 1 := by
        field_simp [hne]
      linarith
    rw [hFG0, ← hGG0]
    simp
  · have h1 := hquad I_GG I_FG
    have h2 : I_FG ^ 2 * I_GG ≤ (I_FF * I_GG) * I_GG := by nlinarith
    exact le_of_mul_le_mul_right h2 hGG_pos

/-- **Correlation-Space Polar–Producer Decomposition:**
For any continuous compactly supported `f : ℝ → ℝ`, interval `[a, b]` (`a ≤ b`), polar weight
`P : ℝ → ℝ`, and collar producer weight `W : ℝ → ℝ` continuous on `Icc a b`,
`∫ x in a..b, autocorr f x * P x + ∫ x in a..b, (autocorr f 0 - autocorr f x) * W x = (∫ x in a..b, W x) * autocorr f 0 + ∫ x in a..b, autocorr f x * (P x - W x)`. -/
theorem correlation_polar_producer_decomposition {f : ℝ → ℝ}
    (hfc : HasCompactSupport f) (hf : Continuous f) {a b : ℝ} (hab : a ≤ b)
    {P W : ℝ → ℝ} (hP : ContinuousOn P (Icc a b)) (hW : ContinuousOn W (Icc a b)) :
    (∫ x in a..b, autocorr f x * P x) +
        (∫ x in a..b, (autocorr f 0 - autocorr f x) * W x) =
      (∫ x in a..b, W x) * autocorr f 0 +
        ∫ x in a..b, autocorr f x * (P x - W x) := by
  have hc : ContinuousOn (autocorr f) (Icc a b) :=
    (continuous_autocorr_of_continuous hfc hf).continuousOn
  have h1 : IntervalIntegrable (fun x => autocorr f x * P x) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]; exact hc.mul hP
  have h2 : IntervalIntegrable (fun x => (autocorr f 0 - autocorr f x) * W x) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]; exact (continuousOn_const.sub hc).mul hW
  have h3 : IntervalIntegrable (fun x => W x * autocorr f 0) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]; exact hW.mul continuousOn_const
  have h4 : IntervalIntegrable (fun x => autocorr f x * (P x - W x)) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]; exact hc.mul (hP.sub hW)
  rw [← intervalIntegral.integral_add h1 h2,
    ← intervalIntegral.integral_mul_const,
    ← intervalIntegral.integral_add h3 h4]
  refine intervalIntegral.integral_congr fun x _ => ?_
  dsimp
  ring

/-- **Correlation-Space Producer–Consumer Residual Bound:**
The squared discrepancy between the combined polar-and-collar functional and the producer charge
`(∫ x in a..b, W x) * autocorr f 0` is bounded by the product of the consumer `L²` correlation
energy and the producer `L²` approximation error:
`(∫ x in a..b, autocorr f x * P x + ∫ x in a..b, (autocorr f 0 - autocorr f x) * W x - (∫ x in a..b, W x) * autocorr f 0)² ≤ (∫ x in a..b, (autocorr f x)²) * (∫ x in a..b, (P x - W x)²)`. -/
theorem correlation_producer_consumer_residual_sq_le {f : ℝ → ℝ}
    (hfc : HasCompactSupport f) (hf : Continuous f) {a b : ℝ} (hab : a ≤ b)
    {P W : ℝ → ℝ} (hP : ContinuousOn P (Icc a b)) (hW : ContinuousOn W (Icc a b)) :
    ((∫ x in a..b, autocorr f x * P x) +
        (∫ x in a..b, (autocorr f 0 - autocorr f x) * W x) -
        (∫ x in a..b, W x) * autocorr f 0) ^ 2 ≤
      (∫ x in a..b, (autocorr f x) ^ 2) * (∫ x in a..b, (P x - W x) ^ 2) := by
  have hdecomp := correlation_polar_producer_decomposition hfc hf hab hP hW
  have hsub :
      (∫ x in a..b, autocorr f x * P x) +
          (∫ x in a..b, (autocorr f 0 - autocorr f x) * W x) -
          (∫ x in a..b, W x) * autocorr f 0 =
        ∫ x in a..b, autocorr f x * (P x - W x) := by
    linarith
  rw [hsub]
  exact intervalIntegral_cauchy_schwarz_sq_le hab
    (continuous_autocorr_of_continuous hfc hf).continuousOn (hP.sub hW)

/-- **Bi-Scale Dyadic-Window Producer–Consumer Duality Theorem:**
If `f ∈ C²_c(ℝ)` vanishes at the `N` dyadic-window grid nodes `log(N + k)` (`0 ≤ k < N`, `N ≥ 1`),
then for any collar producer weight `W` continuous on `[log N, log(2N)]`:
`(∫ x in log N..log(2N), autocorr f x * cosh(x / 2) + ∫ x in log N..log(2N), (autocorr f 0 - autocorr f x) * W x - (∫ x in log N..log(2N), W x) * autocorr f 0)² ≤ 2 * autocorr f 0 * biScaleLevyEnergy f * ∫ x in log N..log(2N), (cosh(x / 2) - W x)²`. -/
theorem dyadic_window_producer_consumer_duality_le_levy {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {N : ℕ} (hN : 1 ≤ N)
    (hzeros : ∀ k ∈ Finset.range N, autocorr f (Real.log ((N + k : ℕ) : ℝ)) = 0)
    {W : ℝ → ℝ}
    (hW : ContinuousOn W (Icc (Real.log (N : ℝ)) (Real.log ((2 * N : ℕ) : ℝ)))) :
    ((∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), autocorr f x * Real.cosh (x / 2)) +
        (∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ),
          (autocorr f 0 - autocorr f x) * W x) -
        (∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), W x) * autocorr f 0) ^ 2 ≤
      2 * autocorr f 0 * biScaleLevyEnergy f *
        ∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), (Real.cosh (x / 2) - W x) ^ 2 := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hle : Real.log (N : ℝ) ≤ Real.log ((2 * N : ℕ) : ℝ) := by
    refine Real.log_le_log hN_pos ?_
    push_cast; linarith
  have hP : ContinuousOn (fun x => Real.cosh (x / 2))
      (Icc (Real.log (N : ℝ)) (Real.log ((2 * N : ℕ) : ℝ))) :=
    (Real.continuous_cosh.comp (continuous_id.div_const 2)).continuousOn
  have hres := correlation_producer_consumer_residual_sq_le hfc hf.continuous hle hP hW
  have hnyq := integral_autocorr_sq_dyadic_window_le_biScaleLevyEnergy hf hfc hN hzeros
  have hW_err_nonneg :
      0 ≤ ∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), (Real.cosh (x / 2) - W x) ^ 2 :=
    intervalIntegral.integral_nonneg hle fun x _ => sq_nonneg _
  exact le_trans hres (mul_le_mul_of_nonneg_right hnyq hW_err_nonneg)

end

end GaloisForLFunctions.BiScaleUncertainty
