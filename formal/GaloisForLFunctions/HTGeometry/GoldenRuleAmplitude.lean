import GaloisForLFunctions.HTGeometry.BoundedMultiplierCalculus
import GaloisForLFunctions.HTGeometry.GoldenRuleKernel

/-!
# The first-order amplitude operator

First-order time-dependent perturbation theory produces, in the interaction picture, the vector

```text
∫₀ᵗ exp (i s (ω − E₀)) ds · v ,
```

that is, multiplication of the form factor `v` by the *amplitude symbol*

```text
A t Δ = ∫₀ᵗ exp (i s Δ) ds = t · exp (i t Δ / 2) · sinc (t Δ / 2) ,     Δ = ω − E₀ .
```

Written through `Real.sinc` the symbol is an entire, bounded, resonance-regular function of the
energy mismatch: no case distinction at `Δ = 0` is needed, and its squared modulus is exactly the
golden-rule kernel.  The two facts this file proves are

* `normSq_ampSymbol : ‖A t Δ‖² = K t Δ`, the bridge to the golden-rule limit, and
* `hasDerivAt_ampOp`, which identifies the multiplier of `A t` as the exact interaction-picture
  primitive of `exp (i t (ω − E₀))`; the fundamental theorem of calculus then evaluates the
  Bochner integral of the first-order Dyson term in closed form.
-/

open MeasureTheory Filter

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## The scalar amplitude symbol -/

/-- Closed form of the first-order amplitude `∫₀ᵗ exp (i s Δ) ds`. -/
def ampSymbol (t Δ : ℝ) : ℂ :=
  (t : ℂ) * Complex.exp (((t * Δ / 2 : ℝ) : ℂ) * Complex.I) * ((Real.sinc (t * Δ / 2) : ℝ) : ℂ)

theorem exp_ofReal_mul_I (u : ℝ) :
    Complex.exp (((u : ℝ) : ℂ) * Complex.I)
      = ((Real.cos u : ℝ) : ℂ) + ((Real.sin u : ℝ) : ℂ) * Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

@[simp] theorem ampSymbol_zero_time (Δ : ℝ) : ampSymbol 0 Δ = 0 := by
  simp [ampSymbol]

@[simp] theorem ampSymbol_zero_gap (t : ℝ) : ampSymbol t 0 = (t : ℂ) := by
  simp [ampSymbol]

/-- The Euler identity behind the closed form. -/
theorem two_sin_mul_I_mul_exp (θ : ℝ) :
    (2 : ℂ) * ((Real.sin θ : ℝ) : ℂ) * Complex.I * Complex.exp (((θ : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((θ : ℝ) : ℂ) * Complex.I) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I) - 1 := by
  have hpyth : ((Real.sin θ : ℝ) : ℂ) ^ (2 : ℕ) + ((Real.cos θ : ℝ) : ℂ) ^ (2 : ℕ) = 1 := by
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) (Real.sin_sq_add_cos_sq θ)
  rw [exp_ofReal_mul_I]
  linear_combination (-1 : ℂ) * hpyth + ((Real.sin θ : ℝ) : ℂ) ^ (2 : ℕ) * Complex.I_sq

/-- **The defining property of the amplitude symbol.**  `A t Δ · (i Δ) = exp (i t Δ) − 1`, with no
case distinction at the resonance. -/
theorem ampSymbol_mul (t Δ : ℝ) :
    ampSymbol t Δ * ((Δ : ℂ) * Complex.I)
      = Complex.exp (((t * Δ : ℝ) : ℂ) * Complex.I) - 1 := by
  rcases eq_or_ne (t * Δ) 0 with h0 | h0
  · have hhalf : (t * Δ / 2 : ℝ) = 0 := by rw [h0]; norm_num
    have hlhs : ampSymbol t Δ * ((Δ : ℂ) * Complex.I) = ((t * Δ : ℝ) : ℂ) * Complex.I := by
      rw [ampSymbol, hhalf]
      simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, Real.sinc_zero,
        Complex.ofReal_one, mul_one]
      push_cast
      ring
    rw [hlhs, h0]
    simp
  · set θ : ℝ := t * Δ / 2 with hθdef
    have hθ : θ ≠ 0 := by
      rw [hθdef]
      intro hc
      exact h0 (by linarith)
    have hθC : ((θ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hθ
    have h2θ : (t : ℂ) * (Δ : ℂ) = 2 * ((θ : ℝ) : ℂ) := by
      have : (2 : ℝ) * θ = t * Δ := by rw [hθdef]; ring
      exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) this.symm
    have hexp2 : Complex.exp (((t * Δ : ℝ) : ℂ) * Complex.I)
        = Complex.exp (((θ : ℝ) : ℂ) * Complex.I) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      have : (2 : ℝ) * θ = t * Δ := by rw [hθdef]; ring
      rw [← this]
      push_cast
      ring
    rw [hexp2, ← two_sin_mul_I_mul_exp θ, ampSymbol, ← hθdef, Real.sinc_of_ne_zero hθ]
    push_cast
    field_simp
    linear_combination Complex.sin ((θ : ℝ) : ℂ) * h2θ

theorem norm_ampSymbol (t Δ : ℝ) : ‖ampSymbol t Δ‖ = |t| * |Real.sinc (t * Δ / 2)| := by
  rw [ampSymbol, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Complex.norm_exp_ofReal_mul_I, Real.norm_eq_abs, Real.norm_eq_abs, mul_one]

/-- **The squared amplitude symbol is the golden-rule kernel.** -/
theorem normSq_ampSymbol (t Δ : ℝ) : ‖ampSymbol t Δ‖ ^ (2 : ℕ) = goldenRuleKernel t Δ := by
  rw [norm_ampSymbol, goldenRuleKernel, mul_pow, sq_abs, sq_abs,
    show Δ * t / 2 = t * Δ / 2 by ring]

theorem norm_ampSymbol_le (t Δ : ℝ) : ‖ampSymbol t Δ‖ ≤ |t| := by
  rw [norm_ampSymbol]
  calc |t| * |Real.sinc (t * Δ / 2)| ≤ |t| * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sinc_le_one _) (abs_nonneg t)
    _ = |t| := mul_one _

/-- **Second-order Taylor bound for the amplitude symbol**, uniform in the energy mismatch. -/
theorem ampSymbol_taylor (t Δ h : ℝ) (hb : |h * Δ| ≤ 1) :
    ‖ampSymbol (t + h) Δ - ampSymbol t Δ
        - (h : ℂ) * Complex.exp (((t * Δ : ℝ) : ℂ) * Complex.I)‖
      ≤ 3 / 4 * h ^ (2 : ℕ) * |Δ| := by
  rcases eq_or_ne Δ 0 with hΔ | hΔ
  · subst hΔ
    simp
  · set z : ℂ := ((h * Δ : ℝ) : ℂ) * Complex.I with hzdef
    have hznorm : ‖z‖ = |h * Δ| := by
      rw [hzdef, norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs, mul_one]
    set u : ℂ := ampSymbol (t + h) Δ - ampSymbol t Δ
      - (h : ℂ) * Complex.exp (((t * Δ : ℝ) : ℂ) * Complex.I) with hudef
    have hsplit : Complex.exp ((((t + h) * Δ : ℝ) : ℂ) * Complex.I)
        = Complex.exp (((t * Δ : ℝ) : ℂ) * Complex.I) * Complex.exp z := by
      rw [hzdef, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hmul : u * ((Δ : ℂ) * Complex.I)
        = Complex.exp (((t * Δ : ℝ) : ℂ) * Complex.I) * (Complex.exp z - 1 - z) := by
      rw [hudef, sub_mul, sub_mul, ampSymbol_mul, ampSymbol_mul, hsplit]
      rw [hzdef]
      push_cast
      ring
    have hnormmul : ‖u‖ * |Δ| = ‖Complex.exp z - 1 - z‖ := by
      have h1 : ‖u * ((Δ : ℂ) * Complex.I)‖ = ‖u‖ * |Δ| := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs, mul_one]
      rw [← h1, hmul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    have hbound : ‖Complex.exp z - 1 - z‖ ≤ 3 / 4 * (h * Δ) ^ (2 : ℕ) := by
      have := norm_exp_sub_one_sub_le (z := z) (by rw [hznorm]; exact hb)
      rw [hznorm] at this
      calc ‖Complex.exp z - 1 - z‖ ≤ 3 / 4 * |h * Δ| ^ (2 : ℕ) := this
        _ = 3 / 4 * (h * Δ) ^ (2 : ℕ) := by rw [sq_abs]
    have habs : (0 : ℝ) < |Δ| := abs_pos.mpr hΔ
    have hfinal : ‖u‖ * |Δ| ≤ (3 / 4 * h ^ (2 : ℕ) * |Δ|) * |Δ| := by
      rw [hnormmul]
      refine hbound.trans (le_of_eq ?_)
      have : (h * Δ) ^ (2 : ℕ) = h ^ (2 : ℕ) * (|Δ| * |Δ|) := by
        rw [← abs_mul, abs_of_nonneg (mul_self_nonneg Δ)]
        ring
      rw [this]
      ring
    exact le_of_mul_le_mul_right hfinal habs

/-! ## The amplitude operator -/

section Operator

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The squared `L²` norm of a class as an integral of squared norms, for an arbitrary measure. -/
theorem lpTwo_norm_sq_eq_integral (f : Lp ℂ 2 μ) :
    ‖f‖ ^ (2 : ℕ) = ∫ x, ‖(f : α → ℂ) x‖ ^ (2 : ℕ) ∂μ := by
  have h1 : (inner ℂ f f : ℂ) = ∫ x, (inner ℂ ((f : α → ℂ) x) ((f : α → ℂ) x) : ℂ) ∂μ :=
    L2.inner_def f f
  have h2 : ∀ z : ℂ, (inner ℂ z z : ℂ) = ((‖z‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    intro z
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have h3 : (inner ℂ f f : ℂ) = ((‖f‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [h3] at h1
  simp only [h2] at h1
  rw [integral_complex_ofReal] at h1
  exact Complex.ofReal_inj.mp h1

@[fun_prop]
theorem continuous_ampSymbol (t : ℝ) : Continuous (ampSymbol t) := by
  unfold ampSymbol
  fun_prop

theorem measurable_ampSymbol_comp (E₀ : ℝ) {ω : α → ℝ} (hω : Measurable ω) (t : ℝ) :
    Measurable fun x : α => ampSymbol t (ω x - E₀) :=
  (continuous_ampSymbol t).measurable.comp (hω.sub measurable_const)

/-- Multiplication by the first-order amplitude symbol. -/
def ampOp (E₀ : ℝ) (ω : α → ℝ) (hω : Measurable ω) (t : ℝ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  lpBoundedMulCLM (p := 2) (μ := μ) (measurable_ampSymbol_comp E₀ hω t) (abs_nonneg t)
    (fun x => norm_ampSymbol_le t (ω x - E₀))

theorem ampOp_coeFn (E₀ : ℝ) (ω : α → ℝ) (hω : Measurable ω) (t : ℝ) (f : Lp ℂ 2 μ) :
    ((ampOp (μ := μ) E₀ ω hω t f : Lp ℂ 2 μ) : α → ℂ)
      =ᵐ[μ] fun x => ampSymbol t (ω x - E₀) * (f : α → ℂ) x :=
  lpBoundedMulCLM_coeFn _ _ _ f

/-- The interaction-picture multiplier `exp (i s (ω − E₀))`. -/
def intOp (E₀ : ℝ) (ω : α → ℝ) (hω : Measurable ω) (s : ℝ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (Complex.exp (((-(s * E₀) : ℝ) : ℂ) * Complex.I)) • (freeGroup (μ := μ) ω hω (-s))

theorem intOp_coeFn (E₀ : ℝ) (ω : α → ℝ) (hω : Measurable ω) (s : ℝ) (f : Lp ℂ 2 μ) :
    ((intOp (μ := μ) E₀ ω hω s f : Lp ℂ 2 μ) : α → ℂ)
      =ᵐ[μ] fun x => Complex.exp (((s * (ω x - E₀) : ℝ) : ℂ) * Complex.I) * (f : α → ℂ) x := by
  have hval : (intOp (μ := μ) E₀ ω hω s f)
      = (Complex.exp (((-(s * E₀) : ℝ) : ℂ) * Complex.I)) •
        ((freeGroup (μ := μ) ω hω (-s)) f) := rfl
  rw [hval]
  filter_upwards [Lp.coeFn_smul (Complex.exp (((-(s * E₀) : ℝ) : ℂ) * Complex.I))
      ((freeGroup (μ := μ) ω hω (-s)) f), freeGroup_coeFn ω hω (-s) f] with x h1 h2
  rw [h1]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h2, freeSymbol, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem continuous_intOp (E₀ : ℝ) (ω : α → ℝ) (hω : Measurable ω) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, |ω x| ≤ C) : Continuous (intOp (μ := μ) E₀ ω hω) := by
  have h1 : Continuous fun s : ℝ => Complex.exp (((-(s * E₀) : ℝ) : ℂ) * Complex.I) := by fun_prop
  have h2 : Continuous fun s : ℝ => freeGroup (μ := μ) ω hω (-s) :=
    (continuous_freeGroup ω hω hC0 hC).comp continuous_neg
  exact h1.smul h2

/-- **The amplitude multiplier is the interaction-picture primitive.** -/
theorem hasDerivAt_ampOp (E₀ : ℝ) (ω : α → ℝ) (hω : Measurable ω) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, |ω x| ≤ C) (t : ℝ) :
    HasDerivAt (ampOp (μ := μ) E₀ ω hω) (intOp (μ := μ) E₀ ω hω t) t := by
  have hD : ∀ x : α, |ω x - E₀| ≤ C + |E₀| := by
    intro x
    have hx : |ω x| ≤ C := hC x
    have h1 : |ω x - E₀| ≤ |ω x| + |E₀| := by
      rw [abs_le]
      constructor <;>
        linarith [neg_abs_le (ω x), neg_abs_le E₀, le_abs_self (ω x), le_abs_self E₀]
    linarith
  have hDnn : (0 : ℝ) ≤ C + |E₀| := add_nonneg hC0 (abs_nonneg _)
  refine hasDerivAt_of_ae_mul (K := 3 / 4 * (C + |E₀|))
    (φ := fun s x => ampSymbol s (ω x - E₀))
    (ψ := fun x => Complex.exp (((t * (ω x - E₀) : ℝ) : ℂ) * Complex.I)) (by linarith) ?_ ?_ ?_
  · intro s f
    exact ampOp_coeFn E₀ ω hω s f
  · intro f
    exact intOp_coeFn E₀ ω hω t f
  · have hpos : (0 : ℝ) < 1 / (C + |E₀| + 1) := by positivity
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hpos] with h hh
    have hhabs : |h| ≤ 1 / (C + |E₀| + 1) := by
      have hd := Metric.mem_ball.mp hh
      rw [Real.dist_eq, sub_zero] at hd
      exact hd.le
    intro x
    have hbx : |h * (ω x - E₀)| ≤ 1 := by
      rw [abs_mul]
      have h2 : |h| * |ω x - E₀| ≤ (1 / (C + |E₀| + 1)) * (C + |E₀|) :=
        mul_le_mul hhabs (hD x) (abs_nonneg _) (by positivity)
      have h3 : (1 / (C + |E₀| + 1)) * (C + |E₀|) ≤ 1 := by
        rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
        linarith
      linarith
    calc ‖ampSymbol (t + h) (ω x - E₀) - ampSymbol t (ω x - E₀)
            - (h : ℂ) * Complex.exp (((t * (ω x - E₀) : ℝ) : ℂ) * Complex.I)‖
        ≤ 3 / 4 * h ^ (2 : ℕ) * |ω x - E₀| := ampSymbol_taylor t (ω x - E₀) h hbx
      _ ≤ 3 / 4 * (C + |E₀|) * h ^ (2 : ℕ) := by nlinarith [sq_nonneg h, hD x]

theorem ampOp_zero (E₀ : ℝ) (ω : α → ℝ) (hω : Measurable ω) :
    ampOp (μ := μ) E₀ ω hω 0 = 0 := by
  refine lpBoundedMulCLM_eq_zero _ _ _ (Filter.Eventually.of_forall fun x => ?_)
  simp

/-- **The first-order Dyson integral in closed form**, at the operator level. -/
theorem integral_intOp (E₀ : ℝ) (ω : α → ℝ) (hω : Measurable ω) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, |ω x| ≤ C) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, intOp (μ := μ) E₀ ω hω s) = ampOp (μ := μ) E₀ ω hω t := by
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (ampOp (μ := μ) E₀ ω hω) (intOp (μ := μ) E₀ ω hω s) s :=
    fun s _ => hasDerivAt_ampOp E₀ ω hω hC0 hC s
  have hcont : Continuous (intOp (μ := μ) E₀ ω hω) := continuous_intOp E₀ ω hω hC0 hC
  have hfin := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable 0 t)
  rw [hfin, ampOp_zero, sub_zero]

theorem integral_intOp_apply (E₀ : ℝ) (ω : α → ℝ) (hω : Measurable ω) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, |ω x| ≤ C) (t : ℝ) (f : Lp ℂ 2 μ) :
    (∫ s in (0 : ℝ)..t, (intOp (μ := μ) E₀ ω hω s) f) = (ampOp (μ := μ) E₀ ω hω t) f := by
  have hcont : Continuous (intOp (μ := μ) E₀ ω hω) := continuous_intOp E₀ ω hω hC0 hC
  rw [← ContinuousLinearMap.intervalIntegral_apply (hcont.intervalIntegrable 0 t) f,
    integral_intOp E₀ ω hω hC0 hC t]

/-- **The first-order transition probability is the golden-rule kernel integrated against the
form-factor density.** -/
theorem norm_sq_ampOp_apply (E₀ : ℝ) (ω : α → ℝ) (hω : Measurable ω) (t : ℝ) (f : Lp ℂ 2 μ) :
    ‖(ampOp (μ := μ) E₀ ω hω t) f‖ ^ (2 : ℕ)
      = ∫ x, goldenRuleKernel t (ω x - E₀) * ‖(f : α → ℂ) x‖ ^ (2 : ℕ) ∂μ := by
  rw [lpTwo_norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [ampOp_coeFn E₀ ω hω t f] with x hx
  rw [hx, norm_mul, mul_pow, normSq_ampSymbol]

end Operator

end GaloisForLFunctions.HTGeometry
