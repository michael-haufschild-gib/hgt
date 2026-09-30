import GaloisForLFunctions.RHTower.DeBruijnHeatGaussianAverage

/-!
# Tilted moments of the heat Gaussian

For the normal density `g_t` of variance `2t` and every complex `c`,

`∫ g_t(w − y) e^{wc} dw = e^{yc + tc²}`   (`integral_gaussDensity_sub_mul_exp`),

so every integral of `g_t(w − y)` against a finite combination of exponentials is explicit. Two
consequences are recorded:

* **Chernoff tails.** For `λ ≥ 0`, `1_{w ≤ b} ≤ e^{λ(b − w)}` and `1_{w ≥ b} ≤ e^{λ(w − b)}` give
  `∫_{w ≤ b} g_t(w − y) e^{wα} ≤ e^{λb + y(α−λ) + t(α−λ)²}` and the mirror bound.
* **Log-linear model error.** With `u₀ = y + 2tα` the tilted measure `g_t(w − y) e^{wα} dw` has
  total mass `e^{yα + tα²}` and is a Gaussian centred at `u₀`; the pointwise bound
  `e^{η|x|} − 1 ≤ η|x| e^{η|x|} ≤ η cosh x · 2 cosh(ηx)` gives
  `∫ g_t(w − y) e^{wα} (e^{η|w − u₀|} − 1) ≤ 2η e^{t(1+η)²} e^{yα + tα²}` for `0 ≤ η ≤ 1`.
-/

open Complex MeasureTheory Filter Set

namespace RHTower.DeBruijn

noncomputable section

/-- **The shifted moment generating function.** -/
theorem integral_gaussDensity_sub_mul_exp {t : ℝ} (ht : 0 < t) (y : ℝ) (c : ℂ) :
    ∫ w : ℝ, (gaussDensity t (w - y) : ℂ) * Complex.exp (w * c) =
      Complex.exp (y * c + t * c ^ 2) := by
  rw [← integral_add_right_eq_self _ y]
  have h : ∀ u : ℝ, (gaussDensity t (u + y - y) : ℂ) * Complex.exp (((u + y : ℝ) : ℂ) * c) =
      Complex.exp (y * c) * ((gaussDensity t u : ℂ) * Complex.exp (u * c)) := by
    intro u
    rw [add_sub_cancel_right]
    push_cast
    rw [add_mul, Complex.exp_add]
    ring
  simp_rw [h]
  rw [integral_const_mul, integral_gaussDensity_mul_exp ht, ← Complex.exp_add]

theorem integrable_gaussDensity_sub_mul_exp {t : ℝ} (ht : 0 < t) (y : ℝ) (c : ℂ) :
    Integrable (fun w : ℝ => (gaussDensity t (w - y) : ℂ) * Complex.exp (w * c)) := by
  refine (((integrable_gaussDensity_mul_exp ht c).comp_sub_right y).const_mul
    (Complex.exp (y * c))).congr (Eventually.of_forall fun w => ?_)
  simp only
  push_cast
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  ring

theorem integrable_gaussDensity_sub_mul_rexp {t : ℝ} (ht : 0 < t) (y c : ℝ) :
    Integrable (fun w : ℝ => gaussDensity t (w - y) * Real.exp (w * c)) := by
  refine (integrable_gaussDensity_sub_mul_exp ht y c).norm.congr (Eventually.of_forall fun w => ?_)
  simp only
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gaussDensity_pos ht _),
    ← Complex.ofReal_mul, Complex.norm_exp_ofReal]

theorem integral_gaussDensity_sub_mul_rexp {t : ℝ} (ht : 0 < t) (y c : ℝ) :
    ∫ w : ℝ, gaussDensity t (w - y) * Real.exp (w * c) = Real.exp (y * c + t * c ^ 2) := by
  have h := integral_gaussDensity_sub_mul_exp ht y c
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  push_cast
  exact h

theorem gaussDensity_sub_mul_rexp_nonneg {t : ℝ} (ht : 0 < t) (y c w : ℝ) :
    0 ≤ gaussDensity t (w - y) * Real.exp (w * c) :=
  mul_nonneg (gaussDensity_pos ht _).le (Real.exp_pos _).le

/-- **Lower Chernoff tail.** -/
theorem setIntegral_Iic_gaussDensity_sub_mul_rexp_le {t : ℝ} (ht : 0 < t) (y α b lam : ℝ)
    (hlam : 0 ≤ lam) :
    ∫ w in Iic b, gaussDensity t (w - y) * Real.exp (w * α) ≤
      Real.exp (lam * b + y * (α - lam) + t * (α - lam) ^ 2) := by
  have hint := integrable_gaussDensity_sub_mul_rexp ht y (α - lam)
  calc ∫ w in Iic b, gaussDensity t (w - y) * Real.exp (w * α)
      ≤ ∫ w in Iic b, Real.exp (lam * b) * (gaussDensity t (w - y) * Real.exp (w * (α - lam))) := by
        refine setIntegral_mono_on (integrable_gaussDensity_sub_mul_rexp ht y α).integrableOn
          (hint.const_mul _).integrableOn measurableSet_Iic fun w hw => ?_
        rw [mul_left_comm, ← Real.exp_add]
        gcongr
        · exact (gaussDensity_pos ht _).le
        · have : lam * w ≤ lam * b := mul_le_mul_of_nonneg_left hw hlam
          linarith
    _ ≤ ∫ w, Real.exp (lam * b) * (gaussDensity t (w - y) * Real.exp (w * (α - lam))) :=
        setIntegral_le_integral (hint.const_mul _)
          (Eventually.of_forall fun w => mul_nonneg (Real.exp_pos _).le
            (gaussDensity_sub_mul_rexp_nonneg ht y _ w))
    _ = _ := by
        rw [integral_const_mul, integral_gaussDensity_sub_mul_rexp ht, ← Real.exp_add]
        ring_nf

/-- **Upper Chernoff tail.** -/
theorem setIntegral_Ici_gaussDensity_sub_mul_rexp_le {t : ℝ} (ht : 0 < t) (y α b lam : ℝ)
    (hlam : 0 ≤ lam) :
    ∫ w in Ici b, gaussDensity t (w - y) * Real.exp (w * α) ≤
      Real.exp (-(lam * b) + y * (α + lam) + t * (α + lam) ^ 2) := by
  have hint := integrable_gaussDensity_sub_mul_rexp ht y (α + lam)
  calc ∫ w in Ici b, gaussDensity t (w - y) * Real.exp (w * α)
      ≤ ∫ w in Ici b,
          Real.exp (-(lam * b)) * (gaussDensity t (w - y) * Real.exp (w * (α + lam))) := by
        refine setIntegral_mono_on (integrable_gaussDensity_sub_mul_rexp ht y α).integrableOn
          (hint.const_mul _).integrableOn measurableSet_Ici fun w hw => ?_
        rw [mul_left_comm, ← Real.exp_add]
        gcongr
        · exact (gaussDensity_pos ht _).le
        · have : lam * b ≤ lam * w := mul_le_mul_of_nonneg_left hw hlam
          linarith
    _ ≤ ∫ w, Real.exp (-(lam * b)) * (gaussDensity t (w - y) * Real.exp (w * (α + lam))) :=
        setIntegral_le_integral (hint.const_mul _)
          (Eventually.of_forall fun w => mul_nonneg (Real.exp_pos _).le
            (gaussDensity_sub_mul_rexp_nonneg ht y _ w))
    _ = _ := by
        rw [integral_const_mul, integral_gaussDensity_sub_mul_rexp ht, ← Real.exp_add]
        ring_nf

/-- `e^{η|x|} − 1 ≤ (η/2) Σ_{±,±} e^{(±1 ± η)x}` for `η ≥ 0`. -/
theorem exp_abs_sub_one_le {η : ℝ} (hη : 0 ≤ η) (x : ℝ) :
    Real.exp (η * |x|) - 1 ≤ η / 2 * (Real.exp ((1 + η) * x) + Real.exp ((1 - η) * x) +
      Real.exp (-(1 - η) * x) + Real.exp (-(1 + η) * x)) := by
  have hv : 0 ≤ η * |x| := mul_nonneg hη (abs_nonneg x)
  -- `e^v − 1 ≤ v e^v`
  have h1 : Real.exp (η * |x|) - 1 ≤ η * |x| * Real.exp (η * |x|) := by
    have := Real.add_one_le_exp (-(η * |x|))
    have hpos := Real.exp_pos (η * |x|)
    have hmul : Real.exp (-(η * |x|)) * Real.exp (η * |x|) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith
  -- `|x| ≤ cosh x` and `e^{η|x|} ≤ 2 cosh(ηx)`
  have h2 : |x| ≤ (Real.exp x + Real.exp (-x)) / 2 := by
    have hc := one_add_sq_div_two_le_cosh x
    rw [Real.cosh_eq] at hc
    have hsq : |x| ^ 2 = x ^ 2 := sq_abs x
    nlinarith [sq_nonneg (|x| - 1)]
  have h3 : Real.exp (η * |x|) ≤ Real.exp (η * x) + Real.exp (-(η * x)) := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
      linarith [Real.exp_pos (-(η * x))]
    · rw [abs_of_nonpos hx, mul_neg]
      linarith [Real.exp_pos (η * x)]
  have hprod : (Real.exp x + Real.exp (-x)) * (Real.exp (η * x) + Real.exp (-(η * x))) =
      Real.exp ((1 + η) * x) + Real.exp ((1 - η) * x) + Real.exp (-(1 - η) * x) +
        Real.exp (-(1 + η) * x) := by
    simp only [add_mul, mul_add, ← Real.exp_add]
    ring_nf
  calc Real.exp (η * |x|) - 1 ≤ η * |x| * Real.exp (η * |x|) := h1
    _ ≤ η * ((Real.exp x + Real.exp (-x)) / 2) * (Real.exp (η * x) + Real.exp (-(η * x))) := by
        gcongr
    _ = _ := by rw [← hprod]; ring

/-- The tilted Gaussian against one more exponential. -/
theorem integral_gaussDensity_sub_mul_rexp_mul_rexp {t : ℝ} (ht : 0 < t) (y α lam u : ℝ) :
    ∫ w, gaussDensity t (w - y) * Real.exp (w * α) * Real.exp (lam * (w - u)) =
      Real.exp (-(lam * u) + y * (α + lam) + t * (α + lam) ^ 2) := by
  have h : ∀ w : ℝ, gaussDensity t (w - y) * Real.exp (w * α) * Real.exp (lam * (w - u)) =
      Real.exp (-(lam * u)) * (gaussDensity t (w - y) * Real.exp (w * (α + lam))) := by
    intro w
    have he : Real.exp (w * α) * Real.exp (lam * (w - u)) =
        Real.exp (-(lam * u)) * Real.exp (w * (α + lam)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      ring_nf
    linear_combination gaussDensity t (w - y) * he
  simp_rw [h]
  rw [integral_const_mul, integral_gaussDensity_sub_mul_rexp ht, ← Real.exp_add]
  ring_nf

theorem integrable_gaussDensity_sub_mul_rexp_mul_rexp {t : ℝ} (ht : 0 < t) (y α lam u : ℝ) :
    Integrable (fun w => gaussDensity t (w - y) * Real.exp (w * α) * Real.exp (lam * (w - u))) := by
  refine ((integrable_gaussDensity_sub_mul_rexp ht y (α + lam)).const_mul
    (Real.exp (-(lam * u)))).congr (Eventually.of_forall fun w => ?_)
  have he : Real.exp (w * α) * Real.exp (lam * (w - u)) =
      Real.exp (-(lam * u)) * Real.exp (w * (α + lam)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    ring_nf
  simp only
  linear_combination -(gaussDensity t (w - y) * he)

/-- Centred at `u₀ = y + 2tα`, the extra exponential only costs `e^{tλ²}`. -/
theorem integral_gaussDensity_sub_mul_rexp_mul_rexp_centre {t : ℝ} (ht : 0 < t) (y α lam : ℝ) :
    ∫ w, gaussDensity t (w - y) * Real.exp (w * α) * Real.exp (lam * (w - (y + 2 * t * α))) =
      Real.exp (y * α + t * α ^ 2) * Real.exp (t * lam ^ 2) := by
  rw [integral_gaussDensity_sub_mul_rexp_mul_rexp ht, ← Real.exp_add]
  ring_nf

/-- **The log-linear model error.** With `u₀ = y + 2tα` and `0 ≤ η`,
`∫ g_t(w − y) e^{wα} (e^{η|w − u₀|} − 1) dw ≤ 2η e^{t(1+η)²} e^{yα + tα²}`. -/
theorem integral_gaussDensity_sub_mul_rexp_mul_exp_abs_sub_one_le {t : ℝ} (ht : 0 < t)
    (y α : ℝ) {η : ℝ} (hη : 0 ≤ η) :
    ∫ w, gaussDensity t (w - y) * Real.exp (w * α) *
        (Real.exp (η * |w - (y + 2 * t * α)|) - 1) ≤
      2 * η * Real.exp (t * (1 + η) ^ 2) * Real.exp (y * α + t * α ^ 2) := by
  set u := y + 2 * t * α with hu
  set G : ℝ → ℝ := fun w => gaussDensity t (w - y) * Real.exp (w * α) with hG
  have hint : ∀ lam : ℝ, Integrable (fun w => G w * Real.exp (lam * (w - u))) := fun lam =>
    integrable_gaussDensity_sub_mul_rexp_mul_rexp ht y α lam u
  have hval : ∀ lam : ℝ, ∫ w, G w * Real.exp (lam * (w - u)) =
      Real.exp (y * α + t * α ^ 2) * Real.exp (t * lam ^ 2) := fun lam =>
    integral_gaussDensity_sub_mul_rexp_mul_rexp_centre ht y α lam
  have hG0 : ∀ w, 0 ≤ G w := fun w => gaussDensity_sub_mul_rexp_nonneg ht y α w
  have hsum : Integrable (fun w => η / 2 * (G w * Real.exp ((1 + η) * (w - u)) +
      G w * Real.exp ((1 - η) * (w - u)) + G w * Real.exp (-(1 - η) * (w - u)) +
      G w * Real.exp (-(1 + η) * (w - u)))) :=
    ((((hint _).add (hint _)).add (hint _)).add (hint _)).const_mul _
  calc ∫ w, G w * (Real.exp (η * |w - u|) - 1)
      ≤ ∫ w, η / 2 * (G w * Real.exp ((1 + η) * (w - u)) +
          G w * Real.exp ((1 - η) * (w - u)) + G w * Real.exp (-(1 - η) * (w - u)) +
          G w * Real.exp (-(1 + η) * (w - u))) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun w => ?_) hsum
          (Eventually.of_forall fun w => ?_)
        · have : 1 ≤ Real.exp (η * |w - u|) := Real.one_le_exp (mul_nonneg hη (abs_nonneg _))
          exact mul_nonneg (hG0 w) (by linarith)
        · have h := exp_abs_sub_one_le hη (w - u)
          refine le_trans (mul_le_mul_of_nonneg_left h (hG0 w)) (le_of_eq ?_)
          ring_nf
    _ = η / 2 * (Real.exp (y * α + t * α ^ 2) * Real.exp (t * (1 + η) ^ 2) +
          Real.exp (y * α + t * α ^ 2) * Real.exp (t * (1 - η) ^ 2) +
          Real.exp (y * α + t * α ^ 2) * Real.exp (t * (-(1 - η)) ^ 2) +
          Real.exp (y * α + t * α ^ 2) * Real.exp (t * (-(1 + η)) ^ 2)) := by
        rw [integral_const_mul, integral_add ?_ (hint _), integral_add ?_ (hint _),
          integral_add (hint _) (hint _), hval, hval, hval, hval]
        · exact (hint _).add (hint _)
        · exact ((hint _).add (hint _)).add (hint _)
    _ ≤ 2 * η * Real.exp (t * (1 + η) ^ 2) * Real.exp (y * α + t * α ^ 2) := by
        have hle : Real.exp (t * (1 - η) ^ 2) ≤ Real.exp (t * (1 + η) ^ 2) :=
          Real.exp_le_exp.mpr (by nlinarith [mul_nonneg ht.le hη])
        have e1 : (-(1 - η)) ^ 2 = (1 - η) ^ 2 := by ring
        have e2 : (-(1 + η)) ^ 2 = (1 + η) ^ 2 := by ring
        rw [e1, e2]
        have hE := Real.exp_pos (y * α + t * α ^ 2)
        nlinarith [mul_le_mul_of_nonneg_left hle hE.le]

end

end RHTower.DeBruijn
