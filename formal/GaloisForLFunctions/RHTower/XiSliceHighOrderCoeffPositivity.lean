import GaloisForLFunctions.RHTower.XiSliceCoeffQuarterArc


/-!
# High-order positivity of the slice coefficients

Let `c_n(t)` be the Taylor coefficients of `g_t(x) = ξ(½+x+it) ξ(½−x+it)` at `x = 0`.  The
Riemann hypothesis is equivalent to `c_n(t) ≥ 0` for every `t` and `n`
(`riemannHypothesis_iff_xiSliceCoeff_nonneg`).  This file proves the unconditional statement that the
coefficients of high order are positive, height by height:

```
∃ t₀ κ, ∀ t ≥ t₀, ∀ k, κ log t ≤ k ≤ (t log t)/8  →  c_{2k}(t) > 0.
```

The proof is a saddle-point evaluation of Cauchy's integral on the circle `|x| = R`, where `R` solves
`R g_t'(R)/g_t(R) = 2k`.  With `S(θ) = g_t(Re^{iθ}) e^{−2ikθ}/g_t(R)` and `Λ = R log t`:

* by the quarter-arc formula, `c_{2k}(t)` is a positive multiple of `∫₀^{π/2} Re S`;
* on `θ ≤ Λ^{−1/2}` the saddle-arc control gives `Re S ≥ 7/40`, and up to `Λ^{−2/5}` it gives
  `Re S ≥ 0`, because the phase error `≤ 43Λθ³` stays below `1/2`;
* on `Λ^{−2/5} ≤ θ ≤ 1/1000` the slope `F'(R) ≥ (9/10) log t` gives `|S| ≤ exp(−Λθ²/8)`;
* on `1/1000 ≤ θ ≤ π/2` the circle-decay law of `|g_t|` gives
  `|S| ≤ 16e^{15}exp(−Λ/(6·10⁶)) + (4+12t)²e^{15}(t/2π)^{−9/2}`.

Each error region contributes at most `Λ^{−1/2}/20` once `Λ` and `t` are large, and
`Λ ≥ κ log t` because `R ≥ k/log t`.
-/

open Complex Real Metric intervalIntegral

namespace RHTower

noncomputable section

/-- Shorthand for the normalised arc value of the slice product at the exponent `2k`. -/
abbrev sliceArc (t R : ℝ) (k : ℕ) (θ : ℝ) : ℂ :=
  HTGeometry.saddleArc (xiSliceProduct t) R (2 * k) θ

theorem saddle_cubic_coeff_eq {R D θ : ℝ} (hR : 0 < R) :
    32 * (R * D) / (R / 2) ^ 2 * R ^ 2 * θ ^ 3 / 3 = 128 / 3 * (R * D) * θ ^ 3 := by
  field_simp; ring

/-- `1 − cos θ ≥ θ²/5` on `|θ| ≤ π`. -/
theorem one_sub_cos_ge_sq_div_five {θ : ℝ} (hθ : |θ| ≤ Real.pi) : θ ^ 2 / 5 ≤ 1 - Real.cos θ := by
  have h := Real.cos_le_one_sub_mul_cos_sq hθ
  have hpi : Real.pi ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hpi0 : 0 < Real.pi ^ 2 := by positivity
  have : θ ^ 2 / 5 ≤ 2 / Real.pi ^ 2 * θ ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hpi0]
    nlinarith [sq_nonneg θ]
  linarith

/-- `1 − cos θ ≤ θ²/2`. -/
theorem one_sub_cos_le_half_sq (θ : ℝ) : 1 - Real.cos θ ≤ θ ^ 2 / 2 := by
  have := Real.one_sub_sq_div_two_le_cos (x := θ); linarith

/-- **Core of the saddle.**  If the phase `φ = |F₁|Rθ³/6 + (128/3)RDθ³` is at most `1/2`, then
`Re S(θ) ≥ (7/8) exp(−F₁R(1−cos θ) − 1/2)`, in particular `Re S(θ) ≥ 0`. -/
theorem sliceArc_re_core {t R θ : ℝ} {k : ℕ} (ht : 8 ≤ t) (hR : 5 ≤ R) (hRt : R ≤ t / 2)
    (hsad : (HTGeometry.scaledLogDeriv (xiSliceProduct t) R).re = 2 * k)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 4)
    (hφ : |(deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re| * R * θ ^ 3 / 6
        + 128 / 3 * (R * xiSliceDiscConstant t) * θ ^ 3 ≤ 1 / 2) :
    7 / 8 * Real.exp (-((deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re * R
        * (1 - Real.cos θ)) - 1 / 2) ≤ (sliceArc t R k θ).re := by
  have hR0 : 0 < R := by linarith
  have hb := xiSlice_saddleArc_bounds ht hR hRt hθ0 hθ
  rw [hsad, saddle_cubic_coeff_eq hR0] at hb
  set F₁ := (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re
  have hDpos : 0 < xiSliceDiscConstant t := by
    unfold xiSliceDiscConstant
    have h1 : 0 ≤ Real.log (3 * t / 2) := Real.log_nonneg (by linarith)
    have h2 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    have h3 := xiLogDerivStirlingConstant_pos
    have h4 := Real.pi_pos
    positivity
  have hc3 : 0 ≤ 128 / 3 * (R * xiSliceDiscConstant t) * θ ^ 3 := by positivity
  have ha : 0 ≤ |F₁| * R * θ ^ 3 / 6 := by positivity
  set φ := |F₁| * R * θ ^ 3 / 6 + 128 / 3 * (R * xiSliceDiscConstant t) * θ ^ 3 with hφdef
  have hφ0 : 0 ≤ φ := by rw [hφdef]; linarith
  have hlow := hb.2 (by linarith [Real.pi_gt_three])
  have hcos : 7 / 8 ≤ Real.cos φ := by
    have := Real.one_sub_sq_div_two_le_cos (x := φ); nlinarith
  have hexp : Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 1 / 2)
      ≤ Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 128 / 3 * (R * xiSliceDiscConstant t) * θ ^ 3) := by
    apply Real.exp_le_exp.mpr
    have := hφ; rw [hφdef] at this
    linarith
  calc 7 / 8 * Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 1 / 2)
      ≤ Real.cos φ * Real.exp (-(F₁ * R * (1 - Real.cos θ))
          - 128 / 3 * (R * xiSliceDiscConstant t) * θ ^ 3) := by
        apply mul_le_mul hcos hexp (Real.exp_pos _).le (by linarith)
    _ = Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 128 / 3 * (R * xiSliceDiscConstant t) * θ ^ 3)
          * Real.cos φ := by ring
    _ ≤ _ := hlow

/-- **Gaussian decay away from the saddle.**  If `F₁ ≥ (9/10) log t`, the disc constant is at most
`log t` and `0 ≤ θ ≤ 1/1000`, then `|S(θ)| ≤ exp(−R log t · θ²/8)`. -/
theorem sliceArc_norm_middle {t R θ : ℝ} {k : ℕ} (ht : 8 ≤ t) (hR : 5 ≤ R) (hRt : R ≤ t / 2)
    (hsad : (HTGeometry.scaledLogDeriv (xiSliceProduct t) R).re = 2 * k)
    (hF₁ : 9 / 10 * Real.log t ≤ (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re)
    (hD : xiSliceDiscConstant t ≤ Real.log t) (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 1000) :
    ‖sliceArc t R k θ‖ ≤ Real.exp (-(R * Real.log t) * θ ^ 2 / 8) := by
  have hR0 : 0 < R := by linarith
  have hb := (xiSlice_saddleArc_bounds ht hR hRt hθ0 (by linarith)).1
  rw [hsad, saddle_cubic_coeff_eq hR0] at hb
  refine hb.trans (Real.exp_le_exp.mpr ?_)
  set F₁ := (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re
  have hlog : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hcos := one_sub_cos_ge_sq_div_five (θ := θ)
    (by rw [abs_of_nonneg hθ0]; linarith [Real.pi_gt_three])
  have h1 : 9 / 10 * Real.log t * R * (θ ^ 2 / 5) ≤ F₁ * R * (1 - Real.cos θ) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_right hF₁ hR0.le) hcos (by positivity)
    nlinarith
  have h2 : 128 / 3 * (R * xiSliceDiscConstant t) * θ ^ 3
      ≤ 128 / 3 * (R * Real.log t) * θ ^ 2 * (1 / 1000) := by
    have : θ ^ 3 = θ ^ 2 * θ := by ring
    rw [this]
    have hDR : R * xiSliceDiscConstant t ≤ R * Real.log t := mul_le_mul_of_nonneg_left hD hR0.le
    have hθ2 : 0 ≤ θ ^ 2 := sq_nonneg θ
    calc 128 / 3 * (R * xiSliceDiscConstant t) * (θ ^ 2 * θ)
        ≤ 128 / 3 * (R * Real.log t) * (θ ^ 2 * θ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
      _ ≤ 128 / 3 * (R * Real.log t) * (θ ^ 2 * (1 / 1000)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hθ hθ2
      _ = _ := by ring
  have hΛ : 0 ≤ R * Real.log t * θ ^ 2 := by positivity
  nlinarith

/-- `|S(θ)| = |g_t(Re^{iθ})| / g_t(R)`. -/
theorem norm_sliceArc_eq (t R θ : ℝ) (k : ℕ) :
    ‖sliceArc t R k θ‖ = ‖xiSliceProduct t ((R : ℂ) * Complex.exp ((θ : ℂ) * I))‖
      / ‖xiSliceProduct t (R : ℂ)‖ := by
  simp only [sliceArc, HTGeometry.saddleArc, norm_div, norm_mul]
  rw [show ‖Complex.exp (-(((2 * (k : ℝ) * θ : ℝ)) : ℂ) * I)‖ = 1 by
    rw [Complex.norm_exp]; simp]
  ring

/-- **Tail of the arc.**  For `t ≥ 10`, `6 ≤ R ≤ t/2`, `log(t/2π) ≥ (9/10) log t` and
`1/1000 ≤ θ ≤ π/2`,
`|S(θ)| ≤ 16 e^{15} exp(−R log t/(6·10⁶)) + (4+12t)² e^{15} exp(−(9/2) log(t/2π))`. -/
theorem sliceArc_norm_tail {t R θ : ℝ} (k : ℕ) (ht : 10 ≤ t) (hR : 6 ≤ R) (hRt : R ≤ t / 2)
    (hlog : 9 / 10 * Real.log t ≤ Real.log (t / (2 * Real.pi)))
    (hθ1 : 1 / 1000 ≤ θ) (hθ2 : θ ≤ Real.pi / 2) :
    ‖sliceArc t R k θ‖ ≤ 16 * Real.exp 15 * Real.exp (-(R * Real.log t) / 6000000)
      + (4 + 12 * t) ^ 2 * Real.exp 15 * Real.exp (-(9 / 2) * Real.log (t / (2 * Real.pi))) := by
  have hR0 : 0 < R := by linarith
  have hcos0 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθ2⟩
  have hcos1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hsin : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
  have hgR : 0 < ‖xiSliceProduct t (R : ℂ)‖ :=
    norm_pos_iff.mpr (xiSliceProduct_ne_zero_of_re (by simp; linarith))
  have hb := norm_xiSliceProduct_circle_le_explicit (θ := θ) (by linarith) (by linarith) hRt hcos0
  rw [norm_sliceArc_eq, div_le_iff₀ hgR]
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hlog2 : 0 ≤ Real.log (t / (2 * Real.pi)) := by linarith
  have hE : 12 * (R * (1 - Real.cos θ) + R * |Real.sin θ|) / t + 4 * (1 / 2 + R * Real.cos θ) / t
      ≤ 15 := by
    have ht0 : 0 < t := by linarith
    have h1 : 12 * (R * (1 - Real.cos θ) + R * |Real.sin θ|) / t ≤ 12 := by
      rw [div_le_iff₀ ht0]
      have : R * (1 - Real.cos θ) + R * |Real.sin θ| ≤ 2 * R := by nlinarith
      linarith
    have h2 : 4 * (1 / 2 + R * Real.cos θ) / t ≤ 3 := by
      rw [div_le_iff₀ ht0]
      have : R * Real.cos θ ≤ R := by nlinarith
      linarith
    linarith
  split_ifs at hb with hA
  · -- `R cos θ ≥ 3/2`: the `ζ` ratio costs `16`
    have hc := one_sub_cos_ge_sq_div_five (θ := θ)
      (by rw [abs_of_nonneg (by linarith)]; linarith [Real.pi_pos])
    have hθsq : (1 / 1000 : ℝ) ^ 2 ≤ θ ^ 2 := by gcongr
    have hgain : R * Real.log t / 6000000 ≤ R * (1 - Real.cos θ) * Real.log (t / (2 * Real.pi)) := by
      have h1 : 1 / 5000000 ≤ 1 - Real.cos θ := by nlinarith
      have h2 : R * (1 / 5000000) * (9 / 10 * Real.log t)
          ≤ R * (1 - Real.cos θ) * Real.log (t / (2 * Real.pi)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h1 hR0.le) hlog (by positivity)
        nlinarith
      nlinarith
    have hexp : Real.exp (-(R * (1 - Real.cos θ)) * Real.log (t / (2 * Real.pi))
          + 12 * (R * (1 - Real.cos θ) + R * |Real.sin θ|) / t + 4 * (1 / 2 + R * Real.cos θ) / t)
        ≤ Real.exp 15 * Real.exp (-(R * Real.log t) / 6000000) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
      have : -(R * (1 - Real.cos θ)) * Real.log (t / (2 * Real.pi))
          = -(R * (1 - Real.cos θ) * Real.log (t / (2 * Real.pi))) := by ring
      rw [this]
      have : -(R * Real.log t) / 6000000 = -(R * Real.log t / 6000000) := by ring
      linarith
    have h2nd : 0 ≤ (4 + 12 * t) ^ 2 * Real.exp 15
        * Real.exp (-(9 / 2) * Real.log (t / (2 * Real.pi))) := by positivity
    calc ‖xiSliceProduct t ((R : ℂ) * Complex.exp ((θ : ℂ) * I))‖
        ≤ ‖xiSliceProduct t (R : ℂ)‖ * 16 * Real.exp (-(R * (1 - Real.cos θ))
            * Real.log (t / (2 * Real.pi)) + 12 * (R * (1 - Real.cos θ) + R * |Real.sin θ|) / t
            + 4 * (1 / 2 + R * Real.cos θ) / t) := hb
      _ ≤ ‖xiSliceProduct t (R : ℂ)‖ * 16 * (Real.exp 15 * Real.exp (-(R * Real.log t) / 6000000)) := by
          gcongr
      _ ≤ _ := by nlinarith
  · -- `R cos θ < 3/2`: the strip part, where the loss is polynomial in `t`
    push Not at hA
    have hgain : 9 / 2 * Real.log (t / (2 * Real.pi))
        ≤ R * (1 - Real.cos θ) * Real.log (t / (2 * Real.pi)) := by
      apply mul_le_mul_of_nonneg_right _ hlog2
      nlinarith
    have hexp : Real.exp (-(R * (1 - Real.cos θ)) * Real.log (t / (2 * Real.pi))
          + 12 * (R * (1 - Real.cos θ) + R * |Real.sin θ|) / t + 4 * (1 / 2 + R * Real.cos θ) / t)
        ≤ Real.exp 15 * Real.exp (-(9 / 2) * Real.log (t / (2 * Real.pi))) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
      have : -(R * (1 - Real.cos θ)) * Real.log (t / (2 * Real.pi))
          = -(R * (1 - Real.cos θ) * Real.log (t / (2 * Real.pi))) := by ring
      rw [this]
      linarith
    have h1st : 0 ≤ 16 * Real.exp 15 * Real.exp (-(R * Real.log t) / 6000000) := by positivity
    calc ‖xiSliceProduct t ((R : ℂ) * Complex.exp ((θ : ℂ) * I))‖
        ≤ ‖xiSliceProduct t (R : ℂ)‖ * (4 + 12 * t) ^ 2 * Real.exp (-(R * (1 - Real.cos θ))
            * Real.log (t / (2 * Real.pi)) + 12 * (R * (1 - Real.cos θ) + R * |Real.sin θ|) / t
            + 4 * (1 / 2 + R * Real.cos θ) / t) := hb
      _ ≤ ‖xiSliceProduct t (R : ℂ)‖ * (4 + 12 * t) ^ 2
            * (Real.exp 15 * Real.exp (-(9 / 2) * Real.log (t / (2 * Real.pi)))) := by
          gcongr
      _ ≤ _ := by nlinarith

theorem exp_three_halves_le_five : Real.exp (3 / 2) ≤ 5 := by
  have h1 : Real.exp (3 / 2) ^ 2 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  have h2 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h3 : Real.exp 1 ^ 3 < 25 := by
    have h0 : 0 < Real.exp 1 := Real.exp_pos 1
    nlinarith [sq_nonneg (Real.exp 1)]
  nlinarith [Real.exp_pos (3 / 2)]

/-- **Positivity of the quarter-arc integral.**  With the saddle slope `F₁` between
`(9/10) log t` and `2 log t`, the disc constant at most `log t`, `log(t/2π) ≥ (9/10) log t`, and
scales `0 < δ₀ ≤ δ ≤ 1/1000` for which the Gaussian core carries more than the three error regions
(each at most `δ₀/20` against a core of at least `(7/40) δ₀`), the integral
`∫₀^{π/2} Re S(θ) dθ` is positive.  Here `Λ = R log t`. -/
theorem quarter_integral_sliceArc_pos {t R δ₀ δ : ℝ} {k : ℕ} (ht : 10 ≤ t) (hR : 6 ≤ R)
    (hRt : R ≤ t / 2)
    (hsad : (HTGeometry.scaledLogDeriv (xiSliceProduct t) R).re = 2 * k)
    (hF₁lo : 9 / 10 * Real.log t ≤ (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re)
    (hF₁hi : (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re ≤ 2 * Real.log t)
    (hD : xiSliceDiscConstant t ≤ Real.log t)
    (hlog : 9 / 10 * Real.log t ≤ Real.log (t / (2 * Real.pi)))
    (hδ₀ : 0 < δ₀) (hδ₀δ : δ₀ ≤ δ) (hδ : δ ≤ 1 / 1000)
    (hcore : R * Real.log t * δ₀ ^ 2 ≤ 1) (hphase : 43 * (R * Real.log t) * δ ^ 3 ≤ 1 / 2)
    (hmid : 1 / 1000 * Real.exp (-(R * Real.log t) * δ ^ 2 / 8) ≤ δ₀ / 20)
    (htail1 : Real.pi / 2 * (16 * Real.exp 15 * Real.exp (-(R * Real.log t) / 6000000)) ≤ δ₀ / 20)
    (htail2 : Real.pi / 2 * ((4 + 12 * t) ^ 2 * Real.exp 15
      * Real.exp (-(9 / 2) * Real.log (t / (2 * Real.pi)))) ≤ δ₀ / 20) :
    0 < ∫ θ in (0 : ℝ)..(Real.pi / 2), (sliceArc t R k θ).re := by
  set F₁ := (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re with hF₁def
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = R * Real.log t := ⟨_, rfl⟩
  rw [← hΛ] at hcore hphase hmid
  have hR0 : 0 < R := by linarith
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have hΛ0 : 0 < Λ := by rw [hΛ]; positivity
  have hF₁0 : 0 ≤ F₁ := by linarith
  -- continuity of the integrand
  have hSc : Continuous fun θ : ℝ => (sliceArc t R k θ).re := by
    have hg := differentiable_xiSliceProduct t
    have : Continuous fun θ : ℝ => xiSliceProduct t ((R : ℂ) * Complex.exp ((θ : ℂ) * I)) :=
      hg.continuous.comp (by fun_prop)
    simp only [sliceArc, HTGeometry.saddleArc]
    fun_prop
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun θ : ℝ => (sliceArc t R k θ).re)
      MeasureTheory.volume a b := fun a b => hSc.intervalIntegrable a b
  have hpi : (1 / 1000 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  -- the phase is small on `[0, δ]`
  have hcoreθ : ∀ θ ∈ Set.Icc 0 δ,
      7 / 8 * Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 1 / 2) ≤ (sliceArc t R k θ).re := by
    intro θ hθ
    apply sliceArc_re_core (by linarith) (by linarith) hRt hsad hθ.1 (by linarith [hθ.2])
    have hθ3 : θ ^ 3 ≤ δ ^ 3 := pow_le_pow_left₀ hθ.1 hθ.2 3
    have h1 : |F₁| * R * θ ^ 3 / 6 ≤ Λ / 3 * θ ^ 3 := by
      rw [abs_of_nonneg hF₁0, hΛ]
      have := mul_le_mul_of_nonneg_right hF₁hi (mul_nonneg hR0.le (pow_nonneg hθ.1 3))
      nlinarith
    have h2 : 128 / 3 * (R * xiSliceDiscConstant t) * θ ^ 3 ≤ 128 / 3 * Λ * θ ^ 3 := by
      rw [hΛ]
      have := mul_le_mul_of_nonneg_left hD hR0.le
      have hθ3' : 0 ≤ θ ^ 3 := pow_nonneg hθ.1 3
      nlinarith
    have h3 : 43 * Λ * θ ^ 3 ≤ 43 * Λ * δ ^ 3 := by gcongr
    linarith
  -- core: `Re S ≥ 7/40` on `[0, δ₀]`
  have hI1 : 7 / 40 * δ₀ ≤ ∫ θ in (0 : ℝ)..δ₀, (sliceArc t R k θ).re := by
    have := intervalIntegral.integral_mono_on hδ₀.le
      (continuous_const.intervalIntegrable 0 δ₀) (hi 0 δ₀)
      (fun θ hθ => (show (7 / 40 : ℝ) ≤ (sliceArc t R k θ).re from by
        have hc := hcoreθ θ ⟨hθ.1, hθ.2.trans hδ₀δ⟩
        have hθ2 : θ ^ 2 ≤ δ₀ ^ 2 := pow_le_pow_left₀ hθ.1 hθ.2 2
        have hq : F₁ * R * (1 - Real.cos θ) ≤ 1 := by
          have h1 := one_sub_cos_le_half_sq θ
          have h0 : 0 ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
          calc F₁ * R * (1 - Real.cos θ) ≤ (2 * Real.log t) * R * (θ ^ 2 / 2) := by
                apply mul_le_mul (mul_le_mul_of_nonneg_right hF₁hi hR0.le) h1 h0 (by positivity)
            _ = Λ * θ ^ 2 := by rw [hΛ]; ring
            _ ≤ Λ * δ₀ ^ 2 := by gcongr
            _ ≤ 1 := hcore
        have he : 1 / 5 ≤ Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 1 / 2) := by
          have h5 := exp_three_halves_le_five
          have : Real.exp (-(3 / 2)) ≤ Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 1 / 2) :=
            Real.exp_le_exp.mpr (by linarith)
          rw [Real.exp_neg] at this
          have hpos := Real.exp_pos (3 / 2)
          calc (1 / 5 : ℝ) ≤ (Real.exp (3 / 2))⁻¹ := by
                rw [inv_eq_one_div]; exact one_div_le_one_div_of_le hpos h5
            _ ≤ _ := this
        linarith))
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
    linarith
  -- mid-core: `Re S ≥ 0` on `[δ₀, δ]`
  have hI2 : 0 ≤ ∫ θ in δ₀..δ, (sliceArc t R k θ).re :=
    intervalIntegral.integral_nonneg hδ₀δ (fun θ hθ =>
      le_trans (by positivity) (hcoreθ θ ⟨hδ₀.le.trans hθ.1, hθ.2⟩))
  -- middle: `Re S ≥ −exp(−Λδ²/8)` on `[δ, 1/1000]`
  have hI3 : -(1 / 1000 * Real.exp (-Λ * δ ^ 2 / 8)) ≤ ∫ θ in δ..(1 / 1000), (sliceArc t R k θ).re := by
    have := intervalIntegral.integral_mono_on hδ
      (continuous_const.intervalIntegrable δ (1 / 1000)) (hi δ (1 / 1000))
      (fun θ hθ => (show -Real.exp (-Λ * δ ^ 2 / 8) ≤ (sliceArc t R k θ).re from by
        have hθ0 : 0 ≤ θ := hδ₀.le.trans (hδ₀δ.trans hθ.1)
        have hn := sliceArc_norm_middle (k := k) (by linarith) (by linarith) hRt hsad hF₁lo hD
          hθ0 hθ.2
        have hre := neg_abs_le (sliceArc t R k θ).re
        have hab := Complex.abs_re_le_norm (sliceArc t R k θ)
        have hδθ : δ ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ (hδ₀.le.trans hδ₀δ) hθ.1 2
        have : Real.exp (-(R * Real.log t) * θ ^ 2 / 8) ≤ Real.exp (-Λ * δ ^ 2 / 8) := by
          apply Real.exp_le_exp.mpr; rw [hΛ]; nlinarith
        linarith))
    have hlen : (1 / 1000 - δ) * -Real.exp (-Λ * δ ^ 2 / 8) ≥ -(1 / 1000 * Real.exp (-Λ * δ ^ 2 / 8)) := by
      have hδ0 : 0 ≤ δ := hδ₀.le.trans hδ₀δ
      nlinarith [Real.exp_pos (-Λ * δ ^ 2 / 8)]
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  -- tail: `Re S ≥ −E` on `[1/1000, π/2]`
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = 16 * Real.exp 15 * Real.exp (-(R * Real.log t) / 6000000)
      + (4 + 12 * t) ^ 2 * Real.exp 15 * Real.exp (-(9 / 2) * Real.log (t / (2 * Real.pi))) :=
    ⟨_, rfl⟩
  have hI4 : -(Real.pi / 2 * E) ≤ ∫ θ in (1 / 1000)..(Real.pi / 2), (sliceArc t R k θ).re := by
    have := intervalIntegral.integral_mono_on hpi
      (continuous_const.intervalIntegrable (1 / 1000) (Real.pi / 2)) (hi (1 / 1000) (Real.pi / 2))
      (fun θ hθ => (show -E ≤ (sliceArc t R k θ).re from by
        have hn := sliceArc_norm_tail k ht hR hRt hlog hθ.1 hθ.2
        rw [← hE] at hn
        have hre := neg_abs_le (sliceArc t R k θ).re
        have hab := Complex.abs_re_le_norm (sliceArc t R k θ)
        linarith))
    have hE0 : 0 ≤ E := by rw [hE]; positivity
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    nlinarith [Real.pi_pos]
  -- assemble
  have hsplit : ∫ θ in (0 : ℝ)..(Real.pi / 2), (sliceArc t R k θ).re
      = (∫ θ in (0 : ℝ)..δ₀, (sliceArc t R k θ).re) + (∫ θ in δ₀..δ, (sliceArc t R k θ).re)
        + (∫ θ in δ..(1 / 1000), (sliceArc t R k θ).re)
        + ∫ θ in (1 / 1000)..(Real.pi / 2), (sliceArc t R k θ).re := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hi 0 δ₀) (hi δ₀ δ),
      intervalIntegral.integral_add_adjacent_intervals (hi 0 δ) (hi δ (1 / 1000)),
      intervalIntegral.integral_add_adjacent_intervals (hi 0 (1 / 1000)) (hi (1 / 1000) (Real.pi / 2))]
  rw [hsplit]
  have hmid' : 1 / 1000 * Real.exp (-Λ * δ ^ 2 / 8) ≤ δ₀ / 20 := hmid
  have htail : Real.pi / 2 * E ≤ δ₀ / 20 + δ₀ / 20 := by
    rw [hE, mul_add]; exact add_le_add htail1 htail2
  linarith only [hI1, hI2, hI3, hI4, hmid', htail, hδ₀]

/-! ## Choice of the scales -/

theorem self_mul_rpow_eq {Λ : ℝ} (h : 0 < Λ) (a : ℝ) : Λ * Λ ^ a = Λ ^ (1 + a) := by
  rw [Real.rpow_add h, Real.rpow_one]

theorem mul_rpow_neg_half_sq {Λ : ℝ} (h : 0 < Λ) : Λ * (Λ ^ (-(1 / 2) : ℝ)) ^ 2 = 1 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul h.le, self_mul_rpow_eq h]; norm_num

theorem mul_rpow_neg_two_fifths_sq {Λ : ℝ} (h : 0 < Λ) :
    Λ * (Λ ^ (-(2 / 5) : ℝ)) ^ 2 = Λ ^ (1 / 5 : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul h.le, self_mul_rpow_eq h]; norm_num

theorem mul_rpow_neg_two_fifths_cube {Λ : ℝ} (h : 0 < Λ) :
    Λ * (Λ ^ (-(2 / 5) : ℝ)) ^ 3 = Λ ^ (-(1 / 5) : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul h.le, self_mul_rpow_eq h]; norm_num

theorem rpow_half_mul_rpow_neg_half_eq_one {Λ : ℝ} (h : 0 < Λ) :
    Λ ^ (1 / 2 : ℝ) * Λ ^ (-(1 / 2) : ℝ) = 1 := by
  rw [← Real.rpow_add h]; norm_num

theorem tendsto_rpow_half_mul_exp_neg_fifth_root :
    Filter.Tendsto (fun Λ : ℝ => Λ ^ (1 / 2 : ℝ) * Real.exp (-(Λ ^ (1 / 5 : ℝ)) / 8))
      Filter.atTop (nhds 0) := by
  have h1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (5 / 2) (1 / 8) (by norm_num)).comp
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5))
  refine h1.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 0] with Λ hΛ
  simp only [Function.comp]
  rw [← Real.rpow_mul hΛ]
  congr 1
  · norm_num
  · congr 1; ring

/-- The polynomial loss of the strip part of the tail is beaten by `t^{−9/2}`:
`(π/2)(4+12t)² e^{15} (t/2π)^{−9/2} ≤ 1/(20t)` once `log t` exceeds an explicit constant. -/
def stripTailLogThreshold : ℝ :=
  2 / 3 * Real.log (20 * (Real.pi / 2 * 256 * Real.exp 15
    * Real.exp (9 / 2 * Real.log (2 * Real.pi))))

theorem strip_tail_le {t : ℝ} (ht : 1 ≤ t) (hlog : stripTailLogThreshold ≤ Real.log t) :
    Real.pi / 2 * ((4 + 12 * t) ^ 2 * Real.exp 15
      * Real.exp (-(9 / 2) * Real.log (t / (2 * Real.pi)))) ≤ 1 / t / 20 := by
  have ht0 : 0 < t := by linarith
  set K₀ := Real.pi / 2 * 256 * Real.exp 15 * Real.exp (9 / 2 * Real.log (2 * Real.pi)) with hK₀
  have hK₀pos : 0 < K₀ := by positivity
  have hlogdiv : Real.log (t / (2 * Real.pi)) = Real.log t - Real.log (2 * Real.pi) :=
    Real.log_div ht0.ne' (by positivity)
  have hsq : (4 + 12 * t) ^ 2 ≤ 256 * Real.exp (2 * Real.log t) := by
    rw [show 2 * Real.log t = (2 : ℕ) * Real.log t by norm_num, Real.exp_nat_mul, Real.exp_log ht0]
    nlinarith
  have hinv : 1 / t = Real.exp (-Real.log t) := by rw [Real.exp_neg, Real.exp_log ht0, one_div]
  have hK : 20 * K₀ ≤ Real.exp (3 / 2 * Real.log t) := by
    rw [← Real.exp_log (by positivity : 0 < 20 * K₀)]
    apply Real.exp_le_exp.mpr
    unfold stripTailLogThreshold at hlog
    rw [← hK₀] at hlog
    linarith
  calc Real.pi / 2 * ((4 + 12 * t) ^ 2 * Real.exp 15
        * Real.exp (-(9 / 2) * Real.log (t / (2 * Real.pi))))
      ≤ Real.pi / 2 * ((256 * Real.exp (2 * Real.log t)) * Real.exp 15
        * Real.exp (-(9 / 2) * Real.log (t / (2 * Real.pi)))) := by gcongr
    _ = K₀ * Real.exp (-(5 / 2) * Real.log t) := by
        rw [hK₀, hlogdiv]
        have : ∀ a b c d : ℝ, Real.exp a * Real.exp b * Real.exp c = Real.exp (a + b + c) := by
          intros; rw [Real.exp_add, Real.exp_add]
        have e1 : Real.exp (2 * Real.log t) * Real.exp (-(9 / 2) * (Real.log t - Real.log (2 * Real.pi)))
            = Real.exp (9 / 2 * Real.log (2 * Real.pi)) * Real.exp (-(5 / 2) * Real.log t) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        calc Real.pi / 2 * (256 * Real.exp (2 * Real.log t) * Real.exp 15
              * Real.exp (-(9 / 2) * (Real.log t - Real.log (2 * Real.pi))))
            = Real.pi / 2 * 256 * Real.exp 15 * (Real.exp (2 * Real.log t)
              * Real.exp (-(9 / 2) * (Real.log t - Real.log (2 * Real.pi)))) := by ring
          _ = _ := by rw [e1]; ring
    _ ≤ 1 / t / 20 := by
        rw [hinv]
        have e2 : Real.exp (-Real.log t) = Real.exp (3 / 2 * Real.log t)
            * Real.exp (-(5 / 2) * Real.log t) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [e2]
        have hpos := Real.exp_pos (-(5 / 2) * Real.log t)
        nlinarith

open scoped ComplexOrder in
/-- **High-order positivity of the slice coefficients.**  There are `t₀` and `κ` such that for
every height `t ≥ t₀` and every `k` with `κ log t ≤ k ≤ (t log t)/8`, the Taylor coefficient
`c_{2k}(t)` of `g_t(x) = ξ(½+x+it) ξ(½−x+it)` is strictly positive.

The coefficient is `(2 g_t(R)/(π R^{2k})) ∫₀^{π/2} Re S`, with `R` the saddle radius
(`R g_t'(R)/g_t(R) = 2k`).  The integral is positive: on `θ ≤ Λ^{−1/2}` (`Λ = R log t`) the saddle
bound gives `Re S ≥ 7/40`; up to `Λ^{−2/5}` it keeps `Re S ≥ 0`; up to `1/1000` the Gaussian decay
`|S| ≤ exp(−Λθ²/8)` applies; beyond that the circle-decay law of `|g_t|` does.  Each error region is
at most `Λ^{−1/2}/20`. -/
theorem exists_xiSliceCoeff_pos_window :
    ∃ t₀ κ : ℝ, ∀ t : ℝ, t₀ ≤ t → ∀ k : ℕ, κ * Real.log t ≤ k → (k : ℝ) ≤ t * Real.log t / 8 →
      0 < xiSliceCoeff t (2 * k) := by
  obtain ⟨C, hC⟩ : ∃ C, C = xiLogDerivStirlingConstant := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = Real.log 4 + Real.pi + 4 * C := ⟨_, rfl⟩
  have hC0 : 0 < C := hC ▸ xiLogDerivStirlingConstant_pos
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hpi0 := Real.pi_pos
  have hB0 : 0 < B := by rw [hB]; positivity
  -- thresholds in `Λ`
  have e1 := (tendsto_order.1 tendsto_rpow_half_mul_exp_neg_fifth_root).2 50 (by norm_num)
  have e2 := (tendsto_order.1 (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) (1 / 6000000)
    (by norm_num))).2 (1 / (20 * (Real.pi / 2 * (16 * Real.exp 15)))) (by positivity)
  have e3 := (tendsto_order.1 (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 5))).2
    (1 / 1000) (by norm_num)
  have e4 := (tendsto_order.1 (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 5))).2
    (1 / 86) (by norm_num)
  obtain ⟨Λ₀, hΛ₀⟩ := Filter.eventually_atTop.mp (e1.and (e2.and (e3.and e4)))
  -- threshold in `t`
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl32 : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hl2pi : 0 < Real.log (2 * Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])
  obtain ⟨L, hL⟩ : ∃ L, L = 10 * (Real.log 2 + Real.log (3 / 2) + Real.pi / 2 + 2 * C + 2 * B
    + Real.log (2 * Real.pi)) + |stripTailLogThreshold| + 1 := ⟨_, rfl⟩
  have hLpos : 0 < L := by rw [hL]; positivity
  refine ⟨max 10 (Real.exp L), max 6 (max Λ₀ 1 / L), ?_⟩
  intro t ht k hk hkt
  have ht10 : 10 ≤ t := le_trans (le_max_left _ _) ht
  have ht0 : 0 < t := by linarith
  have hlogL : L ≤ Real.log t := by
    rw [← Real.log_exp L]; exact Real.log_le_log (Real.exp_pos L) (le_trans (le_max_right _ _) ht)
  have habs := abs_nonneg stripTailLogThreshold
  have hS : Real.log 2 + Real.log (3 / 2) + Real.pi / 2 + 2 * C + 2 * B + Real.log (2 * Real.pi)
      ≤ Real.log t / 10 := by
    rw [hL] at hlogL; linarith only [hlogL, habs]
  have hlogt : 0 < Real.log t := by linarith only [hS, hl2, hl32, hl2pi, hpi0, hC0, hB0]
  have hκ6 : 6 ≤ max 6 (max Λ₀ 1 / L) := le_max_left _ _
  have hk6 : 6 * Real.log t ≤ k := le_trans (mul_le_mul_of_nonneg_right hκ6 hlogt.le) hk
  -- the saddle radius
  have hlo : 5 * (Real.log t + 2 * xiLogDerivStirlingConstant) ≤ 2 * (k : ℝ) := by
    rw [← hC]; linarith only [hk6, hS, hl2, hl32, hl2pi, hpi0, hC0, hB0]
  have hlog2 : Real.log (t / 2) = Real.log t - Real.log 2 := Real.log_div ht0.ne' (by norm_num)
  have hhi : 2 * (k : ℝ) ≤ t / 2 * (Real.log (t / 2) - 2 * xiLogDerivStirlingConstant) := by
    rw [hlog2, ← hC]
    have h1 : Real.log t / 2 ≤ Real.log t - Real.log 2 - 2 * C := by
      linarith only [hS, hlogt, hC0, hB0, hl2, hl32, hl2pi, hpi0]
    have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ t / 2)
    linarith only [h2, hkt]
  obtain ⟨R, ⟨hR5, hRt⟩, hsad⟩ := exists_saddle_radius ht10 hlo hhi
  have hR0 : 0 < R := by linarith
  -- `R ≥ k / log t`
  obtain ⟨-, hLlo, hLhi⟩ := xiSliceLogDeriv_real_bounds (t := t) (R := R) (by linarith)
    (by linarith) hRt
  rw [← hC] at hLlo hLhi
  have hsad2 := hsad
  rw [re_scaledLogDeriv_xiSliceProduct_ofReal (by linarith)] at hsad2
  have hL2 : (xiSliceLogDeriv t R).re ≤ 2 * Real.log t := by
    linarith only [hLhi, hS, hlogt, hC0, hB0, hl2, hl32, hl2pi, hpi0]
  have hRk : (k : ℝ) ≤ R * Real.log t := by
    have := mul_le_mul_of_nonneg_left hL2 hR0.le
    linarith only [this, hsad2]
  have hRκ : max 6 (max Λ₀ 1 / L) * Real.log t ≤ R * Real.log t := le_trans hk hRk
  have hR6 : 6 ≤ R :=
    le_of_mul_le_mul_right (le_trans (mul_le_mul_of_nonneg_right hκ6 hlogt.le) hRκ) hlogt
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = R * Real.log t := ⟨_, rfl⟩
  have hΛ0 : 0 < Λ := by rw [hΛ]; positivity
  have hΛbig : max Λ₀ 1 ≤ Λ := by
    have h1 : max Λ₀ 1 / L * L ≤ max 6 (max Λ₀ 1 / L) * Real.log t :=
      mul_le_mul (le_max_right _ _) hlogL hLpos.le (by positivity)
    rw [div_mul_cancel₀ _ hLpos.ne'] at h1
    rw [hΛ]; linarith only [h1, hRκ]
  have hΛ1 : 1 ≤ Λ := le_trans (le_max_right _ _) hΛbig
  obtain ⟨hE1, hE2, hE3, hE4⟩ := hΛ₀ Λ (le_trans (le_max_left _ _) hΛbig)
  -- slope, disc constant, logarithms
  obtain ⟨hF₁lo, hF₁hi⟩ := xiSlice_saddleSlope_bounds (t := t) (R := R) (by linarith)
    (by linarith) hRt
  rw [← hC] at hF₁lo hF₁hi
  rw [← hB] at hF₁lo hF₁hi
  have hF₁lo' : 9 / 10 * Real.log t
      ≤ (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re := by
    rw [hlog2] at hF₁lo; linarith only [hF₁lo, hS, hlogt, hC0, hB0, hl2, hl32, hl2pi, hpi0]
  have hF₁hi' : (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re
      ≤ 2 * Real.log t := by
    linarith only [hF₁hi, hS, hlogt, hC0, hB0, hl2, hl32, hl2pi, hpi0]
  have hD : xiSliceDiscConstant t ≤ Real.log t := by
    unfold xiSliceDiscConstant
    have e : Real.log (3 * t / 2) = Real.log (3 / 2) + Real.log t := by
      rw [show 3 * t / 2 = 3 / 2 * t by ring, Real.log_mul (by norm_num) ht0.ne']
    rw [e, ← hC, ← hB]
    linarith only [hS, hlogt, hC0, hB0, hl2, hl32, hl2pi, hpi0]
  have hlogpi : 9 / 10 * Real.log t ≤ Real.log (t / (2 * Real.pi)) := by
    rw [Real.log_div ht0.ne' (by positivity)]
    linarith only [hS, hlogt, hC0, hB0, hl2, hl32, hl2pi, hpi0]
  -- the scales
  obtain ⟨δ₀, hδ₀⟩ : ∃ δ₀, δ₀ = Λ ^ (-(1 / 2) : ℝ) := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = Λ ^ (-(2 / 5) : ℝ) := ⟨_, rfl⟩
  have hδ₀pos : 0 < δ₀ := hδ₀ ▸ Real.rpow_pos_of_pos hΛ0 _
  have hδ₀δ : δ₀ ≤ δ := by
    rw [hδ₀, hδ]; exact Real.rpow_le_rpow_of_exponent_le hΛ1 (by norm_num)
  have hδ1000 : δ ≤ 1 / 1000 := hδ ▸ hE3.le
  have hcore : Λ * δ₀ ^ 2 ≤ 1 := by rw [hδ₀]; exact (mul_rpow_neg_half_sq hΛ0).le
  have hphase : 43 * Λ * δ ^ 3 ≤ 1 / 2 := by
    have := mul_rpow_neg_two_fifths_cube hΛ0
    rw [hδ, mul_assoc, this]; linarith only [hE4]
  have hhalf : Λ ^ (1 / 2 : ℝ) * δ₀ = 1 := by rw [hδ₀]; exact rpow_half_mul_rpow_neg_half_eq_one hΛ0
  have hmid : 1 / 1000 * Real.exp (-Λ * δ ^ 2 / 8) ≤ δ₀ / 20 := by
    have e : -Λ * δ ^ 2 / 8 = -(Λ ^ (1 / 5 : ℝ)) / 8 := by
      rw [hδ, ← mul_rpow_neg_two_fifths_sq hΛ0]; ring
    rw [e]
    have h1 : Real.exp (-(Λ ^ (1 / 5 : ℝ)) / 8) ≤ 50 * δ₀ := by
      calc Real.exp (-(Λ ^ (1 / 5 : ℝ)) / 8)
          = Λ ^ (1 / 2 : ℝ) * Real.exp (-(Λ ^ (1 / 5 : ℝ)) / 8) * δ₀ := by
            rw [mul_comm (Λ ^ (1 / 2 : ℝ)), mul_assoc, hhalf, mul_one]
        _ ≤ 50 * δ₀ := by gcongr
    linarith only [h1]
  have htail1 : Real.pi / 2 * (16 * Real.exp 15 * Real.exp (-Λ / 6000000)) ≤ δ₀ / 20 := by
    have e : -Λ / 6000000 = -(1 / 6000000) * Λ := by ring
    rw [e]
    have hK : 0 < Real.pi / 2 * (16 * Real.exp 15) := by positivity
    have h1 : Real.exp (-(1 / 6000000) * Λ)
        ≤ 1 / (20 * (Real.pi / 2 * (16 * Real.exp 15))) * δ₀ := by
      calc Real.exp (-(1 / 6000000) * Λ)
          = Λ ^ (1 / 2 : ℝ) * Real.exp (-(1 / 6000000) * Λ) * δ₀ := by
            rw [mul_comm (Λ ^ (1 / 2 : ℝ)), mul_assoc, hhalf, mul_one]
        _ ≤ 1 / (20 * (Real.pi / 2 * (16 * Real.exp 15))) * δ₀ := by gcongr
    calc Real.pi / 2 * (16 * Real.exp 15 * Real.exp (-(1 / 6000000) * Λ))
        = (Real.pi / 2 * (16 * Real.exp 15)) * Real.exp (-(1 / 6000000) * Λ) := by ring
      _ ≤ (Real.pi / 2 * (16 * Real.exp 15))
          * (1 / (20 * (Real.pi / 2 * (16 * Real.exp 15))) * δ₀) := by gcongr
      _ = δ₀ / 20 := by field_simp
  have htail2 : Real.pi / 2 * ((4 + 12 * t) ^ 2 * Real.exp 15
      * Real.exp (-(9 / 2) * Real.log (t / (2 * Real.pi)))) ≤ δ₀ / 20 := by
    have h1 := strip_tail_le (t := t) (by linarith)
      (by have := le_abs_self stripTailLogThreshold; rw [hL] at hlogL; linarith only [this, hlogL,
        hl2, hl32, hl2pi, hpi0, hC0, hB0])
    have h2 : 1 / t ≤ δ₀ := by
      have hΛt : Λ ≤ t ^ 2 := by
        have hlt := Real.log_le_sub_one_of_pos ht0
        have := mul_le_mul hRt hlt hlogt.le (by linarith : (0 : ℝ) ≤ t / 2)
        rw [hΛ]; nlinarith only [this, ht10]
      have := Real.rpow_le_rpow_of_nonpos hΛ0 hΛt (by norm_num : (-(1 / 2) : ℝ) ≤ 0)
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le] at this
      norm_num at this
      rw [Real.rpow_neg_one] at this
      rw [one_div, hδ₀]; exact this
    have h3 : 1 / t / 20 ≤ δ₀ / 20 := by linarith only [h2]
    exact h1.trans h3
  subst hΛ
  have hpos := quarter_integral_sliceArc_pos (k := k) ht10 hR6 hRt hsad hF₁lo' hF₁hi' hD hlogpi
    hδ₀pos hδ₀δ hδ1000 hcore (by linarith only [hphase]) hmid htail1 htail2
  -- the coefficient
  rw [xiSliceCoeff_two_mul_eq_quarter t k (by linarith : (1 : ℝ) / 2 < R), Complex.zero_lt_real]
  have hxi : 0 < ‖xi (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ :=
    norm_pos_iff.mpr (xi_ne_zero_of_one_lt_re (by simp; linarith))
  have hfac : 0 < 2 * ‖xi (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 / (Real.pi * R ^ (2 * k)) := by
    positivity
  exact mul_pos hfac hpos

end

end RHTower
