import GaloisForLFunctions.HTGeometry.BesselTestFunctionSineTransform

/-!
# Size of the sine transform and of the odd Bessel tail

For a test function `φ` supported in `[a, b]`, `a > 0`, with `ψ = φ/y`, sine transform `S` and odd
Bessel series `P(x) = ∑_k (-1)^k φ̃(2k+1) x^{2k+1}`:

* `|S(u)| ≤ |u| ‖φ‖₁` (`norm_sineTransform_le_mul`) and, by one integration by parts,
  `|S(u)| ≤ ‖ψ'‖₁ / |u|` (`norm_sineTransform_le_div`);
* `φ̃(2k+1) = (2/π) ∫_0^{π/2} sin((2k+1)θ) S(sin θ) dθ` (`besselCoeff_odd_eq_integral`), hence for
  `0 ≤ x < 1`
  `P(x) = (2/π) ∫_0^{π/2} S(sin θ) x(1−x²) sin θ / (1 + 2x² cos 2θ + x⁴) dθ`
  (`oddSeries_eq_integral`) and `|P(x)| ≤ ‖ψ'‖₁ x/(1−x²)` (`norm_oddSeries_le`).
  At `x = e^{−w}` this is `‖ψ'‖₁/(2 sinh w)`.
-/

open MeasureTheory Set Filter Topology Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace BesselTestFunction

variable (T : BesselTestFunction)

theorem continuous_φ : Continuous T.φ := T.smooth.continuous

theorem hasCompactSupport_φ : HasCompactSupport T.φ :=
  HasCompactSupport.intro isCompact_Icc fun y hy => T.vanish y hy

theorem integrable_φ : Integrable T.φ := T.continuous_φ.integrable_of_hasCompactSupport T.hasCompactSupport_φ

theorem ψ_mul_self (y : ℝ) : T.ψ y * y = T.φ y := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [T.ψ_eq_zero_of_nonpos le_rfl, zero_mul, T.vanish 0 fun h => by linarith [h.1, T.pos]]
  · rw [ψ, div_mul_cancel₀]; exact_mod_cast hy

/-- **`|S(u)| ≤ |u| ‖φ‖₁`.** -/
theorem norm_sineTransform_le_mul (u : ℝ) : ‖T.sineTransform u‖ ≤ |u| * ∫ y, ‖T.φ y‖ := by
  rw [sineTransform, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (T.integrable_φ.norm.const_mul _) (Eventually.of_forall fun y => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := Real.abs_sin_le_abs (x := y * u)
  rw [abs_mul] at h1
  calc ‖T.ψ y‖ * |Real.sin (y * u)| ≤ ‖T.ψ y‖ * (|y| * |u|) := by gcongr
    _ = |u| * (‖T.ψ y‖ * |y|) := by ring
    _ = |u| * ‖T.φ y‖ := by
        rw [← T.ψ_mul_self y, norm_mul, Complex.norm_real, Real.norm_eq_abs]

theorem continuous_deriv_ψ : Continuous (deriv T.ψ) :=
  T.contDiff_ψ.continuous_deriv (by simp)

theorem integrable_deriv_ψ : Integrable (deriv T.ψ) :=
  T.continuous_deriv_ψ.integrable_of_hasCompactSupport T.hasCompactSupport_ψ.deriv

/-- **`|S(u)| ≤ ‖ψ'‖₁ / |u|`**, by one integration by parts. -/
theorem norm_sineTransform_le_div {u : ℝ} (hu : u ≠ 0) :
    ‖T.sineTransform u‖ ≤ (∫ y, ‖deriv T.ψ y‖) / |u| := by
  have hψd : ∀ y, HasDerivAt T.ψ (deriv T.ψ y) y := fun y =>
    (T.contDiff_ψ.differentiable (by simp) y).hasDerivAt
  have hv : ∀ y : ℝ, HasDerivAt (fun y : ℝ => ((-Real.cos (y * u) / u : ℝ) : ℂ))
      ((Real.sin (y * u) : ℝ) : ℂ) y := fun y => by
    have h := ((((hasDerivAt_id y).mul_const u).cos).neg.div_const u).ofReal_comp
    refine h.congr_deriv ?_
    simp only [id]
    field_simp
  have hc : Continuous fun y : ℝ => ((-Real.cos (y * u) / u : ℝ) : ℂ) := by fun_prop
  have hcs : Continuous fun y : ℝ => ((Real.sin (y * u) : ℝ) : ℂ) := by fun_prop
  have hbd : ∀ y : ℝ, ‖((-Real.cos (y * u) / u : ℝ) : ℂ)‖ ≤ 1 / |u| := fun y => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg]
    gcongr; exact Real.abs_cos_le_one _
  have hbs : ∀ y : ℝ, ‖((Real.sin (y * u) : ℝ) : ℂ)‖ ≤ 1 := fun y => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_sin_le_one _
  have h1 : Integrable (T.ψ * fun y : ℝ => ((Real.sin (y * u) : ℝ) : ℂ)) :=
    T.integrable_ψ.mul_bdd hcs.aestronglyMeasurable (Eventually.of_forall hbs)
  have h2 : Integrable (deriv T.ψ * fun y : ℝ => ((-Real.cos (y * u) / u : ℝ) : ℂ)) :=
    T.integrable_deriv_ψ.mul_bdd hc.aestronglyMeasurable (Eventually.of_forall hbd)
  have h3 : Integrable (T.ψ * fun y : ℝ => ((-Real.cos (y * u) / u : ℝ) : ℂ)) :=
    T.integrable_ψ.mul_bdd hc.aestronglyMeasurable (Eventually.of_forall hbd)
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable (fun y _ => hψd y) (fun y _ => hv y) h1 h2 h3
  rw [sineTransform]
  rw [hibp, norm_neg]
  calc ‖∫ y, deriv T.ψ y * ((-Real.cos (y * u) / u : ℝ) : ℂ)‖
      ≤ ∫ y, ‖deriv T.ψ y‖ * (1 / |u|) := norm_integral_le_of_norm_le
        (T.integrable_deriv_ψ.norm.mul_const _) (Eventually.of_forall fun y => by
          rw [norm_mul]; gcongr; exact hbd y)
    _ = _ := by rw [integral_mul_const]; ring

theorem norm_sineTransform_mul_le (u : ℝ) : ‖T.sineTransform u‖ * |u| ≤ ∫ y, ‖deriv T.ψ y‖ := by
  rcases eq_or_ne u 0 with rfl | hu
  · rw [abs_zero, mul_zero]; exact integral_nonneg fun _ => norm_nonneg _
  · have := T.norm_sineTransform_le_div hu
    rwa [le_div_iff₀ (abs_pos.2 hu)] at this

/-! ## The angular representation of the odd tail -/

/-- **`φ̃(2k+1) = (2/π) ∫_0^{π/2} sin((2k+1)θ) S(sin θ) dθ`.** -/
theorem besselCoeff_odd_eq_integral (k : ℕ) :
    T.besselCoeff (2 * k + 1) = (2 / Real.pi : ℂ) *
      ∫ θ in (0 : ℝ)..Real.pi / 2, (Real.sin ((2 * k + 1 : ℕ) * θ) : ℂ) * T.sineTransform (Real.sin θ) := by
  rw [besselCoeff]
  have hJ : ∀ y : ℝ, (besselJ (2 * k + 1) y : ℂ) * T.ψ y = (2 / Real.pi : ℂ) *
      ∫ θ in (0 : ℝ)..Real.pi / 2, T.ψ y * ((Real.sin ((2 * k + 1 : ℕ) * θ) * Real.sin (y * Real.sin θ) : ℝ) : ℂ) :=
    fun y => by
      rw [besselJ_odd_eq_integral, intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
      push_cast; ring
  simp_rw [hJ]
  rw [integral_const_mul]
  congr 1
  have hπ2 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  simp_rw [intervalIntegral.integral_of_le hπ2]
  have hint : Integrable (Function.uncurry fun (y θ : ℝ) =>
      T.ψ y * ((Real.sin ((2 * k + 1 : ℕ) * θ) * Real.sin (y * Real.sin θ) : ℝ) : ℂ))
      ((volume : Measure ℝ).prod (volume.restrict (Ioc 0 (Real.pi / 2)))) := by
    refine (T.integrable_ψ.norm.mul_prod (integrable_const (1 : ℝ))).mono' ?_
      (Eventually.of_forall fun z => ?_)
    · exact Continuous.aestronglyMeasurable ((T.continuous_ψ.comp continuous_fst).mul (by fun_prop))
    · simp only [Function.uncurry]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, mul_one]
      have h1 := Real.abs_sin_le_one ((2 * k + 1 : ℕ) * z.2)
      have h2 := Real.abs_sin_le_one (z.1 * Real.sin z.2)
      calc ‖T.ψ z.1‖ * (|Real.sin ((2 * k + 1 : ℕ) * z.2)| * |Real.sin (z.1 * Real.sin z.2)|)
          ≤ ‖T.ψ z.1‖ * (1 * 1) := by gcongr
        _ = _ := by ring
  rw [integral_integral_swap hint]
  congr 1; funext θ
  rw [sineTransform, ← integral_const_mul]
  congr 1; funext y
  push_cast; ring

/-- `Σ_k (-1)^k x^{2k+1} sin((2k+1)θ) = x(1−x²) sin θ / (1 + 2x² cos 2θ + x⁴)` for `0 ≤ x < 1`. -/
theorem hasSum_odd_sin_series {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) (θ : ℝ) :
    HasSum (fun k : ℕ => (-1) ^ k * x ^ (2 * k + 1) * Real.sin ((2 * k + 1 : ℕ) * θ))
      (x * (1 - x ^ 2) * Real.sin θ / (1 + 2 * x ^ 2 * Real.cos (2 * θ) + x ^ 4)) := by
  set z : ℂ := (x : ℂ) * Complex.exp (θ * Complex.I)
  have hz : ‖z‖ = x := by
    simp only [z, norm_mul, Complex.norm_real, Real.norm_of_nonneg hx0, Complex.norm_exp_ofReal_mul_I,
      mul_one]
  have hq : ‖-z ^ 2‖ < 1 := by rw [norm_neg, norm_pow, hz]; nlinarith
  have hg := (hasSum_geometric_of_norm_lt_one hq).mul_left z
  have hpow : ∀ k : ℕ, z * (-z ^ 2) ^ k = (-1) ^ k * z ^ (2 * k + 1) := fun k => by
    rw [neg_pow, ← pow_mul]; ring
  simp_rw [hpow] at hg
  have hzn : ∀ n : ℕ, z ^ n = ((x ^ n * Real.cos (n * θ) : ℝ) : ℂ) + ((x ^ n * Real.sin (n * θ) : ℝ) : ℂ) * Complex.I :=
    fun n => by
      simp only [z]
      rw [mul_pow, ← Complex.exp_nat_mul, show (n : ℂ) * (θ * Complex.I) = ((n * θ : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      push_cast; ring
  have him : ∀ k : ℕ, ((-1) ^ k * z ^ (2 * k + 1)).im = (-1) ^ k * x ^ (2 * k + 1) *
      Real.sin ((2 * k + 1 : ℕ) * θ) := fun k => by
    rw [hzn, show ((-1 : ℂ)) ^ k = (((-1 : ℝ) ^ k : ℝ) : ℂ) by push_cast; ring]
    simp only [Complex.mul_im, Complex.add_im, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.I_re, Complex.I_im]
    ring
  have h1 := Complex.hasSum_im hg
  simp_rw [him] at h1
  convert h1 using 1
  have hw : 1 - -z ^ 2 = (((1 + x ^ 2 * Real.cos (2 * θ)) : ℝ) : ℂ) + ((x ^ 2 * Real.sin (2 * θ) : ℝ) : ℂ) * Complex.I := by
    rw [hzn 2]; push_cast; ring
  have hz1 : z = ((x * Real.cos θ : ℝ) : ℂ) + ((x * Real.sin θ : ℝ) : ℂ) * Complex.I := by
    have := hzn 1
    simp only [pow_one, Nat.cast_one, one_mul] at this
    exact this
  rw [hw, ← div_eq_mul_inv, hz1]
  have him_div : ∀ a b p q : ℝ, (((a : ℂ) + (b : ℂ) * Complex.I) / ((p : ℂ) + (q : ℂ) * Complex.I)).im =
      (b * p - a * q) / (p ^ 2 + q ^ 2) := fun a b p q => by
    rw [Complex.div_im]
    simp [Complex.normSq_apply]
    ring
  rw [him_div]
  have hsin2 := Real.sin_two_mul θ
  have hcos2 := Real.cos_two_mul θ
  have hpy := Real.sin_sq_add_cos_sq θ
  have hD : (1 + x ^ 2 * Real.cos (2 * θ)) ^ 2 + (x ^ 2 * Real.sin (2 * θ)) ^ 2 =
      1 + 2 * x ^ 2 * Real.cos (2 * θ) + x ^ 4 := by
    rw [hsin2, hcos2]
    linear_combination 4 * x ^ 4 * Real.cos θ ^ 2 * hpy
  have hN : x * Real.sin θ * (1 + x ^ 2 * Real.cos (2 * θ)) - x * Real.cos θ * (x ^ 2 * Real.sin (2 * θ)) =
      x * (1 - x ^ 2) * Real.sin θ := by
    rw [hsin2, hcos2]; ring
  rw [hD, hN]

theorem sinTail_kernel_denom_ge {x : ℝ} (θ : ℝ) :
    (1 - x ^ 2) ^ 2 ≤ 1 + 2 * x ^ 2 * Real.cos (2 * θ) + x ^ 4 := by
  have h := Real.neg_one_le_cos (2 * θ)
  have : -(2 * x ^ 2) ≤ 2 * x ^ 2 * Real.cos (2 * θ) := by nlinarith [sq_nonneg x]
  nlinarith

/-- **`P(x) = (2/π) ∫_0^{π/2} S(sin θ) x(1−x²) sin θ/(1 + 2x² cos 2θ + x⁴) dθ`** for `0 ≤ x < 1`. -/
theorem oddSeries_eq_integral {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    T.oddSeries x = (2 / Real.pi : ℂ) * ∫ θ in (0 : ℝ)..Real.pi / 2, T.sineTransform (Real.sin θ) *
      ((x * (1 - x ^ 2) * Real.sin θ / (1 + 2 * x ^ 2 * Real.cos (2 * θ) + x ^ 4) : ℝ) : ℂ) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set M := ∫ y, ‖T.φ y‖
  have hS : ∀ θ : ℝ, ‖T.sineTransform (Real.sin θ)‖ ≤ M := fun θ =>
    (T.norm_sineTransform_le_mul _).trans (by
      have := Real.abs_sin_le_one θ
      have hM : 0 ≤ M := integral_nonneg fun _ => norm_nonneg _
      nlinarith)
  have hH := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := 0) (b := Real.pi / 2)
    (F := fun k θ => (((-1) ^ k * x ^ (2 * k + 1) * Real.sin ((2 * k + 1 : ℕ) * θ) : ℝ) : ℂ) *
      T.sineTransform (Real.sin θ))
    (f := fun θ => T.sineTransform (Real.sin θ) *
      ((x * (1 - x ^ 2) * Real.sin θ / (1 + 2 * x ^ 2 * Real.cos (2 * θ) + x ^ 4) : ℝ) : ℂ))
    (fun k _ => x ^ (2 * k + 1) * M)
    (fun k => Continuous.aestronglyMeasurable (by
      have := T.continuous_sineTransform
      fun_prop))
    (fun k => Eventually.of_forall fun θ _ => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_neg, abs_one,
        one_pow, one_mul, abs_pow, abs_of_nonneg hx0]
      have h1 := Real.abs_sin_le_one ((2 * k + 1 : ℕ) * θ)
      calc x ^ (2 * k + 1) * |Real.sin ((2 * k + 1 : ℕ) * θ)| * ‖T.sineTransform (Real.sin θ)‖
          ≤ x ^ (2 * k + 1) * 1 * M := by gcongr; exact hS θ
        _ = _ := by ring)
    (Eventually.of_forall fun _ _ => by
      have hg := (summable_geometric_of_lt_one (by positivity : 0 ≤ x ^ 2) (by nlinarith)).mul_left x
      refine (hg.mul_right M).congr fun k => ?_
      rw [pow_succ, pow_mul]; ring)
    intervalIntegrable_const
    (Eventually.of_forall fun θ _ => by
      have h := (hasSum_odd_sin_series hx0 hx θ)
      have h' := (Complex.hasSum_ofReal.2 h).mul_right (T.sineTransform (Real.sin θ))
      convert h' using 1; ring)
  have hval : ∀ k : ℕ, ∫ θ in (0 : ℝ)..Real.pi / 2,
      (((-1) ^ k * x ^ (2 * k + 1) * Real.sin ((2 * k + 1 : ℕ) * θ) : ℝ) : ℂ) * T.sineTransform (Real.sin θ) =
      (Real.pi / 2 : ℂ) * ((-1) ^ k * T.besselCoeff (2 * k + 1) * ((x ^ (2 * k + 1) : ℝ) : ℂ)) := fun k => by
    rw [T.besselCoeff_odd_eq_integral k]
    have e : (fun θ : ℝ => (((-1) ^ k * x ^ (2 * k + 1) * Real.sin ((2 * k + 1 : ℕ) * θ) : ℝ) : ℂ) *
        T.sineTransform (Real.sin θ)) = fun θ : ℝ => (((-1) ^ k * x ^ (2 * k + 1) : ℝ) : ℂ) *
          ((Real.sin ((2 * k + 1 : ℕ) * θ) : ℂ) * T.sineTransform (Real.sin θ)) := by
      funext θ; push_cast; ring
    rw [e, intervalIntegral.integral_const_mul]
    field_simp
    push_cast; ring
  simp_rw [hval] at hH
  rw [oddSeries, ← hH.tsum_eq, tsum_mul_left]
  field_simp

/-- **`|P(x)| ≤ ‖ψ'‖₁ x/(1−x²)`** for `0 ≤ x < 1`. -/
theorem norm_oddSeries_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    ‖T.oddSeries x‖ ≤ (∫ y, ‖deriv T.ψ y‖) * (x / (1 - x ^ 2)) := by
  set B := ∫ y, ‖deriv T.ψ y‖
  have hB : 0 ≤ B := integral_nonneg fun _ => norm_nonneg _
  have hq : 0 < 1 - x ^ 2 := by nlinarith
  rw [T.oddSeries_eq_integral hx0 hx, norm_mul]
  have hpt : ∀ θ ∈ Set.uIoc (0 : ℝ) (Real.pi / 2), ‖T.sineTransform (Real.sin θ) *
      ((x * (1 - x ^ 2) * Real.sin θ / (1 + 2 * x ^ 2 * Real.cos (2 * θ) + x ^ 4) : ℝ) : ℂ)‖ ≤
      B * (x / (1 - x ^ 2)) := fun θ _ => by
    have hD := sinTail_kernel_denom_ge (x := x) θ
    have hD0 : 0 < 1 + 2 * x ^ 2 * Real.cos (2 * θ) + x ^ 4 := lt_of_lt_of_le (by positivity) hD
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_mul,
      abs_of_nonneg hx0, abs_of_pos hq, abs_of_pos hD0]
    have hSm := T.norm_sineTransform_mul_le (Real.sin θ)
    calc ‖T.sineTransform (Real.sin θ)‖ * (x * (1 - x ^ 2) * |Real.sin θ| /
          (1 + 2 * x ^ 2 * Real.cos (2 * θ) + x ^ 4))
        = (‖T.sineTransform (Real.sin θ)‖ * |Real.sin θ|) * (x * (1 - x ^ 2) /
          (1 + 2 * x ^ 2 * Real.cos (2 * θ) + x ^ 4)) := by ring
      _ ≤ B * (x * (1 - x ^ 2) / (1 - x ^ 2) ^ 2) := by
          gcongr
      _ = B * (x / (1 - x ^ 2)) := by field_simp
  calc ‖(2 / Real.pi : ℂ)‖ * ‖∫ θ in (0 : ℝ)..Real.pi / 2, T.sineTransform (Real.sin θ) *
        ((x * (1 - x ^ 2) * Real.sin θ / (1 + 2 * x ^ 2 * Real.cos (2 * θ) + x ^ 4) : ℝ) : ℂ)‖
      ≤ (2 / Real.pi) * (B * (x / (1 - x ^ 2)) * |Real.pi / 2 - 0|) := by
        gcongr
        · rw [norm_div, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
        · exact intervalIntegral.norm_integral_le_of_norm_le_const hpt
    _ = _ := by
        rw [sub_zero, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 2)]
        field_simp

/-- **`|P(e^{−w})| ≤ ‖ψ'‖₁ / (2 sinh w)`** for `w > 0`. -/
theorem norm_oddSeries_exp_neg_le {w : ℝ} (hw : 0 < w) :
    ‖T.oddSeries (Real.exp (-w))‖ ≤ (∫ y, ‖deriv T.ψ y‖) / (2 * Real.sinh w) := by
  have hx1 : Real.exp (-w) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  refine (T.norm_oddSeries_le (Real.exp_pos _).le hx1).trans (le_of_eq ?_)
  have hs : 0 < Real.sinh w := Real.sinh_pos_iff.2 hw
  rw [mul_div_assoc']
  congr 1
  rw [Real.sinh_eq, div_eq_div_iff (by nlinarith [Real.exp_pos (-w)]) (by linarith)]
  have h2 : Real.exp (-w) ^ 2 = Real.exp (-w) * Real.exp (-w) := sq _
  have h3 : Real.exp w * Real.exp (-w) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [h3]

end BesselTestFunction

end

end GaloisForLFunctions.HTGeometry
