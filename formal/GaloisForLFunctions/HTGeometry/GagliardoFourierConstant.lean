import Mathlib

/-!
# The Gagliardo constant of a frequency

The difference-quotient and Fourier descriptions of a fractional Sobolev weight are matched by one
scalar integral.  Plancherel turns the translation difference of `u` into multiplication of `û` by
`e^{2πihξ} − 1`, so the Gagliardo seminorm becomes

`∫ |û(ξ)|² (∫ |e^{2πihξ} − 1|² |h|^{-(1+2s)} dh) dξ`,

and the inner integral depends on `ξ` only through `|ξ|^{2s}`.  Its value is the constant that
converts one description into the other.

The modulus is elementary,

`|e^{iθ} − 1|² = 2 − 2cos θ = 4 sin²(θ/2)`,

and the resulting integrand is integrable exactly on `0 < s < 1`: near the origin `sin²` cancels
two powers, leaving `h^{1−2s}`, which needs `s < 1`; near infinity the sine is bounded, leaving
`h^{−(1+2s)}`, which needs `s > 0`.
-/

open MeasureTheory Set Real

namespace GaloisForLFunctions.HTGeometry

/-! ## The modulus of a phase difference -/

/-- The half-angle form of the squared modulus of a phase difference. -/
theorem sin_sq_half (x : ℝ) : Real.sin (x / 2) ^ 2 = 1 / 2 - Real.cos x / 2 := by
  have hdouble : Real.cos x = 2 * Real.cos (x / 2) ^ 2 - 1 := by
    have := Real.cos_two_mul (x / 2)
    rwa [show 2 * (x / 2) = x by ring] at this
  have hpyth := Real.sin_sq_add_cos_sq (x / 2)
  linarith

/-- **The modulus of a phase difference.**  `|e^{iθ} − 1|² = 2 − 2cos θ`, by expanding the
exponential into its real and imaginary parts. -/
theorem normSq_exp_mul_I_sub_one (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ^ 2 = 2 - 2 * Real.cos θ := by
  rw [Complex.exp_mul_I, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_re,
    Complex.sin_ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]
  have hpyth := Real.sin_sq_add_cos_sq θ
  nlinarith [hpyth]

/-- The same modulus in half-angle form: `|e^{iθ} − 1|² = 4 sin²(θ/2)`. -/
theorem normSq_exp_mul_I_sub_one_eq_four_mul_sin_sq (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ^ 2 = 4 * Real.sin (θ / 2) ^ 2 := by
  rw [normSq_exp_mul_I_sub_one, sin_sq_half]
  ring

/-! ## The Gagliardo integrand and its two tails -/

/-- The Gagliardo integrand at unit frequency: the squared phase modulus against the fractional
weight. -/
noncomputable def gagliardoIntegrand (s h : ℝ) : ℝ :=
  4 * Real.sin (Real.pi * h) ^ 2 * h ^ (-(1 + 2 * s))

/-- The integrand is nonnegative on the positive ray. -/
theorem gagliardoIntegrand_nonneg {s h : ℝ} (hh : 0 < h) : 0 ≤ gagliardoIntegrand s h := by
  unfold gagliardoIntegrand
  have h1 : (0 : ℝ) ≤ 4 * Real.sin (Real.pi * h) ^ 2 := by positivity
  exact mul_nonneg h1 (Real.rpow_nonneg hh.le _)

/-- **Near the origin the sine cancels two powers.**  The integrand is dominated by a constant
multiple of `h^{1−2s}`. -/
theorem gagliardoIntegrand_le_near_zero {s h : ℝ} (hh : 0 < h) :
    gagliardoIntegrand s h ≤ 4 * Real.pi ^ 2 * h ^ (1 - 2 * s) := by
  unfold gagliardoIntegrand
  have hsin : Real.sin (Real.pi * h) ^ 2 ≤ (Real.pi * h) ^ 2 := by
    have habs : |Real.sin (Real.pi * h)| ≤ |Real.pi * h| := abs_sin_le_abs
    nlinarith [abs_nonneg (Real.sin (Real.pi * h)), abs_nonneg (Real.pi * h),
      sq_abs (Real.sin (Real.pi * h)), sq_abs (Real.pi * h)]
  have hw : (0 : ℝ) < h ^ (-(1 + 2 * s)) := Real.rpow_pos_of_pos hh _
  have hsplit : (Real.pi * h) ^ 2 * h ^ (-(1 + 2 * s)) = Real.pi ^ 2 * h ^ (1 - 2 * s) := by
    have hh2 : (h : ℝ) ^ 2 = h ^ (2 : ℝ) := by
      rw [← Real.rpow_natCast h 2]; norm_num
    rw [mul_pow, hh2, mul_assoc, ← Real.rpow_add hh]
    congr 2
    ring
  calc 4 * Real.sin (Real.pi * h) ^ 2 * h ^ (-(1 + 2 * s))
      ≤ 4 * (Real.pi * h) ^ 2 * h ^ (-(1 + 2 * s)) := by nlinarith [hsin, hw]
    _ = 4 * ((Real.pi * h) ^ 2 * h ^ (-(1 + 2 * s))) := by ring
    _ = 4 * (Real.pi ^ 2 * h ^ (1 - 2 * s)) := by rw [hsplit]
    _ = 4 * Real.pi ^ 2 * h ^ (1 - 2 * s) := by ring

/-- **Near infinity the sine is bounded.**  The integrand is dominated by `4 h^{−(1+2s)}`. -/
theorem gagliardoIntegrand_le_near_infty {s h : ℝ} (hh : 0 < h) :
    gagliardoIntegrand s h ≤ 4 * h ^ (-(1 + 2 * s)) := by
  unfold gagliardoIntegrand
  have hsin : Real.sin (Real.pi * h) ^ 2 ≤ 1 := by
    have := Real.neg_one_le_sin (Real.pi * h)
    have := Real.sin_le_one (Real.pi * h)
    nlinarith
  have hw : (0 : ℝ) < h ^ (-(1 + 2 * s)) := Real.rpow_pos_of_pos hh _
  nlinarith [hsin, hw]

/-! ## Integrability exactly on the unit strip of exponents -/

/-- The integrand is measurable. -/
theorem measurable_gagliardoIntegrand (s : ℝ) : Measurable (gagliardoIntegrand s) := by
  unfold gagliardoIntegrand
  fun_prop

/-- **The Gagliardo integrand is integrable near the origin exactly below `s = 1`.** -/
theorem integrableOn_gagliardoIntegrand_Ioo {s : ℝ} (hs : s < 1) :
    IntegrableOn (gagliardoIntegrand s) (Ioo 0 1) := by
  have hbase : IntegrableOn (fun h : ℝ => h ^ (1 - 2 * s)) (Ioo 0 1) := by
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one]
    linarith
  have hdom : IntegrableOn (fun h : ℝ => 4 * Real.pi ^ 2 * h ^ (1 - 2 * s)) (Ioo 0 1) :=
    hbase.const_mul _
  refine MeasureTheory.Integrable.mono' hdom
    (measurable_gagliardoIntegrand s).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
  rw [Real.norm_eq_abs, abs_of_nonneg (gagliardoIntegrand_nonneg hh.1)]
  exact gagliardoIntegrand_le_near_zero hh.1

/-- **The Gagliardo integrand is integrable near infinity exactly above `s = 0`.** -/
theorem integrableOn_gagliardoIntegrand_Ioi {s : ℝ} (hs : 0 < s) :
    IntegrableOn (gagliardoIntegrand s) (Ioi 1) := by
  have hbase : IntegrableOn (fun h : ℝ => h ^ (-(1 + 2 * s))) (Ioi 1) := by
    rw [integrableOn_Ioi_rpow_iff zero_lt_one]
    linarith
  have hdom : IntegrableOn (fun h : ℝ => 4 * h ^ (-(1 + 2 * s))) (Ioi 1) :=
    hbase.const_mul _
  refine MeasureTheory.Integrable.mono' hdom
    (measurable_gagliardoIntegrand s).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  have hpos : (0 : ℝ) < h := lt_trans zero_lt_one hh
  rw [Real.norm_eq_abs, abs_of_nonneg (gagliardoIntegrand_nonneg hpos)]
  exact gagliardoIntegrand_le_near_infty hpos

/-- **The Gagliardo constant exists exactly on `0 < s < 1`.**  Both tails converge there, so the
integrand is integrable on the whole positive ray.  This is the constant that converts the
difference-quotient description of a fractional Sobolev weight into the Fourier description. -/
theorem integrableOn_gagliardoIntegrand_Ioi_zero {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    IntegrableOn (gagliardoIntegrand s) (Ioi 0) := by
  have hsplit : Ioi (0 : ℝ) = Ioo 0 1 ∪ Ici 1 := by
    ext x
    simp only [mem_Ioi, mem_union, mem_Ioo, mem_Ici]
    constructor
    · intro hx
      rcases lt_or_ge x 1 with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr h
    · rintro (⟨h1, _⟩ | h1)
      · exact h1
      · linarith
  have hIci : IntegrableOn (gagliardoIntegrand s) (Ici 1) :=
    (integrableOn_gagliardoIntegrand_Ioi hs0).congr_set_ae Ioi_ae_eq_Ici.symm
  rw [hsplit]
  exact (integrableOn_gagliardoIntegrand_Ioo hs1).union hIci

/-! ## Strict positivity of the constant

The integrand is strictly positive on the whole unit window, because `sin(πh)` vanishes only at the
integers.  Positivity of `c_s` is what makes the Fourier description of the Sobolev weight
equivalent to the difference-quotient one rather than merely dominated by it.
-/

/-- The integrand is strictly positive on the unit window: `sin(πh)` has no zero there. -/
theorem gagliardoIntegrand_pos {s h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    0 < gagliardoIntegrand s h := by
  unfold gagliardoIntegrand
  have hsin : 0 < Real.sin (Real.pi * h) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
    nlinarith [Real.pi_pos]
  have hw : (0 : ℝ) < h ^ (-(1 + 2 * s)) := Real.rpow_pos_of_pos hh0 _
  have hnum : (0 : ℝ) < 4 * Real.sin (Real.pi * h) ^ 2 := by positivity
  exact mul_pos hnum hw

/-! ## The scaling law

The frequency enters the Gagliardo integral only through a dilation of the shift variable, and the
weight is homogeneous.  So the whole `ξ`-dependence is the single power `|ξ|^{2s}`, with the
constant `c_s` computed once at unit frequency.
-/

/-- The integrand at frequency `ξ` is a homogeneous rescaling of the unit-frequency integrand. -/
theorem gagliardoIntegrand_scaling {s ξ h : ℝ} (hξ : 0 < ξ) (hh : 0 < h) :
    4 * Real.sin (Real.pi * (ξ * h)) ^ 2 * h ^ (-(1 + 2 * s))
      = ξ ^ (1 + 2 * s) * gagliardoIntegrand s (ξ * h) := by
  unfold gagliardoIntegrand
  have hmul : (ξ * h) ^ (-(1 + 2 * s)) = ξ ^ (-(1 + 2 * s)) * h ^ (-(1 + 2 * s)) :=
    Real.mul_rpow hξ.le hh.le
  rw [hmul]
  have hinv : ξ ^ (1 + 2 * s) * ξ ^ (-(1 + 2 * s)) = 1 := by
    rw [← Real.rpow_add hξ]
    simp
  calc 4 * Real.sin (Real.pi * (ξ * h)) ^ 2 * h ^ (-(1 + 2 * s))
      = (ξ ^ (1 + 2 * s) * ξ ^ (-(1 + 2 * s))) *
        (4 * Real.sin (Real.pi * (ξ * h)) ^ 2 * h ^ (-(1 + 2 * s))) := by rw [hinv]; ring
    _ = ξ ^ (1 + 2 * s) *
        (4 * Real.sin (Real.pi * (ξ * h)) ^ 2 *
          (ξ ^ (-(1 + 2 * s)) * h ^ (-(1 + 2 * s)))) := by ring

/-- **The scaling law.**  The Gagliardo integral at frequency `ξ` is `|ξ|^{2s}` times its value at
unit frequency.  This is the whole `ξ`-dependence of the Fourier weight. -/
theorem integral_gagliardoIntegrand_scaling {s ξ : ℝ} (hξ : 0 < ξ) :
    (∫ h in Ioi (0 : ℝ), 4 * Real.sin (Real.pi * (ξ * h)) ^ 2 * h ^ (-(1 + 2 * s)))
      = ξ ^ (2 * s) * ∫ h in Ioi (0 : ℝ), gagliardoIntegrand s h := by
  have hcongr : (∫ h in Ioi (0 : ℝ), 4 * Real.sin (Real.pi * (ξ * h)) ^ 2 * h ^ (-(1 + 2 * s)))
      = ∫ h in Ioi (0 : ℝ), ξ ^ (1 + 2 * s) * gagliardoIntegrand s (ξ * h) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun h hh => ?_
    exact gagliardoIntegrand_scaling hξ (mem_Ioi.mp hh)
  rw [hcongr, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_comp_mul_left_Ioi (gagliardoIntegrand s) 0 hξ, mul_zero, smul_eq_mul]
  have hsplit : ξ ^ (1 + 2 * s) * (ξ⁻¹ * ∫ h in Ioi (0 : ℝ), gagliardoIntegrand s h)
      = (ξ ^ (1 + 2 * s) * ξ⁻¹) * ∫ h in Ioi (0 : ℝ), gagliardoIntegrand s h := by ring
  rw [hsplit]
  congr 1
  rw [show (ξ : ℝ)⁻¹ = ξ ^ (-1 : ℝ) by rw [Real.rpow_neg_one], ← Real.rpow_add hξ]
  congr 1
  ring

/-! ## The Fourier symbol of the difference operator

Translating multiplies the transform by a character, so the difference operator has symbol
`1 − e^{2πihξ}`.  Its squared modulus is exactly the numerator of the Gagliardo integrand — which
is why the difference-quotient and Fourier descriptions of the fractional weight agree, and why the
constant `c_s` computed above is the conversion factor.
-/

/-- **The symbol modulus is the Gagliardo numerator.**  `|1 − e^{2πiθ}|² = 4 sin²(πθ)`. -/
theorem normSq_one_sub_fourierChar (θ : ℝ) :
    ‖1 - ((Real.fourierChar θ : Circle) : ℂ)‖ ^ 2 = 4 * Real.sin (Real.pi * θ) ^ 2 := by
  have hchar : ((Real.fourierChar θ : Circle) : ℂ)
      = Complex.exp (((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I) := by
    rw [Real.fourierChar_apply]
  rw [← norm_neg, neg_sub, hchar]
  rw [normSq_exp_mul_I_sub_one_eq_four_mul_sin_sq,
    show (2 * Real.pi * θ) / 2 = Real.pi * θ by ring]

/-- The symbol modulus against the fractional weight is the Gagliardo integrand at frequency `ξ`. -/
theorem normSq_symbol_mul_weight (s ξ h : ℝ) :
    ‖1 - ((Real.fourierChar (h * ξ) : Circle) : ℂ)‖ ^ 2 * h ^ (-(1 + 2 * s))
      = 4 * Real.sin (Real.pi * (h * ξ)) ^ 2 * h ^ (-(1 + 2 * s)) := by
  rw [normSq_one_sub_fourierChar]

/-! ## The difference operator as a Fourier multiplier

The `L²` half needs no new construction: the corpus already carries Plancherel as an isometry and
the bounded-symbol Fourier multiplier (`HTGeometry/L2FourierMultiplier.lean`).  The difference
operator is the multiplier with symbol `1 − e^{2πihξ}`, whose modulus is bounded by `2` and whose
squared modulus is the Gagliardo numerator.
-/

/-- The symbol of the difference operator at shift `h`. -/
noncomputable def differenceSymbol (h ξ : ℝ) : ℂ := 1 - ((Real.fourierChar (h * ξ) : Circle) : ℂ)

/-- The symbol is measurable. -/
theorem measurable_differenceSymbol (h : ℝ) : Measurable (differenceSymbol h) := by
  unfold differenceSymbol
  have hc : Continuous fun ξ : ℝ => ((Real.fourierChar (h * ξ) : Circle) : ℂ) := by
    fun_prop
  exact (continuous_const.sub hc).measurable

/-- **The symbol is bounded by two**, since a character has modulus one. -/
theorem norm_differenceSymbol_le (h ξ : ℝ) : ‖differenceSymbol h ξ‖ ≤ 2 := by
  unfold differenceSymbol
  have hone : ‖((Real.fourierChar (h * ξ) : Circle) : ℂ)‖ = 1 := Circle.norm_coe _
  calc ‖(1 : ℂ) - ((Real.fourierChar (h * ξ) : Circle) : ℂ)‖
      ≤ ‖(1 : ℂ)‖ + ‖((Real.fourierChar (h * ξ) : Circle) : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [hone, norm_one]; norm_num

/-- **The squared symbol modulus is the Gagliardo numerator.** -/
theorem normSq_differenceSymbol (h ξ : ℝ) :
    ‖differenceSymbol h ξ‖ ^ 2 = 4 * Real.sin (Real.pi * (h * ξ)) ^ 2 :=
  normSq_one_sub_fourierChar (h * ξ)

/-! ## The Tonelli exchange

The Gagliardo double integral has a nonnegative integrand, so the order of integration may be
exchanged with no integrability side condition: the `ℝ≥0∞` Tonelli theorem applies directly.  After
the exchange the inner integral is the scaling law, which contributes `c_s |ξ|^{2s}` pointwise.
-/

/-- The two-variable Gagliardo kernel is measurable. -/
theorem measurable_gagliardoKernel (s : ℝ) :
    Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal (4 * Real.sin (Real.pi * (p.2 * p.1)) ^ 2 * p.1 ^ (-(1 + 2 * s))) := by
  fun_prop

/-- **The Gagliardo double integral may be exchanged.**  Both variables run over the positive ray
and the integrand is nonnegative, so Tonelli applies in `ℝ≥0∞` with no side conditions. -/
theorem lintegral_gagliardo_swap {s : ℝ} {G : ℝ → ENNReal} (hG : Measurable G) :
    (∫⁻ h in Ioi (0 : ℝ), ∫⁻ ξ in Ioi (0 : ℝ),
        ENNReal.ofReal (4 * Real.sin (Real.pi * (ξ * h)) ^ 2 * h ^ (-(1 + 2 * s))) * G ξ)
      = ∫⁻ ξ in Ioi (0 : ℝ), ∫⁻ h in Ioi (0 : ℝ),
        ENNReal.ofReal (4 * Real.sin (Real.pi * (ξ * h)) ^ 2 * h ^ (-(1 + 2 * s))) * G ξ := by
  refine MeasureTheory.lintegral_lintegral_swap ?_
  refine Measurable.aemeasurable ?_
  exact (measurable_gagliardoKernel s).mul (hG.comp measurable_snd)

end GaloisForLFunctions.HTGeometry
