import GaloisForLFunctions.RHTower.BesselJZeroODE

/-!
# The envelope of the derivative of the order-zero Bessel function

The same two-block van der Corput split that bounds `J_0` bounds its derivative: the representation

```text
J_0'(u) = -(2/pi) int_0^(pi/2) sin θ sin(u sin θ) dθ
```

has the same phase `u sin θ` and the amplitude `sin θ`, whose total variation on a quarter period is
bounded by an absolute constant.  Hence

```text
|J_0'(u)| <= 144 sqrt 2 / sqrt u,     u >= 1.
```

* `besselJ0Deriv_eq_two_div_pi_mul` — the reflection `θ ↦ pi - θ` folding the derivative integral onto
  a quarter period.
* `integral_sin_mul_sin_eq_neg_im` — the passage to the complex oscillatory integral, with amplitude
  `sin θ`.
* `norm_integral_sinAmp_besselPhase_first`, `norm_integral_sinAmp_besselPhase_second` — the two van der
  Corput blocks.
* **`abs_besselJ0Deriv_le_envelope`** — the derivative envelope.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set Filter Topology

/-! ## The amplitude `sin θ` as a complex function -/

/-- The complex amplitude of the derivative representation. -/
def sinAmp (θ : ℝ) : ℂ := (Real.sin θ : ℂ)

theorem hasDerivAt_sinAmp (θ : ℝ) : HasDerivAt sinAmp ((Real.cos θ : ℂ)) θ :=
  (Real.hasDerivAt_sin θ).ofReal_comp

theorem deriv_sinAmp : deriv sinAmp = fun θ : ℝ => (Real.cos θ : ℂ) :=
  funext fun θ => (hasDerivAt_sinAmp θ).deriv

theorem contDiff_sinAmp : ContDiff ℝ 1 sinAmp := by
  have h : ContDiff ℝ 1 fun θ : ℝ => (Real.sin θ : ℂ) :=
    Complex.ofRealCLM.contDiff.comp Real.contDiff_sin
  exact h

theorem continuous_sinAmp : Continuous sinAmp :=
  Complex.continuous_ofReal.comp Real.continuous_sin

theorem norm_sinAmp_le (θ : ℝ) : ‖sinAmp θ‖ ≤ 1 := by
  rw [sinAmp, Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_sin_le_one θ

/-- The amplitude budget of `sin θ` on a subinterval of the quarter period is at most `4`. -/
theorem sinAmp_budget_le {a b : ℝ} (hab : a ≤ b) (hb : b ≤ Real.pi / 2) (ha : 0 ≤ a) :
    ‖sinAmp b‖ + ‖sinAmp a‖ + ∫ t in a..b, ‖deriv sinAmp t‖ ≤ 4 := by
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hint : (∫ t in a..b, ‖deriv sinAmp t‖) ≤ 1 * |b - a| := by
    rw [deriv_sinAmp]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun t : ℝ => ‖(Real.cos t : ℂ)‖) (a := a) (b := b) (C := 1)
      (fun x _ => by
        rw [Real.norm_eq_abs, abs_norm, Complex.norm_real, Real.norm_eq_abs]
        exact Real.abs_cos_le_one x)
    calc (∫ t in a..b, ‖(Real.cos t : ℂ)‖)
        ≤ |∫ t in a..b, ‖(Real.cos t : ℂ)‖| := le_abs_self _
      _ ≤ 1 * |b - a| := by
          rw [← Real.norm_eq_abs]
          exact h
  have hlen : |b - a| ≤ 2 := by
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - a)]
    linarith
  have h1 := norm_sinAmp_le b
  have h2 := norm_sinAmp_le a
  linarith

/-! ## Folding the derivative integral -/

theorem continuous_sin_mul_sin' (u : ℝ) :
    Continuous fun θ : ℝ => Real.sin θ * Real.sin (u * Real.sin θ) := by fun_prop

theorem besselJ0Deriv_eq_two_div_pi_mul (u : ℝ) :
    besselJ0Deriv u
      = -(2 / Real.pi) * ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ * Real.sin (u * Real.sin θ) := by
  have hcont := continuous_sin_mul_sin' u
  have hsplit : (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * Real.sin (u * Real.sin θ))
      = (∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ * Real.sin (u * Real.sin θ))
        + ∫ θ in (Real.pi / 2)..Real.pi, Real.sin θ * Real.sin (u * Real.sin θ) :=
    (intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)).symm
  have hrefl : (∫ θ in (Real.pi / 2)..Real.pi, Real.sin θ * Real.sin (u * Real.sin θ))
      = ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ * Real.sin (u * Real.sin θ) := by
    have h := intervalIntegral.integral_comp_sub_left
      (fun θ : ℝ => Real.sin θ * Real.sin (u * Real.sin θ)) Real.pi (a := 0) (b := Real.pi / 2)
    have h1 : Real.pi - Real.pi / 2 = Real.pi / 2 := by ring
    have h2 : Real.pi - 0 = Real.pi := by ring
    rw [h1, h2] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp [Real.sin_pi_sub]
  rw [besselJ0Deriv, hsplit, hrefl]
  ring

/-! ## The complex oscillatory form -/

theorem integral_sin_mul_sin_eq_neg_im (u a b : ℝ) :
    (∫ θ in a..b, Real.sin θ * Real.sin (u * Real.sin θ))
      = -(∫ θ in a..b, sinAmp θ * Complex.exp (Complex.I * (besselPhase u θ : ℂ))).im := by
  have hcont : Continuous
      fun θ : ℝ => sinAmp θ * Complex.exp (Complex.I * (besselPhase u θ : ℂ)) := by
    refine continuous_sinAmp.mul ((continuous_besselIntegrand u).congr ?_)
    intro θ
    rw [one_mul]
  have hint : IntervalIntegrable
      (fun θ : ℝ => sinAmp θ * Complex.exp (Complex.I * (besselPhase u θ : ℂ))) volume a b :=
    hcont.intervalIntegrable _ _
  have h := ContinuousLinearMap.intervalIntegral_comp_comm (Complex.imCLM) hint
  rw [Complex.imCLM_apply] at h
  rw [← h, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hexp : (Complex.exp (Complex.I * (besselPhase u θ : ℂ))).im
      = Real.sin (besselPhase u θ) := by
    rw [mul_comm Complex.I, Complex.exp_ofReal_mul_I_im]
  have hmul : (sinAmp θ * Complex.exp (Complex.I * (besselPhase u θ : ℂ))).im
      = Real.sin θ * Real.sin (besselPhase u θ) := by
    rw [sinAmp, Complex.mul_im, hexp, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [Complex.imCLM_apply, hmul, besselPhase, Real.sin_neg]
  ring

/-! ## The two blocks -/

theorem norm_integral_sinAmp_besselPhase_first {u : ℝ} (hu : 0 < u) :
    ‖∫ θ in (0 : ℝ)..(Real.pi / 4), sinAmp θ * Complex.exp (Complex.I * (besselPhase u θ : ℂ))‖
      ≤ 16 * Real.sqrt 2 / u := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hab : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  set lam : ℝ := u * (Real.sqrt 2 / 2) with hlam
  have hlampos : 0 < lam := by rw [hlam]; positivity
  have hnn : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 4), 0 ≤ deriv (deriv (besselPhase u)) t := by
    intro t ht
    rw [deriv_deriv_besselPhase]
    have hsin : 0 ≤ Real.sin t :=
      Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (le_trans ht.2 (by linarith))
    positivity
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 4), lam ≤ |deriv (besselPhase u) t| := by
    intro t ht
    rw [deriv_besselPhase]
    have hcos : Real.sqrt 2 / 2 ≤ Real.cos t := by
      have h := Real.cos_le_cos_of_nonneg_of_le_pi ht.1 (by linarith) ht.2
      rwa [Real.cos_pi_div_four] at h
    have hcosnn : (0 : ℝ) ≤ Real.cos t := le_trans (by positivity) hcos
    rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ u * Real.cos t), hlam]
    exact mul_le_mul_of_nonneg_left hcos hu.le
  have h := _root_.RHTower.firstDerivTest (φ := besselPhase u) (A := sinAmp)
    hab hlampos (contDiff_besselPhase u) hnn hbound contDiff_sinAmp
  have hbud : ‖sinAmp (Real.pi / 4)‖ + ‖sinAmp 0‖
      + ∫ t in (0 : ℝ)..(Real.pi / 4), ‖deriv sinAmp t‖ ≤ 4 :=
    sinAmp_budget_le (by positivity) (by linarith) (le_refl 0)
  refine h.trans ?_
  calc 4 * (‖sinAmp (Real.pi / 4)‖ + ‖sinAmp 0‖
        + ∫ t in (0 : ℝ)..(Real.pi / 4), ‖deriv sinAmp t‖) / lam
      ≤ 4 * 4 / lam := by gcongr
    _ = 16 * Real.sqrt 2 / u := by
        rw [hlam, div_eq_div_iff (by positivity) hu.ne']
        linear_combination (-(8 * u)) * hs2

theorem norm_integral_sinAmp_besselPhase_second {u : ℝ} (hu : 0 < u) :
    ‖∫ θ in (Real.pi / 4)..(Real.pi / 2),
        sinAmp θ * Complex.exp (Complex.I * (besselPhase u θ : ℂ))‖
      ≤ 128 * Real.sqrt 2 / Real.sqrt u := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hab : Real.pi / 4 ≤ Real.pi / 2 := by linarith
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hmupos : (0 : ℝ) < u / 2 := by positivity
  have hbound : ∀ t ∈ Set.Icc (Real.pi / 4) (Real.pi / 2),
      u / 2 ≤ deriv (deriv (besselPhase u)) t := by
    intro t ht
    rw [deriv_deriv_besselPhase]
    have hsin : Real.sqrt 2 / 2 ≤ Real.sin t := by
      have h := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) ht.2 ht.1
      rwa [Real.sin_pi_div_four] at h
    have hs2le : (1 : ℝ) ≤ Real.sqrt 2 := by nlinarith
    have hhalf : (1 : ℝ) / 2 ≤ Real.sin t := le_trans (by linarith) hsin
    calc u / 2 = u * (1 / 2) := by ring
      _ ≤ u * Real.sin t := mul_le_mul_of_nonneg_left hhalf hu.le
  have h := _root_.RHTower.secondDerivTest (φ := besselPhase u) (A := sinAmp)
    hab hmupos (contDiff_besselPhase u) hbound contDiff_sinAmp
  have hbud : ‖sinAmp (Real.pi / 2)‖ + ‖sinAmp (Real.pi / 4)‖
      + ∫ t in (Real.pi / 4)..(Real.pi / 2), ‖deriv sinAmp t‖ ≤ 4 :=
    sinAmp_budget_le hab (le_refl _) (by positivity)
  refine h.trans ?_
  have hsqrt : Real.sqrt (u / 2) = Real.sqrt u / Real.sqrt 2 := Real.sqrt_div hu.le 2
  have hupos : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.mpr hu
  calc 32 * (‖sinAmp (Real.pi / 2)‖ + ‖sinAmp (Real.pi / 4)‖
        + ∫ t in (Real.pi / 4)..(Real.pi / 2), ‖deriv sinAmp t‖) / Real.sqrt (u / 2)
      ≤ 32 * 4 / Real.sqrt (u / 2) := by gcongr
    _ = 128 * Real.sqrt 2 / Real.sqrt u := by
        rw [hsqrt, div_div_eq_mul_div]
        norm_num

/-! ## The derivative envelope -/

theorem abs_integral_quarterPeriod_sin_le {u : ℝ} (hu : 1 ≤ u) :
    |∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ * Real.sin (u * Real.sin θ)|
      ≤ 144 * Real.sqrt 2 / Real.sqrt u := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu
  have hupos : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.mpr hu0
  have hcont : Continuous
      fun θ : ℝ => sinAmp θ * Complex.exp (Complex.I * (besselPhase u θ : ℂ)) := by
    refine continuous_sinAmp.mul ((continuous_besselIntegrand u).congr ?_)
    intro θ
    rw [one_mul]
  have hint : ∀ a b : ℝ, IntervalIntegrable
      (fun θ : ℝ => sinAmp θ * Complex.exp (Complex.I * (besselPhase u θ : ℂ))) volume a b :=
    fun a b => hcont.intervalIntegrable a b
  have hsplit : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        sinAmp θ * Complex.exp (Complex.I * (besselPhase u θ : ℂ)))
      = (∫ θ in (0 : ℝ)..(Real.pi / 4),
          sinAmp θ * Complex.exp (Complex.I * (besselPhase u θ : ℂ)))
        + ∫ θ in (Real.pi / 4)..(Real.pi / 2),
            sinAmp θ * Complex.exp (Complex.I * (besselPhase u θ : ℂ)) :=
    (intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)).symm
  rw [integral_sin_mul_sin_eq_neg_im, abs_neg]
  refine le_trans (Complex.abs_im_le_norm _) ?_
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have h1 := norm_integral_sinAmp_besselPhase_first hu0
  have h2 := norm_integral_sinAmp_besselPhase_second hu0
  have hfirst : 16 * Real.sqrt 2 / u ≤ 16 * Real.sqrt 2 / Real.sqrt u := by
    have := sqrt_le_self_of_one_le hu
    gcongr
  have hsum : 16 * Real.sqrt 2 / Real.sqrt u + 128 * Real.sqrt 2 / Real.sqrt u
      = 144 * Real.sqrt 2 / Real.sqrt u := by
    field_simp
    ring
  linarith [h1, h2, hfirst, hsum]

/-- **The derivative envelope.**  `J_0'` decays like `u^{-1/2}` as well, with the same mechanism: the
stationary point of the phase at `θ = pi/2` is nondegenerate, and the amplitude `sin θ` has bounded
total variation. -/
theorem abs_besselJ0Deriv_le_envelope {u : ℝ} (hu : 1 ≤ u) :
    |besselJ0Deriv u| ≤ 144 * Real.sqrt 2 / Real.sqrt u := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu
  have hupos : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.mpr hu0
  have hfac : (2 : ℝ) / Real.pi ≤ 1 := by
    rw [div_le_one hpi]
    linarith [Real.pi_gt_three]
  rw [besselJ0Deriv_eq_two_div_pi_mul, abs_mul, abs_neg,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / Real.pi)]
  have hbase := abs_integral_quarterPeriod_sin_le hu
  have habs : (0 : ℝ) ≤ |∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ * Real.sin (u * Real.sin θ)| :=
    abs_nonneg _
  calc (2 / Real.pi) * |∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ * Real.sin (u * Real.sin θ)|
      ≤ 1 * |∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ * Real.sin (u * Real.sin θ)| :=
        mul_le_mul_of_nonneg_right hfac habs
    _ = |∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ * Real.sin (u * Real.sin θ)| := one_mul _
    _ ≤ 144 * Real.sqrt 2 / Real.sqrt u := hbase

/-! ## The Liouville–Green normalisation -/

/-- The normalisation `v(x) = sqrt x · J_0(x)`, which removes the first-order term of Bessel's
equation. -/
def besselV (x : ℝ) : ℝ := Real.sqrt x * besselJ0 x

/-- Its derivative. -/
def besselVDeriv (x : ℝ) : ℝ :=
  1 / (2 * Real.sqrt x) * besselJ0 x + Real.sqrt x * besselJ0Deriv x

theorem hasDerivAt_besselV {x : ℝ} (hx : 0 < x) : HasDerivAt besselV (besselVDeriv x) x :=
  (Real.hasDerivAt_sqrt hx.ne').mul (hasDerivAt_besselJ0 x)

/-- **The normalised equation.**  `v'' = -(1 + 1/(4x²)) v`: the first-order term of Bessel's equation
is absorbed, leaving a harmonic oscillator with an integrable perturbation. -/
theorem hasDerivAt_besselVDeriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt besselVDeriv (-(1 + 1 / (4 * x ^ (2 : ℕ))) * besselV x) x := by
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  have hsqrt : HasDerivAt (fun t : ℝ => Real.sqrt t) (1 / (2 * Real.sqrt x)) x :=
    Real.hasDerivAt_sqrt hx.ne'
  have hden : HasDerivAt (fun t : ℝ => 2 * Real.sqrt t) (2 * (1 / (2 * Real.sqrt x))) x :=
    hsqrt.const_mul 2
  have hinv : HasDerivAt (fun t : ℝ => 1 / (2 * Real.sqrt t))
      (-(1 / (4 * x * Real.sqrt x))) x := by
    have h := (hasDerivAt_const x (1 : ℝ)).fun_div hden (by positivity)
    have h4 : (2 * Real.sqrt x) ^ (2 : ℕ) = 4 * x := by
      rw [mul_pow, Real.sq_sqrt hx.le]
      ring
    have hval : ((0 : ℝ) * (2 * Real.sqrt x) - 1 * (2 * (1 / (2 * Real.sqrt x))))
          / (2 * Real.sqrt x) ^ (2 : ℕ)
        = -(1 / (4 * x * Real.sqrt x)) := by
      rw [h4]
      field_simp
      ring
    rw [hval] at h
    exact h
  have hprod1 : HasDerivAt (fun t : ℝ => 1 / (2 * Real.sqrt t) * besselJ0 t)
      (-(1 / (4 * x * Real.sqrt x)) * besselJ0 x
        + 1 / (2 * Real.sqrt x) * besselJ0Deriv x) x :=
    hinv.mul (hasDerivAt_besselJ0 x)
  have hprod2 : HasDerivAt (fun t : ℝ => Real.sqrt t * besselJ0Deriv t)
      (1 / (2 * Real.sqrt x) * besselJ0Deriv x + Real.sqrt x * besselJ0SecondDeriv x) x :=
    hsqrt.mul (hasDerivAt_besselJ0Deriv x)
  have h := hprod1.add hprod2
  have hode := besselJ0_ode hx.ne'
  have h2 : besselJ0SecondDeriv x = -(besselJ0Deriv x / x) - besselJ0 x := by linarith [hode]
  have hval : -(1 / (4 * x * Real.sqrt x)) * besselJ0 x + 1 / (2 * Real.sqrt x) * besselJ0Deriv x
      + (1 / (2 * Real.sqrt x) * besselJ0Deriv x + Real.sqrt x * besselJ0SecondDeriv x)
      = -(1 + 1 / (4 * x ^ (2 : ℕ))) * besselV x := by
    obtain ⟨S, hS0, hSx, hSeq⟩ : ∃ S : ℝ, 0 < S ∧ S * S = x ∧ Real.sqrt x = S :=
      ⟨Real.sqrt x, hsx, hsq, rfl⟩
    rw [h2, besselV, hSeq, ← hSx]
    field_simp
    ring
  rw [hval] at h
  exact h

/-! ## Boundedness of the normalised solution -/

theorem abs_besselV_le {x : ℝ} (hx : 1 ≤ x) : |besselV x| ≤ 72 * Real.sqrt 2 := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hJ := abs_besselJ0_le_envelope hx
  rw [besselV, abs_mul, abs_of_nonneg hsx.le]
  calc Real.sqrt x * |besselJ0 x| ≤ Real.sqrt x * (72 * Real.sqrt 2 / Real.sqrt x) := by
        exact mul_le_mul_of_nonneg_left hJ hsx.le
    _ = 72 * Real.sqrt 2 := by
        field_simp

theorem abs_besselVDeriv_le {x : ℝ} (hx : 1 ≤ x) : |besselVDeriv x| ≤ 180 * Real.sqrt 2 := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hsx1 : (1 : ℝ) ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hJ := abs_besselJ0_le_envelope hx
  have hD := abs_besselJ0Deriv_le_envelope hx
  have h1 : |1 / (2 * Real.sqrt x) * besselJ0 x| ≤ 36 * Real.sqrt 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.sqrt x))]
    calc 1 / (2 * Real.sqrt x) * |besselJ0 x|
        ≤ 1 / (2 * Real.sqrt x) * (72 * Real.sqrt 2 / Real.sqrt x) := by
          exact mul_le_mul_of_nonneg_left hJ (by positivity)
      _ = 36 * Real.sqrt 2 / (Real.sqrt x * Real.sqrt x) := by
          field_simp
          ring
      _ ≤ 36 * Real.sqrt 2 := by
          rw [hsq, div_le_iff₀ hx0]
          nlinarith [Real.sqrt_nonneg 2]
  have h2 : |Real.sqrt x * besselJ0Deriv x| ≤ 144 * Real.sqrt 2 := by
    rw [abs_mul, abs_of_nonneg hsx.le]
    calc Real.sqrt x * |besselJ0Deriv x|
        ≤ Real.sqrt x * (144 * Real.sqrt 2 / Real.sqrt x) := by
          exact mul_le_mul_of_nonneg_left hD hsx.le
      _ = 144 * Real.sqrt 2 := by field_simp
  rw [besselVDeriv]
  calc |1 / (2 * Real.sqrt x) * besselJ0 x + Real.sqrt x * besselJ0Deriv x|
      ≤ |1 / (2 * Real.sqrt x) * besselJ0 x| + |Real.sqrt x * besselJ0Deriv x| := abs_add_le _ _
    _ ≤ 36 * Real.sqrt 2 + 144 * Real.sqrt 2 := by linarith
    _ = 180 * Real.sqrt 2 := by ring

/-! ## The integrable perturbation weight -/

/-- The weight `x^{-2}`, with antiderivative `-x^{-1}`. -/
def invSq (x : ℝ) : ℝ := (x ^ (2 : ℕ))⁻¹

theorem invSq_nonneg (x : ℝ) : 0 ≤ invSq x := by
  rw [invSq]
  positivity

theorem hasDerivAt_negInv {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => -t⁻¹) (invSq x) x := by
  have h := (hasDerivAt_inv hx).neg
  rw [show -(-(x ^ (2 : ℕ))⁻¹) = invSq x from by rw [invSq]; ring] at h
  exact h

theorem continuousWithinAt_negInv {a : ℝ} (ha : 0 < a) :
    ContinuousWithinAt (fun t : ℝ => -t⁻¹) (Ici a) a :=
  ((continuousAt_inv₀ ha.ne').neg).continuousWithinAt

theorem tendsto_negInv : Filter.Tendsto (fun t : ℝ => -t⁻¹) atTop (𝓝 0) := by
  simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).neg

theorem integrableOn_invSq {a : ℝ} (ha : 0 < a) : IntegrableOn invSq (Ioi a) volume :=
  MeasureTheory.integrableOn_Ioi_deriv_of_nonneg (continuousWithinAt_negInv ha)
    (fun _ hx => hasDerivAt_negInv (ne_of_gt (lt_trans ha hx)))
    (fun x _ => invSq_nonneg x) tendsto_negInv

theorem integral_Ioi_invSq {a : ℝ} (ha : 0 < a) : (∫ x in Ioi a, invSq x) = a⁻¹ := by
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg
    (continuousWithinAt_negInv ha)
    (fun _ hx => hasDerivAt_negInv (ne_of_gt (lt_trans ha hx)))
    (fun x _ => invSq_nonneg x) tendsto_negInv
  rw [h]
  ring

/-! ## The rotating frame -/

/-- The rotating frame of the normalised solution, `w = (v + i v') e^{i x}`.  It is constant for the
unperturbed oscillator and moves at speed `O(x^{-2})` for Bessel. -/
def besselW (x : ℝ) : ℂ :=
  ((besselV x : ℂ) + Complex.I * (besselVDeriv x : ℂ)) * Complex.exp (Complex.I * (x : ℂ))

/-- The exact speed of the rotating frame. -/
def besselWDeriv (x : ℝ) : ℂ :=
  -(Complex.I * ((1 / (4 * x ^ (2 : ℕ)) : ℝ) : ℂ) * (besselV x : ℂ)
    * Complex.exp (Complex.I * (x : ℂ)))

theorem continuous_besselJ0 : Continuous besselJ0 :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_besselJ0 x).continuousAt

theorem continuous_besselV : Continuous besselV :=
  Real.continuous_sqrt.mul continuous_besselJ0

theorem continuous_cexp_I_mul : Continuous fun t : ℝ => Complex.exp (Complex.I * (t : ℂ)) := by
  refine Complex.continuous_exp.comp (continuous_const.mul ?_)
  exact Complex.continuous_ofReal

/-- **The frame equation.**  The whole motion of the frame is the perturbation `1/(4x²)`; the harmonic
part cancels exactly. -/
theorem hasDerivAt_besselW {x : ℝ} (hx : 0 < x) : HasDerivAt besselW (besselWDeriv x) x := by
  have hV : HasDerivAt (fun t : ℝ => (besselV t : ℂ)) ((besselVDeriv x : ℝ) : ℂ) x :=
    (hasDerivAt_besselV hx).ofReal_comp
  have hD : HasDerivAt (fun t : ℝ => (besselVDeriv t : ℂ))
      (((-(1 + 1 / (4 * x ^ (2 : ℕ))) * besselV x : ℝ) : ℂ)) x :=
    (hasDerivAt_besselVDeriv hx).ofReal_comp
  have hid : HasDerivAt (fun t : ℝ => ((t : ℝ) : ℂ)) (1 : ℂ) x := by
    simpa using (hasDerivAt_id x).ofReal_comp
  have hIt : HasDerivAt (fun t : ℝ => Complex.I * ((t : ℝ) : ℂ)) Complex.I x := by
    simpa using hid.const_mul Complex.I
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * ((t : ℝ) : ℂ)))
      (Complex.exp (Complex.I * (x : ℂ)) * Complex.I) x := hIt.cexp
  have hsum := hV.fun_add (hD.const_mul Complex.I)
  have h := hsum.fun_mul hexp
  have hval : (((besselVDeriv x : ℝ) : ℂ)
        + Complex.I * ((-(1 + 1 / (4 * x ^ (2 : ℕ))) * besselV x : ℝ) : ℂ))
        * Complex.exp (Complex.I * (x : ℂ))
      + (((besselV x : ℝ) : ℂ) + Complex.I * ((besselVDeriv x : ℝ) : ℂ))
        * (Complex.exp (Complex.I * (x : ℂ)) * Complex.I)
      = besselWDeriv x := by
    rw [besselWDeriv]
    push_cast
    linear_combination (((besselVDeriv x : ℝ) : ℂ) * Complex.exp (Complex.I * (x : ℂ)))
      * Complex.I_sq
  rw [hval] at h
  exact h

theorem norm_besselWDeriv_le {x : ℝ} (hx : 1 ≤ x) :
    ‖besselWDeriv x‖ ≤ 18 * Real.sqrt 2 * invSq x := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hexp : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
    rw [mul_comm]
    exact Complex.norm_exp_ofReal_mul_I x
  have hV := abs_besselV_le hx
  rw [besselWDeriv, norm_neg, norm_mul, norm_mul, norm_mul, hexp, Complex.norm_I,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (4 * x ^ (2 : ℕ)))]
  rw [one_mul, mul_one, invSq]
  calc 1 / (4 * x ^ (2 : ℕ)) * |besselV x| ≤ 1 / (4 * x ^ (2 : ℕ)) * (72 * Real.sqrt 2) := by
        exact mul_le_mul_of_nonneg_left hV (by positivity)
    _ = 18 * Real.sqrt 2 * (x ^ (2 : ℕ))⁻¹ := by ring

theorem continuousOn_besselWDeriv : ContinuousOn besselWDeriv (Ioi 1) := by
  intro x hx
  have hx1 : (1 : ℝ) < x := hx
  have hx0 : x ≠ 0 := by
    have : (0 : ℝ) < x := lt_trans zero_lt_one hx1
    exact this.ne'
  have hw : ContinuousWithinAt (fun t : ℝ => ((1 / (4 * t ^ (2 : ℕ)) : ℝ) : ℂ)) (Ioi 1) x := by
    refine (Complex.continuous_ofReal.continuousAt.comp ?_).continuousWithinAt
    exact ContinuousAt.div continuousAt_const (by fun_prop) (by positivity)
  have hVc : ContinuousWithinAt (fun t : ℝ => (besselV t : ℂ)) (Ioi 1) x :=
    ((Complex.continuous_ofReal.comp continuous_besselV).continuousAt).continuousWithinAt
  have hE : ContinuousWithinAt (fun t : ℝ => Complex.exp (Complex.I * (t : ℂ))) (Ioi 1) x :=
    (continuous_cexp_I_mul.continuousAt).continuousWithinAt
  exact (((continuousWithinAt_const.mul hw).mul hVc).mul hE).neg

theorem integrableOn_besselWDeriv : IntegrableOn besselWDeriv (Ioi 1) volume := by
  have hdom : IntegrableOn (fun t : ℝ => 18 * Real.sqrt 2 * invSq t) (Ioi 1) volume :=
    (integrableOn_invSq (by norm_num)).const_mul _
  refine MeasureTheory.Integrable.mono' hdom
    (continuousOn_besselWDeriv.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_besselWDeriv_le (le_of_lt ht)

/-! ## The limit of the frame -/

/-- **The frame converges.**  Its total variation past `x` is `O(1/x)`, so the rotating frame settles
to a limit: the Bessel oscillation is asymptotically a pure cosine wave. -/
theorem exists_besselW_limit :
    ∃ L : ℂ, ∀ x : ℝ, 1 ≤ x → ‖besselW x - L‖ ≤ 18 * Real.sqrt 2 / x := by
  have hint := integrableOn_besselWDeriv
  refine ⟨besselW 1 + ∫ t in Ioi (1 : ℝ), besselWDeriv t, fun x hx => ?_⟩
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hI1 : IntegrableOn besselWDeriv (Ioc 1 x) volume := hint.mono_set (fun t ht => ht.1)
  have hI2 : IntegrableOn besselWDeriv (Ioi x) volume :=
    hint.mono_set (fun t ht => lt_of_le_of_lt hx ht)
  have hdisj : Disjoint (Ioc (1 : ℝ) x) (Ioi x) := by
    refine Set.disjoint_left.mpr fun t ht ht' => ?_
    exact absurd ht'.out (not_lt.mpr ht.2)
  have hunion : Ioc (1 : ℝ) x ∪ Ioi x = Ioi 1 := Ioc_union_Ioi_eq_Ioi hx
  have hsplit : (∫ t in Ioi (1 : ℝ), besselWDeriv t)
      = (∫ t in Ioc (1 : ℝ) x, besselWDeriv t) + ∫ t in Ioi x, besselWDeriv t := by
    rw [← hunion]
    exact MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hI1 hI2
  have hftc : (∫ t in (1 : ℝ)..x, besselWDeriv t) = besselW x - besselW 1 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => ?_) ?_
    · have ht1 : (1 : ℝ) ≤ t := by
        rw [Set.uIcc_of_le hx] at ht
        exact ht.1
      exact hasDerivAt_besselW (lt_of_lt_of_le zero_lt_one ht1)
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
      exact hI1
  have hIoc : (∫ t in Ioc (1 : ℝ) x, besselWDeriv t) = besselW x - besselW 1 := by
    rw [← intervalIntegral.integral_of_le hx]
    exact hftc
  have heq : besselW x - (besselW 1 + ∫ t in Ioi (1 : ℝ), besselWDeriv t)
      = -∫ t in Ioi x, besselWDeriv t := by
    rw [hsplit, hIoc]
    ring
  rw [heq, norm_neg]
  have hnorm : IntegrableOn (fun t : ℝ => 18 * Real.sqrt 2 * invSq t) (Ioi x) volume :=
    (integrableOn_invSq hx0).const_mul _
  calc ‖∫ t in Ioi x, besselWDeriv t‖ ≤ ∫ t in Ioi x, ‖besselWDeriv t‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi x, 18 * Real.sqrt 2 * invSq t := by
        refine MeasureTheory.setIntegral_mono_on hI2.norm hnorm measurableSet_Ioi fun t ht => ?_
        exact norm_besselWDeriv_le (le_trans hx (le_of_lt ht))
    _ = 18 * Real.sqrt 2 * x⁻¹ := by
        rw [MeasureTheory.integral_const_mul, integral_Ioi_invSq hx0]
    _ = 18 * Real.sqrt 2 / x := by
        rw [div_eq_mul_inv]

/-! ## The phase asymptotic -/

theorem besselV_eq_re {x : ℝ} :
    besselV x = (besselW x * Complex.exp (-(Complex.I * (x : ℂ)))).re := by
  rw [besselW, mul_assoc, ← Complex.exp_add]
  rw [show Complex.I * (x : ℂ) + -(Complex.I * (x : ℂ)) = 0 from by ring]
  rw [Complex.exp_zero, mul_one, Complex.add_re, Complex.mul_re]
  simp

/-- **The Bessel phase asymptotic.**  There are absolute constants `p, q` with

```text
|sqrt x J_0(x) - (p cos x + q sin x)| <= 18 sqrt 2 / x,      x >= 1,
```

so `J_0(x) = A x^{-1/2} cos(x - δ) + O(x^{-3/2})` with `A = sqrt(p² + q²)`.  The constants are the real
and imaginary parts of the limit of the rotating frame; their values are not identified, and are not
needed for any estimate. -/
theorem exists_besselJ0_phase_asymptotic :
    ∃ p q : ℝ, ∀ x : ℝ, 1 ≤ x →
      |Real.sqrt x * besselJ0 x - (p * Real.cos x + q * Real.sin x)| ≤ 18 * Real.sqrt 2 / x := by
  obtain ⟨L, hL⟩ := exists_besselW_limit
  refine ⟨L.re, L.im, fun x hx => ?_⟩
  have hexp : Complex.exp (-(Complex.I * (x : ℂ)))
      = (Real.cos x : ℂ) - (Real.sin x : ℂ) * Complex.I := by
    have h1 : -(Complex.I * (x : ℂ)) = (-(x : ℂ)) * Complex.I := by ring
    rw [h1, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]
    ring
  have hexpre : (L * Complex.exp (-(Complex.I * (x : ℂ)))).re
      = L.re * Real.cos x + L.im * Real.sin x := by
    rw [hexp]
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hdiff : Real.sqrt x * besselJ0 x - (L.re * Real.cos x + L.im * Real.sin x)
      = ((besselW x - L) * Complex.exp (-(Complex.I * (x : ℂ)))).re := by
    rw [sub_mul, Complex.sub_re, ← besselV_eq_re, hexpre, besselV]
  rw [hdiff]
  refine le_trans (Complex.abs_re_le_norm _) ?_
  rw [norm_mul]
  have hnorm : ‖Complex.exp (-(Complex.I * (x : ℂ)))‖ = 1 := by
    rw [show -(Complex.I * (x : ℂ)) = ((-x : ℝ) : ℂ) * Complex.I from by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I (-x)

  rw [hnorm, mul_one]
  exact hL x hx

end GaloisForLFunctions.RHTower

end
