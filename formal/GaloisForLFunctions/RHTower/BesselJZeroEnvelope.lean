import GaloisForLFunctions.RHTower.VanDerCorput

/-!
# The Bessel function of order zero and its envelope decay

The Bessel function of the first kind of order zero is defined by Bessel's integral representation

```text
J_0(u) = (1/pi) int_0^pi cos(u sin θ) dθ,
```

and the two elementary bounds it obeys are proved here:

* `abs_besselJ0_le_one` — the trivial bound `|J_0| <= 1`, from the representation alone.
* **`abs_besselJ0_le_envelope`** — the envelope decay `|J_0(u)| <= 72 sqrt 2 / sqrt u` for `u >= 1`.
  The proof is a two-block van der Corput split of the half-period integral: on `[0, pi/4]` the phase
  derivative `u cos θ` is bounded below by `u sqrt 2 / 2` and the first-derivative test gives `O(1/u)`;
  on `[pi/4, pi/2]` the stationary point of `u sin θ` sits at the right endpoint and the second
  derivative `u sin θ` is bounded below by `u/2`, so the second-derivative test gives `O(1/sqrt u)`.
  The `1/sqrt u` block is the dominant one, and it is exactly the square-root loss of a nondegenerate
  stationary point.

The auxiliary phase objects `besselPhase`, its two derivatives and `besselJ0_eq_two_div_pi_mul` (the
reflection `θ ↦ pi - θ` folding the representation onto a quarter period) are the only intermediate
data.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory intervalIntegral

/-! ## The representation and its trivial bound -/

/-- The Bessel function of the first kind of order zero, in Bessel's integral representation. -/
def besselJ0 (u : ℝ) : ℝ := (1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi, Real.cos (u * Real.sin θ)

theorem continuous_cos_mul_sin (u : ℝ) : Continuous fun θ : ℝ => Real.cos (u * Real.sin θ) := by
  fun_prop

theorem besselJ0_zero : besselJ0 0 = 1 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [besselJ0]
  norm_num

theorem besselJ0_neg (u : ℝ) : besselJ0 (-u) = besselJ0 u := by
  rw [besselJ0, besselJ0]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [neg_mul, Real.cos_neg]

/-- The trivial bound `|J_0| ≤ 1`. -/
theorem abs_besselJ0_le_one (u : ℝ) : |besselJ0 u| ≤ 1 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hbd : ‖∫ θ in (0 : ℝ)..Real.pi, Real.cos (u * Real.sin θ)‖ ≤ 1 * |Real.pi - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => ?_
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  rw [Real.norm_eq_abs] at hbd
  rw [besselJ0, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / Real.pi)]
  have hval : |Real.pi - 0| = Real.pi := by
    rw [sub_zero, abs_of_pos hpi]
  rw [hval, one_mul] at hbd
  calc 1 / Real.pi * |∫ θ in (0 : ℝ)..Real.pi, Real.cos (u * Real.sin θ)|
      ≤ 1 / Real.pi * Real.pi := by
        exact mul_le_mul_of_nonneg_left hbd (by positivity)
    _ = 1 := by field_simp

/-! ## Folding onto a quarter period -/

/-- The reflection `θ ↦ pi - θ` identifies the two halves of the representation, so `J_0` is a
quarter-period integral. -/
theorem besselJ0_eq_two_div_pi_mul (u : ℝ) :
    besselJ0 u = (2 / Real.pi) * ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos (u * Real.sin θ) := by
  have hcont := continuous_cos_mul_sin u
  have hsplit : (∫ θ in (0 : ℝ)..Real.pi, Real.cos (u * Real.sin θ))
      = (∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos (u * Real.sin θ))
        + ∫ θ in (Real.pi / 2)..Real.pi, Real.cos (u * Real.sin θ) :=
    (intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)).symm
  have hrefl : (∫ θ in (Real.pi / 2)..Real.pi, Real.cos (u * Real.sin θ))
      = ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos (u * Real.sin θ) := by
    have h := intervalIntegral.integral_comp_sub_left
      (fun θ : ℝ => Real.cos (u * Real.sin θ)) Real.pi (a := 0) (b := Real.pi / 2)
    have hendpoints : Real.pi - Real.pi / 2 = Real.pi / 2 ∧ Real.pi - 0 = Real.pi := by
      constructor <;> ring
    rw [hendpoints.1, hendpoints.2] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [Real.sin_pi_sub]
  rw [besselJ0, hsplit, hrefl]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-! ## The phase and its derivatives -/

/-- The phase of the Bessel representation, signed so that its second derivative is nonnegative on
the quarter period. -/
def besselPhase (u θ : ℝ) : ℝ := -(u * Real.sin θ)

theorem hasDerivAt_besselPhase (u θ : ℝ) :
    HasDerivAt (besselPhase u) (-(u * Real.cos θ)) θ := by
  have h : HasDerivAt (fun θ : ℝ => u * Real.sin θ) (u * Real.cos θ) θ :=
    (Real.hasDerivAt_sin θ).const_mul u
  exact h.neg

theorem deriv_besselPhase (u : ℝ) : deriv (besselPhase u) = fun θ => -(u * Real.cos θ) :=
  funext fun θ => (hasDerivAt_besselPhase u θ).deriv

theorem hasDerivAt_deriv_besselPhase (u θ : ℝ) :
    HasDerivAt (deriv (besselPhase u)) (u * Real.sin θ) θ := by
  rw [deriv_besselPhase]
  have h : HasDerivAt (fun θ : ℝ => u * Real.cos θ) (u * -Real.sin θ) θ :=
    (Real.hasDerivAt_cos θ).const_mul u
  have h2 := h.neg
  rw [show -(u * -Real.sin θ) = u * Real.sin θ from by ring] at h2
  exact h2

theorem deriv_deriv_besselPhase (u : ℝ) :
    deriv (deriv (besselPhase u)) = fun θ => u * Real.sin θ :=
  funext fun θ => (hasDerivAt_deriv_besselPhase u θ).deriv

theorem contDiff_besselPhase (u : ℝ) : ContDiff ℝ 2 (besselPhase u) := by
  show ContDiff ℝ 2 fun θ : ℝ => -(u * Real.sin θ)
  exact (contDiff_const.mul Real.contDiff_sin).neg

/-- The complex integrand of the van der Corput tests, with unit amplitude. -/
theorem continuous_besselIntegrand (u : ℝ) :
    Continuous fun θ : ℝ => (1 : ℂ) * Complex.exp (Complex.I * (besselPhase u θ : ℂ)) := by
  refine continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul ?_))
  exact Complex.continuous_ofReal.comp (by unfold besselPhase; fun_prop)

/-- The real cosine integral is the real part of the unit-amplitude phase integral. -/
theorem integral_cos_eq_re_phase (u a b : ℝ) :
    (∫ θ in a..b, Real.cos (u * Real.sin θ))
      = (∫ θ in a..b, (1 : ℂ) * Complex.exp (Complex.I * (besselPhase u θ : ℂ))).re := by
  have hint : IntervalIntegrable
      (fun θ : ℝ => (1 : ℂ) * Complex.exp (Complex.I * (besselPhase u θ : ℂ))) volume a b :=
    (continuous_besselIntegrand u).intervalIntegrable _ _
  have h := ContinuousLinearMap.intervalIntegral_comp_comm (Complex.reCLM) hint
  rw [Complex.reCLM_apply] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hre : ((1 : ℂ) * Complex.exp (Complex.I * (besselPhase u θ : ℂ))).re
      = Real.cos (besselPhase u θ) := by
    rw [one_mul, mul_comm Complex.I, Complex.exp_ofReal_mul_I_re]
  rw [Complex.reCLM_apply, hre, besselPhase, Real.cos_neg]

/-! ## The two van der Corput blocks -/

/-- On `[0, pi/4]` the phase derivative `u cos θ` is bounded below, so the first-derivative test
gives a bound of order `1/u`. -/
theorem norm_integral_besselPhase_first {u : ℝ} (hu : 0 < u) :
    ‖∫ θ in (0 : ℝ)..(Real.pi / 4), (1 : ℂ) * Complex.exp (Complex.I * (besselPhase u θ : ℂ))‖
      ≤ 8 * Real.sqrt 2 / u := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hab : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  set lam : ℝ := u * (Real.sqrt 2 / 2) with hlam
  have hlampos : 0 < lam := by
    rw [hlam]; positivity
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
  have hA : ContDiff ℝ 1 (fun _ : ℝ => (1 : ℂ)) := contDiff_const
  have h := _root_.RHTower.firstDerivTest (φ := besselPhase u) (A := fun _ : ℝ => (1 : ℂ))
    hab hlampos (contDiff_besselPhase u) hnn hbound hA
  have hzero : (∫ t in (0 : ℝ)..(Real.pi / 4), ‖deriv (fun _ : ℝ => (1 : ℂ)) t‖) = 0 := by
    simp
  rw [hzero] at h
  refine h.trans ?_
  rw [norm_one, hlam]
  rw [div_le_div_iff₀ (by positivity) hu]
  nlinarith [hs2pos, hs2, hu.le]

/-- On `[pi/4, pi/2]` the second derivative `u sin θ` is bounded below, so the second-derivative test
gives a bound of order `1/sqrt u`.  This is the block that carries the envelope. -/
theorem norm_integral_besselPhase_second {u : ℝ} (hu : 0 < u) :
    ‖∫ θ in (Real.pi / 4)..(Real.pi / 2),
        (1 : ℂ) * Complex.exp (Complex.I * (besselPhase u θ : ℂ))‖
      ≤ 64 * Real.sqrt 2 / Real.sqrt u := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hab : Real.pi / 4 ≤ Real.pi / 2 := by linarith
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2le : (1 : ℝ) ≤ Real.sqrt 2 := by nlinarith
  have hmupos : (0 : ℝ) < u / 2 := by positivity
  have hbound : ∀ t ∈ Set.Icc (Real.pi / 4) (Real.pi / 2),
      u / 2 ≤ deriv (deriv (besselPhase u)) t := by
    intro t ht
    rw [deriv_deriv_besselPhase]
    have hsin : Real.sqrt 2 / 2 ≤ Real.sin t := by
      have h := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) ht.2 ht.1
      rwa [Real.sin_pi_div_four] at h
    have hhalf : (1 : ℝ) / 2 ≤ Real.sin t := le_trans (by linarith) hsin
    calc u / 2 = u * (1 / 2) := by ring
      _ ≤ u * Real.sin t := mul_le_mul_of_nonneg_left hhalf hu.le
  have hA : ContDiff ℝ 1 (fun _ : ℝ => (1 : ℂ)) := contDiff_const
  have h := _root_.RHTower.secondDerivTest (φ := besselPhase u) (A := fun _ : ℝ => (1 : ℂ))
    hab hmupos (contDiff_besselPhase u) hbound hA
  have hzero : (∫ t in (Real.pi / 4)..(Real.pi / 2), ‖deriv (fun _ : ℝ => (1 : ℂ)) t‖) = 0 := by
    simp
  rw [hzero] at h
  refine h.trans ?_
  rw [norm_one]
  have hsqrt : Real.sqrt (u / 2) = Real.sqrt u / Real.sqrt 2 := Real.sqrt_div hu.le 2
  have hupos : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.mpr hu
  rw [hsqrt]
  rw [div_div_eq_mul_div, div_le_div_iff₀ (by positivity) hupos]
  nlinarith [hs2, hs2pos, hupos.le]

/-! ## The envelope -/

theorem sqrt_le_self_of_one_le {u : ℝ} (hu : 1 ≤ u) : Real.sqrt u ≤ u := by
  nlinarith [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ u), Real.sqrt_nonneg u,
    Real.one_le_sqrt.mpr hu]

/-- The quarter-period integral obeys the square-root envelope. -/
theorem abs_integral_quarterPeriod_le {u : ℝ} (hu : 1 ≤ u) :
    |∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos (u * Real.sin θ)|
      ≤ 72 * Real.sqrt 2 / Real.sqrt u := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu
  have hupos : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.mpr hu0
  have hint : ∀ a b : ℝ, IntervalIntegrable
      (fun θ : ℝ => (1 : ℂ) * Complex.exp (Complex.I * (besselPhase u θ : ℂ))) volume a b :=
    fun a b => (continuous_besselIntegrand u).intervalIntegrable a b
  have hsplit : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        (1 : ℂ) * Complex.exp (Complex.I * (besselPhase u θ : ℂ)))
      = (∫ θ in (0 : ℝ)..(Real.pi / 4),
          (1 : ℂ) * Complex.exp (Complex.I * (besselPhase u θ : ℂ)))
        + ∫ θ in (Real.pi / 4)..(Real.pi / 2),
            (1 : ℂ) * Complex.exp (Complex.I * (besselPhase u θ : ℂ)) :=
    (intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)).symm
  rw [integral_cos_eq_re_phase]
  refine le_trans (Complex.abs_re_le_norm _) ?_
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have h1 := norm_integral_besselPhase_first hu0
  have h2 := norm_integral_besselPhase_second hu0
  have hfirst : 8 * Real.sqrt 2 / u ≤ 8 * Real.sqrt 2 / Real.sqrt u := by
    have := sqrt_le_self_of_one_le hu
    gcongr
  have hsum : 8 * Real.sqrt 2 / Real.sqrt u + 64 * Real.sqrt 2 / Real.sqrt u
      = 72 * Real.sqrt 2 / Real.sqrt u := by
    field_simp
    ring
  linarith [h1, h2, hfirst, hsum]

/-- **The envelope bound.**  For `u ≥ 1` the Bessel function of order zero decays like `u^{-1/2}`,
with the explicit constant `72 sqrt 2`.  The exponent is the square-root loss of the single
nondegenerate stationary point of `u sin θ` at `θ = pi/2`. -/
theorem abs_besselJ0_le_envelope {u : ℝ} (hu : 1 ≤ u) :
    |besselJ0 u| ≤ 72 * Real.sqrt 2 / Real.sqrt u := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu
  have hupos : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.mpr hu0
  have hfac : (2 : ℝ) / Real.pi ≤ 1 := by
    rw [div_le_one hpi]
    linarith [Real.pi_gt_three]
  rw [besselJ0_eq_two_div_pi_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / Real.pi)]
  have hbase := abs_integral_quarterPeriod_le hu
  have habs : (0 : ℝ) ≤ |∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos (u * Real.sin θ)| := abs_nonneg _
  calc (2 / Real.pi) * |∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos (u * Real.sin θ)|
      ≤ 1 * |∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos (u * Real.sin θ)| :=
        mul_le_mul_of_nonneg_right hfac habs
    _ = |∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos (u * Real.sin θ)| := one_mul _
    _ ≤ 72 * Real.sqrt 2 / Real.sqrt u := hbase

/-- The two bounds together: the Bessel envelope is `min(1, C u^{-1/2})`. -/
theorem abs_besselJ0_le_min {u : ℝ} (hu : 1 ≤ u) :
    |besselJ0 u| ≤ 1 ∧ |besselJ0 u| ≤ 72 * Real.sqrt 2 / Real.sqrt u :=
  ⟨abs_besselJ0_le_one u, abs_besselJ0_le_envelope hu⟩

end GaloisForLFunctions.RHTower

end
