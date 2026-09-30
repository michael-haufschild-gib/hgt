import GaloisForLFunctions.HTGeometry.HamburgerFunctionalEquation

/-!
# Hamburger's theorem under square summability

The Laplace–periodicity proof of Hamburger's theorem uses only `Σ ‖a_n‖/n² < ∞`. The partial
fractions `Σ a_n t/(π(n² + t²))` then converge absolutely, and the Laplace transform of the theta
series is summable termwise. This file restates the Laplace step, the periodicity law and the odd
vanishing theorem under that hypothesis (`coeff_eq_zero_of_odd_coeffTheta_relation_of_sq`). It
applies to coefficients growing like `n^{1-ε}` on average, beyond the absolute convergence
abscissa `1`.
-/

open Complex MeasureTheory Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

theorem summable_sq_of_rpow_two {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ (2 : ℝ)) :
    Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ 2 :=
  ha.congr fun n => by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- **Laplace transform of a theta series.**  For `t > 0`,
`∫₀^∞ θ_a(x) e^{-π t² x} dx = Σ_{n≥1} a_n / (π (n² + t²))`. -/
theorem hasSum_integral_coeffTheta_mul_exp_of_sq (a : ℕ → ℂ)
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ (2 : ℝ))
    {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => a (n + 1) / ((Real.pi * (((n : ℝ) + 1) ^ 2 + t ^ 2) : ℝ) : ℂ))
      (∫ x in Ioi (0 : ℝ), coeffTheta a x * ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ)) := by
  set F : ℕ → ℝ → ℂ := fun n x =>
    a (n + 1) * ((Real.exp (-(Real.pi * (((n : ℝ) + 1) ^ 2 + t ^ 2)) * x) : ℝ) : ℂ) with hF
  have hk : ∀ n : ℕ, 0 < Real.pi * (((n : ℝ) + 1) ^ 2 + t ^ 2) := fun n => by positivity
  have hFint : ∀ n : ℕ, Integrable (F n) (volume.restrict (Ioi 0)) := fun n =>
    ((integrableOn_Ioi_exp_neg_mul (hk n)).ofReal).const_mul _
  have hFnorm : ∀ n : ℕ, ∫ x in Ioi (0 : ℝ), ‖F n x‖ =
      ‖a (n + 1)‖ / (Real.pi * (((n : ℝ) + 1) ^ 2 + t ^ 2)) := by
    intro n
    have : ∀ x : ℝ, ‖F n x‖ = ‖a (n + 1)‖ *
        Real.exp (-(Real.pi * (((n : ℝ) + 1) ^ 2 + t ^ 2)) * x) := by
      intro x
      rw [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    simp_rw [this]
    rw [integral_const_mul, integral_Ioi_exp_neg_mul (hk n), mul_one_div]
  have hsum : Summable fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖F n x‖ := by
    simp_rw [hFnorm]
    refine (ha.mul_left (1 / Real.pi)).of_nonneg_of_le
      (fun n => div_nonneg (norm_nonneg _) (hk n).le) fun n => ?_
    have hn : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
    rw [show (((n : ℝ) + 1) ^ (2 : ℝ)) = ((n : ℝ) + 1) ^ 2 by norm_cast]
    rw [div_le_iff₀ (hk n)]
    calc ‖a (n + 1)‖ = 1 / Real.pi * (‖a (n + 1)‖ / ((n : ℝ) + 1) ^ 2) *
          (Real.pi * ((n : ℝ) + 1) ^ 2) := by field_simp
      _ ≤ 1 / Real.pi * (‖a (n + 1)‖ / ((n : ℝ) + 1) ^ 2) *
          (Real.pi * (((n : ℝ) + 1) ^ 2 + t ^ 2)) := by
        gcongr
        nlinarith [sq_nonneg t]
  have h := MeasureTheory.hasSum_integral_of_summable_integral_norm hFint hsum
  have hval : ∀ n : ℕ, ∫ x in Ioi (0 : ℝ), F n x =
      a (n + 1) / ((Real.pi * (((n : ℝ) + 1) ^ 2 + t ^ 2) : ℝ) : ℂ) := by
    intro n
    rw [hF, integral_const_mul, integral_complex_ofReal, integral_Ioi_exp_neg_mul (hk n)]
    push_cast
    ring
  have hsumF : ∀ x ∈ Ioi (0 : ℝ), ∑' n : ℕ, F n x =
      coeffTheta a x * ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ) := by
    intro x hx
    rw [coeffTheta, ← tsum_mul_right]
    refine tsum_congr fun n => ?_
    rw [hF, mul_assoc, ← ofReal_mul, ← Real.exp_add]
    ring_nf
  simp_rw [hval] at h
  rwa [setIntegral_congr_fun measurableSet_Ioi hsumF] at h


/-- **Laplace transform of the dual theta term.**  For `t > 0`,
`∫₀^∞ x^{-1/2} θ_b(1/x) e^{-π t² x} dx = Σ_{n≥1} b_n e^{-2π n t}/t`. -/
theorem hasSum_integral_dual_coeffTheta_mul_exp_of_sq (b : ℕ → ℂ)
    (hb : Summable fun n : ℕ => ‖b (n + 1)‖ / ((n : ℝ) + 1) ^ (2 : ℝ))
    {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => b (n + 1) *
        ((1 / t * Real.exp (-(2 * Real.pi * ((n : ℝ) + 1) * t)) : ℝ) : ℂ))
      (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b x⁻¹ *
        ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ)) := by
  set F : ℕ → ℝ → ℂ := fun n x => b (n + 1) * ((x ^ (-(1 / 2 : ℝ)) *
    Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 / x) - Real.pi * t ^ 2 * x) : ℝ) : ℂ) with hF
  have hm : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hFint : ∀ n : ℕ, Integrable (F n) (volume.restrict (Ioi 0)) := fun n =>
    ((integrableOn_rpow_neg_half_mul_exp_theta_dual (hm n) ht).ofReal).const_mul _
  have hFnorm : ∀ n : ℕ, ∫ x in Ioi (0 : ℝ), ‖F n x‖ =
      ‖b (n + 1)‖ * (1 / t * Real.exp (-(2 * Real.pi * ((n : ℝ) + 1) * t))) := by
    intro n
    have : ∀ x ∈ Ioi (0 : ℝ), ‖F n x‖ = ‖b (n + 1)‖ * (x ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 / x) - Real.pi * t ^ 2 * x)) := by
      intro x hx
      have hx0 : (0 : ℝ) < x := hx
      rw [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [setIntegral_congr_fun measurableSet_Ioi this, integral_const_mul,
      integral_rpow_neg_half_mul_exp_theta_dual (hm n) ht]
  have hsum : Summable fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖F n x‖ := by
    simp_rw [hFnorm]
    refine (hb.mul_left (1 / t / (2 * Real.pi ^ 2 * t ^ 2))).of_nonneg_of_le
      (fun n => by positivity) fun n => ?_
    have hy : 0 < 2 * Real.pi * ((n : ℝ) + 1) * t := by positivity
    have he := exp_neg_le_two_div_sq hy
    rw [show (((n : ℝ) + 1) ^ (2 : ℝ)) = ((n : ℝ) + 1) ^ 2 by norm_cast]
    calc ‖b (n + 1)‖ * (1 / t * Real.exp (-(2 * Real.pi * ((n : ℝ) + 1) * t)))
        ≤ ‖b (n + 1)‖ * (1 / t * (2 / (2 * Real.pi * ((n : ℝ) + 1) * t) ^ 2)) := by gcongr
      _ = 1 / t / (2 * Real.pi ^ 2 * t ^ 2) * (‖b (n + 1)‖ / ((n : ℝ) + 1) ^ 2) := by
        field_simp
  have h := MeasureTheory.hasSum_integral_of_summable_integral_norm hFint hsum
  have hval : ∀ n : ℕ, ∫ x in Ioi (0 : ℝ), F n x =
      b (n + 1) * ((1 / t * Real.exp (-(2 * Real.pi * ((n : ℝ) + 1) * t)) : ℝ) : ℂ) := by
    intro n
    rw [hF, integral_const_mul, integral_complex_ofReal,
      integral_rpow_neg_half_mul_exp_theta_dual (hm n) ht]
  have hsumF : ∀ x ∈ Ioi (0 : ℝ), ∑' n : ℕ, F n x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b x⁻¹ *
        ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hcpow : (x : ℂ) ^ (-(1 / 2 : ℂ)) = ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hx0.le]
      push_cast
      ring_nf
    rw [coeffTheta, ← tsum_mul_left, ← tsum_mul_right]
    refine tsum_congr fun n => ?_
    rw [hF, hcpow]
    beta_reduce
    rw [show -(Real.pi * ((n : ℝ) + 1) ^ 2 / x) - Real.pi * t ^ 2 * x =
      -Real.pi * ((n : ℝ) + 1) ^ 2 * x⁻¹ + -(Real.pi * t ^ 2) * x by ring, Real.exp_add]
    push_cast
    ring
  simp_rw [hval] at h
  rwa [setIntegral_congr_fun measurableSet_Ioi hsumF] at h


theorem integrableOn_dual_coeffTheta_mul_exp_of_sq (b : ℕ → ℂ)
    (hb : Summable fun n : ℕ => ‖b (n + 1)‖ / ((n : ℝ) + 1) ^ (2 : ℝ))
    {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b x⁻¹ *
      ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ)) (Ioi 0) := by
  have hS : Summable fun n : ℕ => ‖b (n + 1)‖ / ((n : ℝ) + 1) ^ (2 * (1 : ℝ)) :=
    by rw [mul_one]; exact hb
  set S : ℝ := ∑' n : ℕ, ‖b (n + 1)‖ / ((n : ℝ) + 1) ^ (2 * (1 : ℝ)) with hSdef
  have hdom : IntegrableOn (fun x : ℝ => x ^ (1 / 2 : ℝ) *
      Real.exp (-(Real.pi * t ^ 2) * x ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) le_rfl (by positivity)
  refine (hdom.const_mul (S / Real.pi)).mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun x hx => ?_))
  · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
    have hx0 : (0 : ℝ) < x := hx
    refine ContinuousAt.continuousWithinAt ?_
    refine ((continuousAt_ofReal_cpow_const _ _ (Or.inr hx0.ne')).mul ?_).mul ?_
    · exact ((continuousOn_coeffTheta b (by simpa using hS)).continuousAt
        (Ioi_mem_nhds (inv_pos.mpr hx0))).comp (continuousAt_inv₀ hx0.ne')
    · exact (by fun_prop : Continuous fun x : ℝ =>
        ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ)).continuousAt
  · have hx0 : (0 : ℝ) < x := hx
    have hθ := norm_coeffTheta_le b (inv_pos.mpr hx0) zero_le_one le_rfl hS
    rw [← hSdef, Real.rpow_neg_one] at hθ
    have hinv : (Real.pi * x⁻¹)⁻¹ = x / Real.pi := by field_simp
    rw [hinv] at hθ
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.rpow_one]
    have hre : (-(1 / 2 : ℂ)).re = -(1 / 2 : ℝ) := by norm_num
    rw [hre]
    have hpow : x ^ (-(1 / 2 : ℝ)) * x = x ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add_one hx0.ne']
      norm_num
    calc x ^ (-(1 / 2 : ℝ)) * ‖coeffTheta b x⁻¹‖ * Real.exp (-(Real.pi * t ^ 2) * x)
        ≤ x ^ (-(1 / 2 : ℝ)) * (x / Real.pi * S) * Real.exp (-(Real.pi * t ^ 2) * x) := by
          gcongr
      _ = S / Real.pi * (x ^ (-(1 / 2 : ℝ)) * x * Real.exp (-(Real.pi * t ^ 2) * x)) := by
          ring
      _ = S / Real.pi * (x ^ (1 / 2 : ℝ) * Real.exp (-(Real.pi * t ^ 2) * x)) := by rw [hpow]


/-- **The Hamburger identity on the positive axis.**  If
`θ_a(x) = ε x^{-1/2} θ_b(1/x) + α + β x^{-1/2}` for all `x > 0`, then for every real `t > 0`
`L_a(t) = ε Σ_{n≥1} b_n e^{-2π n t} + α/(π t) + β`, where `L_a(t) = Σ a_n t/(π(n² + t²))`.
Multiply the theta relation by `e^{-π t² x}` and integrate over `x > 0`: the left side gives
the partial fractions, and the dual side gives `e^{-2π n t}/t` by the half-integral Laplace–Bessel
formula. -/
theorem hamburgerSeries_eq_of_coeffTheta_relation_ofReal_of_sq (a b : ℕ → ℂ)
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ (2 : ℝ))
    (hb : Summable fun n : ℕ => ‖b (n + 1)‖ / ((n : ℝ) + 1) ^ (2 : ℝ))
    {ε α β : ℂ}
    (htheta : ∀ x : ℝ, 0 < x → coeffTheta a x =
      ε * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b x⁻¹) + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ)))
    {t : ℝ} (ht : 0 < t) :
    hamburgerSeries a t =
      ε * ∑' n : ℕ, b (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * t)) +
        α / (Real.pi * t) + β := by
  set e : ℝ → ℂ := fun x => ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ) with he_def
  have hB : 0 < Real.pi * t ^ 2 := by positivity
  have he_int : IntegrableOn e (Ioi 0) := (integrableOn_Ioi_exp_neg_mul hB).ofReal
  have hhe_eq : ∀ x ∈ Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x =
      ((x ^ ((1 / 2 : ℝ) - 1) * Real.exp (-((Real.pi * t ^ 2) * x)) : ℝ) : ℂ) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [he_def, Complex.ofReal_mul, Complex.ofReal_cpow hx0.le]
    push_cast
    ring_nf
  have hhe_int : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x) (Ioi 0) := by
    have h : IntegrableOn (fun x : ℝ => x ^ ((1 / 2 : ℝ) - 1) *
        Real.exp (-(Real.pi * t ^ 2) * x ^ (1 : ℝ))) (Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) le_rfl hB
    have h' : IntegrableOn (fun x : ℝ => ((x ^ ((1 / 2 : ℝ) - 1) *
        Real.exp (-((Real.pi * t ^ 2) * x)) : ℝ) : ℂ)) (Ioi 0) := by
      have := Integrable.ofReal (𝕜 := ℂ) h
      simp only [Real.rpow_one, neg_mul] at this
      exact this
    exact IntegrableOn.congr_fun h' (fun x hx => (hhe_eq x hx).symm) measurableSet_Ioi
  have hD_int := integrableOn_dual_coeffTheta_mul_exp_of_sq b hb ht
  have hI0 : ∫ x in Ioi (0 : ℝ), e x = ((1 / (Real.pi * t ^ 2) : ℝ) : ℂ) := by
    rw [he_def, integral_complex_ofReal, integral_Ioi_exp_neg_mul hB]
  have hIh : ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x = ((1 / t : ℝ) : ℂ) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hhe_eq, integral_complex_ofReal,
      integral_Ioi_rpow_neg_half_mul_exp_neg_mul_sq ht]
  have hpt : ∀ x ∈ Ioi (0 : ℝ), coeffTheta a x * e x =
      ε * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b x⁻¹ * e x) +
        (α * e x + β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * e x)) := by
    intro x hx
    rw [htheta x hx]
    ring
  have hsplit : ∫ x in Ioi (0 : ℝ), coeffTheta a x * e x =
      ε * (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b x⁻¹ * e x) +
        (α * ∫ x in Ioi (0 : ℝ), e x) +
          β * ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x := by
    have h1 : ∫ x in Ioi (0 : ℝ), (ε * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b x⁻¹ * e x) +
        (α * e x + β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * e x))) =
        (∫ x in Ioi (0 : ℝ), ε * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b x⁻¹ * e x)) +
          ∫ x in Ioi (0 : ℝ), (α * e x + β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * e x)) :=
      integral_add (hD_int.const_mul ε) ((he_int.const_mul α).add (hhe_int.const_mul β))
    have h2 : ∫ x in Ioi (0 : ℝ), (α * e x + β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * e x)) =
        (∫ x in Ioi (0 : ℝ), α * e x) +
          ∫ x in Ioi (0 : ℝ), β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * e x) :=
      integral_add (he_int.const_mul α) (hhe_int.const_mul β)
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, h1, h2, integral_const_mul,
      integral_const_mul, integral_const_mul]
    ring
  have hL := (hasSum_integral_coeffTheta_mul_exp_of_sq a ha ht).tsum_eq
  have hD := (hasSum_integral_dual_coeffTheta_mul_exp_of_sq b hb ht).tsum_eq
  rw [hsplit, ← hD, hI0, hIh] at hL
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hham : hamburgerSeries a t = (t : ℂ) * ∑' n : ℕ,
      a (n + 1) / ((Real.pi * (((n : ℝ) + 1) ^ 2 + t ^ 2) : ℝ) : ℂ) := by
    rw [hamburgerSeries, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    push_cast
    ring
  have hdual : ∑' n : ℕ, b (n + 1) *
      ((1 / t * Real.exp (-(2 * Real.pi * ((n : ℝ) + 1) * t)) : ℝ) : ℂ) =
      (1 / (t : ℂ)) * ∑' n : ℕ, b (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * t)) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    push_cast
    ring
  rw [hham, hL, hdual]
  push_cast
  field_simp


/-- **The Hamburger identity on the right half-plane.**  Under the theta relation
`θ_a(x) = ε x^{-1/2} θ_b(1/x) + α + β x^{-1/2}`, for every `t` with `Re t > 0`
`L_a(t) = ε Σ_{n≥1} b_n e^{-2π n t} + α/(π t) + β`.  Both sides are holomorphic on the
half-plane and agree on the positive axis. -/
theorem hamburgerSeries_eq_of_coeffTheta_relation_of_sq (a b : ℕ → ℂ)
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ (2 : ℝ))
    (hb : Summable fun n : ℕ => ‖b (n + 1)‖ / ((n : ℝ) + 1) ^ (2 : ℝ))
    {ε α β : ℂ}
    (htheta : ∀ x : ℝ, 0 < x → coeffTheta a x =
      ε * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b x⁻¹) + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ)))
    {t : ℂ} (ht : 0 < t.re) :
    hamburgerSeries a t =
      ε * ∑' n : ℕ, b (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * t)) +
        α / (Real.pi * t) + β := by
  set U : Set ℂ := {t : ℂ | 0 < t.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have ha2 : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have := summable_sq_of_rpow_two ha
    simpa using this
  have hf : AnalyticOnNhd ℂ (hamburgerSeries a) U :=
    (differentiableOn_hamburgerSeries ha2).analyticOnNhd hUo
  have hg : AnalyticOnNhd ℂ (fun t : ℂ => ε * ∑' n : ℕ, b (n + 1) *
      cexp (-(2 * Real.pi * ((n : ℂ) + 1) * t)) + α / (Real.pi * t) + β) U := by
    refine DifferentiableOn.analyticOnNhd ?_ hUo
    refine (((differentiableOn_expDualSeries (summable_sq_of_rpow_two hb)).const_mul ε).add
      ?_).add (differentiableOn_const _)
    refine DifferentiableOn.div (differentiableOn_const _) (by fun_prop) fun t ht => ?_
    have ht' : 0 < t.re := ht
    refine mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) fun h => ?_
    rw [h, zero_re] at ht'
    exact lt_irrefl _ ht'
  have h1U : (1 : ℂ) ∈ U := by simp [hU]
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), hamburgerSeries a z = ε * ∑' n : ℕ, b (n + 1) *
      cexp (-(2 * Real.pi * ((n : ℂ) + 1) * z)) + α / (Real.pi * z) + β := by
    set u : ℕ → ℂ := fun k => ((1 + 1 / ((k : ℝ) + 1) : ℝ) : ℂ) with hu
    have hlim : Tendsto u atTop (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
      · have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (1 : ℝ)
        rw [add_zero] at h
        have h2 := (Complex.continuous_ofReal.tendsto 1).comp h
        rw [Complex.ofReal_one] at h2
        exact h2
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, hu]
        intro h
        have h' : (1 + 1 / ((k : ℝ) + 1) : ℝ) = 1 := by exact_mod_cast h
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
    refine hlim.frequently (Frequently.of_forall fun k => ?_)
    have hk : (0 : ℝ) < 1 + 1 / ((k : ℝ) + 1) := by positivity
    exact hamburgerSeries_eq_of_coeffTheta_relation_ofReal_of_sq a b ha hb htheta hk
  exact hf.eqOn_of_preconnected_of_frequently_eq hg (convex_halfSpace_re_gt 0).isPreconnected
    h1U hfreq ht


/-- Under the theta relation the Hamburger series is `i`-periodic up to the pole of `α/(π t)`. -/
theorem hamburgerSeries_periodic_of_coeffTheta_relation_of_sq (a b : ℕ → ℂ)
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ (2 : ℝ))
    (hb : Summable fun n : ℕ => ‖b (n + 1)‖ / ((n : ℝ) + 1) ^ (2 : ℝ))
    {ε α β : ℂ}
    (htheta : ∀ x : ℝ, 0 < x → coeffTheta a x =
      ε * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b x⁻¹) + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ)))
    {t : ℂ} (ht : 0 < t.re) :
    hamburgerSeries a (t + I) - hamburgerSeries a t =
      α / Real.pi / (t + I) - α / Real.pi / t := by
  have ht' : 0 < (t + I).re := by simpa using ht
  rw [hamburgerSeries_eq_of_coeffTheta_relation_of_sq a b ha hb htheta ht',
    hamburgerSeries_eq_of_coeffTheta_relation_of_sq a b ha hb htheta ht]
  have hper : ∑' n : ℕ, b (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * (t + I))) =
      ∑' n : ℕ, b (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * t)) := by
    refine tsum_congr fun n => ?_
    rw [show -(2 * (Real.pi : ℂ) * ((n : ℂ) + 1) * (t + I)) =
      -(2 * Real.pi * ((n : ℂ) + 1) * t) + ((-((n : ℤ) + 1) : ℤ) : ℂ) * (2 * Real.pi * I) by
        push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hper, div_div, div_div]
  ring


/-- **Hamburger's conclusion from the theta relation.**  If the theta series of `a` satisfies
`θ_a(x) = ε x^{-1/2} θ_b(1/x) + α + β x^{-1/2}` for all `x > 0`, then every coefficient of `a`
equals `-2α`.  This is the Laplace–periodicity half of Hamburger's theorem, with the theta relation
as hypothesis. -/
theorem coeff_eq_of_coeffTheta_relation_of_sq {a b : ℕ → ℂ} {α β ε : ℂ}
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ (2 : ℝ))
    (hb : Summable fun n : ℕ => ‖b (n + 1)‖ / ((n : ℝ) + 1) ^ (2 : ℝ))
    (htheta : ∀ x : ℝ, 0 < x → coeffTheta a x =
      ε * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b x⁻¹) + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ)))
    (n : ℕ) : a (n + 1) = -(2 * α) := by
  have ha2 : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have := summable_sq_of_rpow_two ha
    simpa using this
  have h := coeff_eq_of_hamburgerSeries_periodic_re_pos ha2 (α / Real.pi)
    (fun t ht => hamburgerSeries_periodic_of_coeffTheta_relation_of_sq a b ha hb htheta ht) n
  rw [h]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp


/-- **The odd theta relation forces vanishing.**  If `θ_a(x) = -x^{-1/2} θ_a(1/x) + α + β x^{-1/2}`
for all `x > 0`, then `a_n = 0` for every `n ≥ 1`.  All coefficients equal `-2α` by Hamburger's
periodicity argument.  The relation at `x = 4` and `x = 1/4` forces `α = β`, and at `x = 1` it
gives `α (1 + 2 Σ e^{-π n²}) = 0`. -/
theorem coeff_eq_zero_of_odd_coeffTheta_relation_of_sq {a : ℕ → ℂ} {α β : ℂ}
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ (2 : ℝ))
    (htheta : ∀ x : ℝ, 0 < x → coeffTheta a x =
      (-1) * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta a x⁻¹) + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ)))
    (n : ℕ) : a (n + 1) = 0 := by
  have hcoeff : ∀ m : ℕ, a (m + 1) = -(2 * α) :=
    coeff_eq_of_coeffTheta_relation_of_sq ha ha htheta
  have h4 : ((4 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) = 1 / 2 := by
    have := ofReal_sq_cpow_neg_half (c := 2) (by norm_num)
    norm_num at this ⊢
    exact this
  have h14 : ((1 / 4 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) = 2 := by
    have := ofReal_sq_cpow_neg_half (c := 1 / 2) (by norm_num)
    norm_num at this ⊢
    exact this
  have E4 := htheta 4 (by norm_num)
  have E14 := htheta (1 / 4) (by norm_num)
  rw [h4, show ((4 : ℝ))⁻¹ = 1 / 4 by norm_num] at E4
  rw [h14, show ((1 / 4 : ℝ))⁻¹ = 4 by norm_num] at E14
  have hαβ : α = β := by linear_combination E14 - 2 * E4
  have E1 := htheta 1 one_pos
  rw [Complex.ofReal_one, Complex.one_cpow, inv_one] at E1
  rw [← hαβ] at E1
  have hθ1 : coeffTheta a 1 = α := by linear_combination E1 / 2
  set S : ℝ := ∑' m : ℕ, Real.exp (-Real.pi * ((m : ℝ) + 1) ^ 2 * 1) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun m => (Real.exp_pos _).le
  have hθS : coeffTheta a 1 = -(2 * α) * (S : ℂ) := by
    rw [coeffTheta, hS, Complex.ofReal_tsum, ← tsum_mul_left]
    exact tsum_congr fun m => by rw [hcoeff m]
  have hα : α = 0 := by
    have h1 : α * (1 + 2 * (S : ℂ)) = 0 := by linear_combination hθS - hθ1
    have h2 : (1 + 2 * (S : ℂ)) ≠ 0 := by
      have : (0 : ℝ) < 1 + 2 * S := by linarith
      exact_mod_cast this.ne'
    exact (mul_eq_zero.mp h1).resolve_right h2
  rw [hcoeff n, hα]
  ring


end GaloisForLFunctions.HTGeometry
