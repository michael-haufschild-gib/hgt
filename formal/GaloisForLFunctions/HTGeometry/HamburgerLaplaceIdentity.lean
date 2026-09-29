import GaloisForLFunctions.HTGeometry.DirichletCoefficientTheta
import GaloisForLFunctions.HTGeometry.LaplaceBesselHalfIntegral
import GaloisForLFunctions.HTGeometry.HamburgerPeriodicityResidue

/-!
# The Laplace step of Hamburger's theorem

Suppose the theta series `θ_a(x) = Σ_{n≥1} a_n e^{-π n² x}` satisfies a transformation law
`θ_a(x) = ε x^{-1/2} θ_b(1/x) + α + β x^{-1/2}`.  Multiply by `e^{-π t² x}` and integrate over
`x > 0`.  The left side gives the partial fractions `Σ a_n/(π(n² + t²))`
(`hasSum_integral_coeffTheta_mul_exp`).  The dual side gives `Σ b_n e^{-2π n t}/t`, by the
half-integral Laplace–Bessel formula (`hasSum_integral_dual_coeffTheta_mul_exp`).  So for `t > 0`

`L_a(t) = ε Σ_{n≥1} b_n e^{-2π n t} + α/(π t) + β`,   `L_a(t) = Σ a_n t/(π(n² + t²))`

(`hamburgerSeries_eq_of_coeffTheta_relation_ofReal`).  Both sides are holomorphic on `Re t > 0`
(`differentiableOn_hamburgerSeries`, `differentiableOn_expDualSeries`), so the identity holds on
the whole right half-plane (`hamburgerSeries_eq_of_coeffTheta_relation`).  Its right side is
`i`-periodic apart from `α/(π t)`.  This is what forces the Dirichlet coefficients to be constant.
-/

open Complex MeasureTheory Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- `∫₀^∞ e^{-k x} dx = 1/k`. -/
theorem integral_Ioi_exp_neg_mul {k : ℝ} (hk : 0 < k) :
    ∫ x in Ioi (0 : ℝ), Real.exp (-k * x) = 1 / k := by
  rw [integral_exp_mul_Ioi (by linarith) 0, mul_zero, Real.exp_zero, neg_div_neg_eq]

theorem integrableOn_Ioi_exp_neg_mul {k : ℝ} (hk : 0 < k) :
    IntegrableOn (fun x : ℝ => Real.exp (-k * x)) (Ioi 0) :=
  integrableOn_exp_mul_Ioi (by linarith) 0

/-- **Laplace transform of a theta series.**  For `t > 0`,
`∫₀^∞ θ_a(x) e^{-π t² x} dx = Σ_{n≥1} a_n / (π (n² + t²))`. -/
theorem hasSum_integral_coeffTheta_mul_exp (a : ℕ → ℂ)
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
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
    refine ((ha 2 (by norm_num)).mul_left (1 / Real.pi)).of_nonneg_of_le
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

/-- `e^{-y} ≤ 2/y²` for `y > 0`. -/
theorem exp_neg_le_two_div_sq {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ 2 / y ^ 2 := by
  have h := Real.quadratic_le_exp_of_nonneg hy.le
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos y) (by positivity)]
  nlinarith

/-- The one-term dual Laplace integral:
`∫₀^∞ x^{-1/2} e^{-π m²/x - π t² x} dx = e^{-2π m t}/t` for `m, t > 0`. -/
theorem integral_rpow_neg_half_mul_exp_theta_dual {m t : ℝ} (hm : 0 < m) (ht : 0 < t) :
    ∫ x in Ioi (0 : ℝ), x ^ (-(1 / 2 : ℝ)) *
      Real.exp (-(Real.pi * m ^ 2 / x) - Real.pi * t ^ 2 * x) =
      1 / t * Real.exp (-(2 * Real.pi * m * t)) := by
  rw [integral_rpow_neg_half_mul_exp_neg_div_sub_mul (by positivity) (by positivity)]
  have h1 : √(Real.pi / (Real.pi * t ^ 2)) = 1 / t := by
    rw [show Real.pi / (Real.pi * t ^ 2) = (1 / t) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)
  have h2 : √(Real.pi * m ^ 2 * (Real.pi * t ^ 2)) = Real.pi * m * t := by
    rw [show Real.pi * m ^ 2 * (Real.pi * t ^ 2) = (Real.pi * m * t) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  rw [h1, h2]
  ring_nf

theorem integrableOn_rpow_neg_half_mul_exp_theta_dual {m t : ℝ} (hm : 0 < m) (ht : 0 < t) :
    IntegrableOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ)) *
      Real.exp (-(Real.pi * m ^ 2 / x) - Real.pi * t ^ 2 * x)) (Ioi 0) := by
  have hdom : IntegrableOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ)) *
      Real.exp (-(Real.pi * t ^ 2) * x ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) le_rfl (by positivity)
  refine hdom.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall
    fun x hx => ?_))
  · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
    have hx0 : (0 : ℝ) < x := hx
    refine ContinuousAt.continuousWithinAt ?_
    refine (Real.continuousAt_rpow_const _ _ (Or.inl hx0.ne')).mul ?_
    refine Real.continuous_exp.continuousAt.comp ?_
    exact ((continuousAt_const.div continuousAt_id hx0.ne').neg).sub
      (continuousAt_const.mul continuousAt_id)
  · have hx0 : (0 : ℝ) < x := hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_one]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    have : 0 ≤ Real.pi * m ^ 2 / x := by positivity
    linarith

/-- **Laplace transform of the dual theta term.**  For `t > 0`,
`∫₀^∞ x^{-1/2} θ_b(1/x) e^{-π t² x} dx = Σ_{n≥1} b_n e^{-2π n t}/t`. -/
theorem hasSum_integral_dual_coeffTheta_mul_exp (b : ℕ → ℂ)
    (hb : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖b (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
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
    refine ((hb 2 (by norm_num)).mul_left (1 / t / (2 * Real.pi ^ 2 * t ^ 2))).of_nonneg_of_le
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

theorem integrableOn_dual_coeffTheta_mul_exp (b : ℕ → ℂ)
    (hb : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖b (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b x⁻¹ *
      ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ)) (Ioi 0) := by
  have hS : Summable fun n : ℕ => ‖b (n + 1)‖ / ((n : ℝ) + 1) ^ (2 * (1 : ℝ)) :=
    hb _ (by norm_num)
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

theorem integral_Ioi_rpow_neg_half_mul_exp_neg_mul_sq {t : ℝ} (ht : 0 < t) :
    ∫ x in Ioi (0 : ℝ), x ^ ((1 / 2 : ℝ) - 1) * Real.exp (-((Real.pi * t ^ 2) * x)) = 1 / t := by
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) (by positivity),
    Real.Gamma_one_half_eq, ← Real.sqrt_eq_rpow,
    ← Real.sqrt_mul (by positivity)]
  rw [show 1 / (Real.pi * t ^ 2) * Real.pi = (1 / t) ^ 2 by field_simp]
  exact Real.sqrt_sq (by positivity)

/-- **The Hamburger identity on the positive axis.**  If
`θ_a(x) = ε x^{-1/2} θ_b(1/x) + α + β x^{-1/2}` for all `x > 0`, then for every real `t > 0`
`L_a(t) = ε Σ_{n≥1} b_n e^{-2π n t} + α/(π t) + β`, where `L_a(t) = Σ a_n t/(π(n² + t²))`.
Multiply the theta relation by `e^{-π t² x}` and integrate over `x > 0`: the left side gives
the partial fractions, and the dual side gives `e^{-2π n t}/t` by the half-integral Laplace–Bessel
formula. -/
theorem hamburgerSeries_eq_of_coeffTheta_relation_ofReal (a b : ℕ → ℂ)
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    (hb : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖b (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
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
  have hD_int := integrableOn_dual_coeffTheta_mul_exp b hb ht
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
  have hL := (hasSum_integral_coeffTheta_mul_exp a ha ht).tsum_eq
  have hD := (hasSum_integral_dual_coeffTheta_mul_exp b hb ht).tsum_eq
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

/-- On the disc `|t - t₀| < Re t₀ / 2` the partial-fraction denominators are uniformly
comparable to `m²`: `‖m² + t²‖ ≥ c m²` with `c` depending only on `t₀`.  For `m ≥ 2R` this is
`m² - |t|²`, and for small `m` it is the factorization `(t - im)(t + im)`, each factor having
modulus at least `Re t`. -/
theorem norm_natCast_sq_add_sq_ge_on_ball {t₀ t : ℂ} (h0 : 0 < t₀.re)
    (ht : t ∈ Metric.ball t₀ (t₀.re / 2)) {m : ℕ} :
    min (3 / 4) ((t₀.re / 2) ^ 2 / (4 * (‖t₀‖ + t₀.re / 2) ^ 2)) * (m : ℝ) ^ 2 ≤
      ‖(m : ℂ) ^ 2 + t ^ 2‖ := by
  set δ : ℝ := t₀.re / 2 with hδ
  set R : ℝ := ‖t₀‖ + δ with hR
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hRpos : 0 < R := by rw [hR]; linarith [norm_nonneg t₀]
  rw [Metric.mem_ball, dist_eq_norm] at ht
  have hre : δ < t.re := by
    have h1 := abs_re_le_norm (t - t₀)
    rw [sub_re, abs_le] at h1
    linarith [h1.1]
  have hnorm : ‖t‖ ≤ R := by
    have := norm_le_norm_add_norm_sub' t t₀
    rw [hR]
    have h2 : ‖t - t₀‖ = ‖t₀ - t‖ := norm_sub_rev _ _
    linarith
  rcases le_or_gt (2 * R) (m : ℝ) with hm | hm
  · have h1 : ‖((m : ℂ)) ^ 2‖ = (m : ℝ) ^ 2 := by rw [norm_pow, Complex.norm_natCast]
    have h2 : ‖t ^ 2‖ ≤ R ^ 2 := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg t) hnorm 2
    have h3 := norm_sub_le ((m : ℂ) ^ 2 + t ^ 2) (t ^ 2)
    rw [add_sub_cancel_right, h1] at h3
    have h4 : R ^ 2 ≤ (m : ℝ) ^ 2 / 4 := by nlinarith
    calc min (3 / 4) (δ ^ 2 / (4 * R ^ 2)) * (m : ℝ) ^ 2 ≤ 3 / 4 * (m : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ ≤ ‖(m : ℂ) ^ 2 + t ^ 2‖ := by nlinarith
  · have hfac : (m : ℂ) ^ 2 + t ^ 2 = (t - (m : ℂ) * I) * (t + (m : ℂ) * I) := by
      ring_nf
      rw [I_sq]
      ring
    have h1 : t.re ≤ ‖t - (m : ℂ) * I‖ := by
      have := abs_re_le_norm (t - (m : ℂ) * I)
      simp at this
      exact (le_abs_self _).trans this
    have h2 : t.re ≤ ‖t + (m : ℂ) * I‖ := by
      have := abs_re_le_norm (t + (m : ℂ) * I)
      simp at this
      exact (le_abs_self _).trans this
    have h3 : δ ^ 2 ≤ ‖(m : ℂ) ^ 2 + t ^ 2‖ := by
      rw [hfac, norm_mul]
      have : δ * δ ≤ t.re * t.re := mul_le_mul hre.le hre.le hδpos.le (by linarith)
      nlinarith
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have h4 : (m : ℝ) ^ 2 ≤ 4 * R ^ 2 := by nlinarith
    calc min (3 / 4) (δ ^ 2 / (4 * R ^ 2)) * (m : ℝ) ^ 2 ≤ δ ^ 2 / (4 * R ^ 2) * (m : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ ≤ δ ^ 2 / (4 * R ^ 2) * (4 * R ^ 2) := by gcongr
      _ = δ ^ 2 := by field_simp
      _ ≤ _ := h3

/-- The Hamburger series is holomorphic on the right half-plane. -/
theorem differentiableOn_hamburgerSeries {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) :
    DifferentiableOn ℂ (hamburgerSeries a) {t : ℂ | 0 < t.re} := by
  intro t₀ ht₀
  have h0 : 0 < t₀.re := ht₀
  set c : ℝ := min (3 / 4) ((t₀.re / 2) ^ 2 / (4 * (‖t₀‖ + t₀.re / 2) ^ 2)) with hc
  set R : ℝ := ‖t₀‖ + t₀.re / 2 with hR
  have hcpos : 0 < c := lt_min (by norm_num) (by positivity)
  have hRpos : 0 < R := by rw [hR]; linarith [norm_nonneg t₀]
  have hden : ∀ n : ℕ, ∀ t ∈ Metric.ball t₀ (t₀.re / 2),
      c * ((n + 1 : ℕ) : ℝ) ^ 2 ≤ ‖((n + 1 : ℕ) : ℂ) ^ 2 + t ^ 2‖ :=
    fun n t ht => norm_natCast_sq_add_sq_ge_on_ball h0 ht
  have hU : DifferentiableOn ℂ (hamburgerSeries a) (Metric.ball t₀ (t₀.re / 2)) := by
    refine differentiableOn_tsum_of_summable_norm (ha.mul_left (R / (Real.pi * c)))
      (fun n => ?_) Metric.isOpen_ball (fun n t ht => ?_)
    · refine DifferentiableOn.div (by fun_prop) (by fun_prop) fun t ht => ?_
      have hpos : 0 < ‖((n + 1 : ℕ) : ℂ) ^ 2 + t ^ 2‖ :=
        lt_of_lt_of_le (by positivity) (hden n t ht)
      exact mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (norm_pos_iff.mp hpos)
    · have hpos : 0 < c * ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
      have htR : ‖t‖ ≤ R := by
        rw [Metric.mem_ball, dist_eq_norm] at ht
        have := norm_le_norm_add_norm_sub' t t₀
        have h2 : ‖t - t₀‖ = ‖t₀ - t‖ := norm_sub_rev _ _
        rw [hR]
        linarith
      rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, div_le_iff₀ (mul_pos Real.pi_pos
          (lt_of_lt_of_le hpos (hden n t ht)))]
      calc ‖a (n + 1)‖ * ‖t‖ ≤ ‖a (n + 1)‖ * R := mul_le_mul_of_nonneg_left htR (norm_nonneg _)
        _ = R / (Real.pi * c) * (‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) *
              (Real.pi * (c * ((n + 1 : ℕ) : ℝ) ^ 2)) := by field_simp
        _ ≤ R / (Real.pi * c) * (‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) *
              (Real.pi * ‖((n + 1 : ℕ) : ℂ) ^ 2 + t ^ 2‖) := by
            gcongr
            exact hden n t ht
  exact (hU.differentiableAt (Metric.ball_mem_nhds t₀ (by positivity))).differentiableWithinAt

/-- The dual exponential series `Σ b_n e^{-2π n t}` is holomorphic on the right half-plane. -/
theorem differentiableOn_expDualSeries {b : ℕ → ℂ}
    (hb : Summable fun n : ℕ => ‖b (n + 1)‖ / ((n : ℝ) + 1) ^ 2) :
    DifferentiableOn ℂ (fun t : ℂ => ∑' n : ℕ, b (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * t)))
      {t : ℂ | 0 < t.re} := by
  intro t₀ ht₀
  have h0 : 0 < t₀.re := ht₀
  set δ : ℝ := t₀.re / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hV : IsOpen {t : ℂ | δ < t.re} := isOpen_lt continuous_const Complex.continuous_re
  have hU : DifferentiableOn ℂ
      (fun t : ℂ => ∑' n : ℕ, b (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * t)))
      {t : ℂ | δ < t.re} := by
    refine differentiableOn_tsum_of_summable_norm
      (hb.mul_left (1 / (2 * Real.pi ^ 2 * δ ^ 2))) (fun n => by fun_prop) hV
      (fun n t ht => ?_)
    have ht' : δ < t.re := ht
    have hre : (-(2 * (Real.pi : ℂ) * ((n : ℂ) + 1) * t)).re =
        -(2 * Real.pi * ((n : ℝ) + 1) * t.re) := by
      simp [mul_re]
    rw [norm_mul, Complex.norm_exp, hre]
    have hy : 0 < 2 * Real.pi * ((n : ℝ) + 1) * δ := by positivity
    have h1 : Real.exp (-(2 * Real.pi * ((n : ℝ) + 1) * t.re)) ≤
        Real.exp (-(2 * Real.pi * ((n : ℝ) + 1) * δ)) := by
      rw [Real.exp_le_exp, neg_le_neg_iff]
      gcongr
    have h2 := exp_neg_le_two_div_sq hy
    calc ‖b (n + 1)‖ * Real.exp (-(2 * Real.pi * ((n : ℝ) + 1) * t.re))
        ≤ ‖b (n + 1)‖ * (2 / (2 * Real.pi * ((n : ℝ) + 1) * δ) ^ 2) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (norm_nonneg _)
      _ = 1 / (2 * Real.pi ^ 2 * δ ^ 2) * (‖b (n + 1)‖ / ((n : ℝ) + 1) ^ 2) := by
          field_simp
  exact (hU.differentiableAt (hV.mem_nhds (by show δ < t₀.re; rw [hδ]; linarith))).differentiableWithinAt

theorem summable_sq_of_forall_rpow {a : ℕ → ℂ}
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ) :
    Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ 2 := by
  refine (ha 2 (by norm_num)).congr fun n => ?_
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- **The Hamburger identity on the right half-plane.**  Under the theta relation
`θ_a(x) = ε x^{-1/2} θ_b(1/x) + α + β x^{-1/2}`, for every `t` with `Re t > 0`
`L_a(t) = ε Σ_{n≥1} b_n e^{-2π n t} + α/(π t) + β`.  Both sides are holomorphic on the
half-plane and agree on the positive axis. -/
theorem hamburgerSeries_eq_of_coeffTheta_relation (a b : ℕ → ℂ)
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    (hb : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖b (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
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
    have := summable_sq_of_forall_rpow ha
    simpa using this
  have hf : AnalyticOnNhd ℂ (hamburgerSeries a) U :=
    (differentiableOn_hamburgerSeries ha2).analyticOnNhd hUo
  have hg : AnalyticOnNhd ℂ (fun t : ℂ => ε * ∑' n : ℕ, b (n + 1) *
      cexp (-(2 * Real.pi * ((n : ℂ) + 1) * t)) + α / (Real.pi * t) + β) U := by
    refine DifferentiableOn.analyticOnNhd ?_ hUo
    refine (((differentiableOn_expDualSeries (summable_sq_of_forall_rpow hb)).const_mul ε).add
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
    exact hamburgerSeries_eq_of_coeffTheta_relation_ofReal a b ha hb htheta hk
  exact hf.eqOn_of_preconnected_of_frequently_eq hg (convex_halfSpace_re_gt 0).isPreconnected
    h1U hfreq ht

end GaloisForLFunctions.HTGeometry
