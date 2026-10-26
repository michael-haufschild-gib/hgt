import GaloisForLFunctions.ArithmeticPositiveDuality.PositiveMeasureHamburgerRigidity
import GaloisForLFunctions.RHTower.HamburgerStabilityCriticalLine

/-!
# Quantitative Hamburger stability for positive measures

Positive-measure rigidity (`measure_eq_of_measureTheta_relation`) says that a nonnegative Borel
measure `ν` on `[1, ∞)` whose theta transform obeys Riemann's degree-one theta law is a multiple of
the counting measure of the positive integers. Here the functional equation holds only up to a
defect on the critical line, and the conclusion becomes an inequality.

Let `D_ν(s) = ∫ u^{-s} dν(u)` and let `E` be continuous on `1/2 ≤ Re s ≤ 3/2`, holomorphic inside,
`O(1/(1 + t²))`, with `Γ_ℝ(s) D_ν(s) = E(s) + β Γ_ℝ(s - 1)` on `Re s = 3/2` and

`E(s) - E(1 - s) = -β (Γ_ℝ(s - 1) - Γ_ℝ(-s)) + Γ_ℝ(s) g(Im s / 2)` on `Re s = 1/2`.

**Theorem** (`integral_sinc_sq_le_of_critical_line_defect`). If `g` is measurable, polynomially
bounded and integrable, then

`∫ (sin(π u) / (π u))² dν(u) ≤ (6/π) ∫ ‖g‖`.

The left side is the off-lattice mass of `ν`: `sinc²(π u)` vanishes exactly on `ℤ ∖ {0}`. So a
positive measure whose functional equation fails by an `L¹` defect lies within that defect of
integer support; `g = 0` recovers the exact support statement of positive-measure rigidity.

**Proof.**
* The defect enters the theta law through `K(x) = (1/2π) ∫ x^{-(1/4+it)} Γ_ℝ(1/2+2it) g(t) dt`
  (`critical_line_even_theta_relation_defect`), whose Laplace transform `J` obeys
  `‖J(τ)‖ ≤ (3/2π) ‖τ‖^{-1/2} ‖g‖₁` (`norm_defectLaplace_le`).
* Laplace integration of the defective theta law gives `L_ν(t) = F_ν(t) - β/(πt) + β + J(t)` on
  `Re t > 0` (`measureSeries_eq_of_theta_defect`).
* Pairing with the Fejér window `2 (1 - |τ|)` on `t = ε + iτ` and letting `ε → 0⁺`: the dual side
  tends to `2 ∫ sinc² dν`, the series and polar sides vanish as in the exact case, and the defect
  side is at most `2 · (3/2π) ‖g‖₁ ∫_{-1}^{1} |τ|^{-1/2} dτ = (12/π) ‖g‖₁`.
-/

open Complex MeasureTheory Filter Topology Set Function
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

open GaloisForLFunctions.HTGeometry

/-! ## 1. Laplace transforms of the two theta pieces -/

/-- With `e(x) = e^{-π t² x}`, `t ∫₀^∞ θ_ν e = L_ν(t)` and `t ∫₀^∞ x^{-1/2} θ_ν(1/x) e = F_ν(t)`
for real `t > 0`, both integrands being integrable on `(0, ∞)`. -/
theorem laplace_measureTheta_pieces {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x : ℝ =>
      measureTheta ν x * ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ)) (Ioi 0) ∧
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ *
      ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ)) (Ioi 0) ∧
    (t : ℂ) * (∫ x in Ioi (0 : ℝ),
      measureTheta ν x * ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ)) = measureSeries ν t ∧
    (t : ℂ) * (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ *
      ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ)) = measureDual ν t := by
  haveI : SigmaFinite ν := sigmaFinite_of_measure_Iio_one_eq_zero hsupp hmom
  let S : Set (ℝ × ℝ) := {p : ℝ × ℝ | 1 ≤ p.1 ∧ 0 < p.2}
  have hS : MeasurableSet S :=
    (measurableSet_Ici.preimage measurable_fst).inter (measurableSet_Ioi.preimage measurable_snd)
  -- The series side.
  let G₁ : ℝ → ℝ → ℂ := fun u x =>
    S.indicator (fun p => ((Real.exp (-(Real.pi * (p.1 ^ 2 + t ^ 2)) * p.2) : ℝ) : ℂ)) (u, x)
  have hG₁_meas : AEStronglyMeasurable (uncurry G₁) (ν.prod (volume.restrict (Ioi 0))) := by
    have hc : Continuous (fun p : ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (p.1 ^ 2 + t ^ 2)) * p.2) : ℝ) : ℂ)) := by fun_prop
    exact (aestronglyMeasurable_indicator_iff hS).mpr (hc.continuousOn.aestronglyMeasurable hS)
  have hG₁_eq : ∀ u x : ℝ, 1 ≤ u → 0 < x →
      G₁ u x = ((Real.exp (-(Real.pi * (u ^ 2 + t ^ 2)) * x) : ℝ) : ℂ) :=
    fun u x hu hx => Set.indicator_of_mem (show (u, x) ∈ S from ⟨hu, hx⟩) _
  have hG₁_int : Integrable (uncurry G₁) (ν.prod (volume.restrict (Ioi 0))) := by
    rw [integrable_prod_iff hG₁_meas]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
      have hk : 0 < Real.pi * (u ^ 2 + t ^ 2) := by positivity
      exact IntegrableOn.congr_fun (integrableOn_Ioi_exp_neg_mul hk).ofReal
        (fun x hx => (hG₁_eq u x hu hx).symm) measurableSet_Ioi
    · refine (hmom.const_mul (1 / Real.pi)).mono' ?_ ?_
      · exact hG₁_meas.norm.integral_prod_right'
      · filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
        have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
        have hk : 0 < Real.pi * (u ^ 2 + t ^ 2) := by positivity
        have hn : ∀ x ∈ Ioi (0 : ℝ),
            ‖G₁ u x‖ = Real.exp (-(Real.pi * (u ^ 2 + t ^ 2)) * x) := by
          intro x hx
          rw [hG₁_eq u x hu hx, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (Real.exp_pos _)]
        show ‖∫ y in Ioi (0 : ℝ), ‖G₁ u y‖‖ ≤ 1 / Real.pi * (1 / u ^ 2)
        rw [setIntegral_congr_fun measurableSet_Ioi hn, integral_Ioi_exp_neg_mul hk,
          Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ hk]
        calc (1 : ℝ) = 1 / Real.pi * (1 / u ^ 2) * (Real.pi * u ^ 2) := by field_simp
          _ ≤ 1 / Real.pi * (1 / u ^ 2) * (Real.pi * (u ^ 2 + t ^ 2)) := by
              gcongr; nlinarith [sq_nonneg t]
  -- The dual side.
  let G₂ : ℝ → ℝ → ℂ := fun u x =>
    S.indicator (fun p => ((p.2 ^ (-(1 / 2 : ℝ)) *
      Real.exp (-(Real.pi * p.1 ^ 2 / p.2) - Real.pi * t ^ 2 * p.2) : ℝ) : ℂ)) (u, x)
  have hG₂_meas : AEStronglyMeasurable (uncurry G₂) (ν.prod (volume.restrict (Ioi 0))) := by
    have hc : ContinuousOn (fun p : ℝ × ℝ => ((p.2 ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(Real.pi * p.1 ^ 2 / p.2) - Real.pi * t ^ 2 * p.2) : ℝ) : ℂ)) S := by
      intro p hp
      refine ContinuousAt.continuousWithinAt ?_
      refine Complex.continuous_ofReal.continuousAt.comp ?_
      refine ((Real.continuousAt_rpow_const _ _ (Or.inl hp.2.ne')).comp
        continuous_snd.continuousAt).mul ?_
      refine Real.continuous_exp.continuousAt.comp ?_
      exact (((continuous_const.mul (continuous_fst.pow 2)).continuousAt.div
        continuous_snd.continuousAt hp.2.ne').neg).sub
        (continuous_const.mul continuous_snd).continuousAt
    exact (aestronglyMeasurable_indicator_iff hS).mpr (hc.aestronglyMeasurable hS)
  have hG₂_eq : ∀ u x : ℝ, 1 ≤ u → 0 < x → G₂ u x = ((x ^ (-(1 / 2 : ℝ)) *
      Real.exp (-(Real.pi * u ^ 2 / x) - Real.pi * t ^ 2 * x) : ℝ) : ℂ) :=
    fun u x hu hx => Set.indicator_of_mem (show (u, x) ∈ S from ⟨hu, hx⟩) _
  have hG₂_int : Integrable (uncurry G₂) (ν.prod (volume.restrict (Ioi 0))) := by
    rw [integrable_prod_iff hG₂_meas]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
      have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
      exact IntegrableOn.congr_fun (integrableOn_rpow_neg_half_mul_exp_theta_dual hu0 ht).ofReal
        (fun x hx => (hG₂_eq u x hu hx).symm) measurableSet_Ioi
    · refine (hmom.const_mul (1 / t / (2 * Real.pi ^ 2 * t ^ 2))).mono'
        hG₂_meas.norm.integral_prod_right' ?_
      filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
      have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
      have hn : ∀ x ∈ Ioi (0 : ℝ), ‖G₂ u x‖ =
          x ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * u ^ 2 / x) - Real.pi * t ^ 2 * x) := by
        intro x hx
        have hx0 : (0 : ℝ) < x := hx
        rw [hG₂_eq u x hu hx0, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hx0.le _) (Real.exp_pos _).le)]
      show ‖∫ y in Ioi (0 : ℝ), ‖G₂ u y‖‖ ≤ 1 / t / (2 * Real.pi ^ 2 * t ^ 2) * (1 / u ^ 2)
      rw [setIntegral_congr_fun measurableSet_Ioi hn,
        integral_rpow_neg_half_mul_exp_theta_dual hu0 ht,
        Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hy : 0 < 2 * Real.pi * u * t := by positivity
      calc 1 / t * Real.exp (-(2 * Real.pi * u * t))
          ≤ 1 / t * (2 / (2 * Real.pi * u * t) ^ 2) :=
            mul_le_mul_of_nonneg_left (exp_neg_le_two_div_sq hy) (by positivity)
        _ = 1 / t / (2 * Real.pi ^ 2 * t ^ 2) * (1 / u ^ 2) := by field_simp
  set e : ℝ → ℂ := fun x => ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ) with he
  have hG₁_x : ∀ x ∈ Ioi (0 : ℝ), ∫ u : ℝ, G₁ u x ∂ν = measureTheta ν x * e x := by
    intro x hx
    have hae : (fun u : ℝ => G₁ u x) =ᵐ[ν]
        fun u : ℝ => ((Real.exp (-Real.pi * u ^ 2 * x) : ℝ) : ℂ) * e x := by
      filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
      rw [hG₁_eq u x hu hx]
      simp only [e]
      rw [← ofReal_mul, ← Real.exp_add]
      congr 2
      ring
    rw [integral_congr_ae hae, integral_mul_const, measureTheta]
  have hG₂_x : ∀ x ∈ Ioi (0 : ℝ),
      ∫ u : ℝ, G₂ u x ∂ν = (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ * e x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hcpow : (x : ℂ) ^ (-(1 / 2 : ℂ)) = ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hx0.le]; push_cast; ring_nf
    have hae : (fun u : ℝ => G₂ u x) =ᵐ[ν]
        fun u : ℝ => (x : ℂ) ^ (-(1 / 2 : ℂ)) *
          ((Real.exp (-Real.pi * u ^ 2 * x⁻¹) : ℝ) : ℂ) * e x := by
      filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
      rw [hG₂_eq u x hu hx0]
      simp only [e]
      rw [hcpow, show -(Real.pi * u ^ 2 / x) - Real.pi * t ^ 2 * x =
        -Real.pi * u ^ 2 * x⁻¹ + -(Real.pi * t ^ 2) * x by ring, Real.exp_add]
      push_cast; ring
    rw [integral_congr_ae hae, measureTheta]
    simp_rw [mul_assoc]
    rw [integral_const_mul, integral_mul_const]
  have hθ_int : IntegrableOn (fun x : ℝ => measureTheta ν x * e x) (Ioi 0) :=
    IntegrableOn.congr_fun hG₁_int.integral_prod_right hG₁_x measurableSet_Ioi
  have hD_int : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ * e x) (Ioi 0) :=
    IntegrableOn.congr_fun hG₂_int.integral_prod_right hG₂_x measurableSet_Ioi
  have hL_swap : ∫ x in Ioi (0 : ℝ), measureTheta ν x * e x =
      ∫ u : ℝ, (((Real.pi * (u ^ 2 + t ^ 2) : ℝ) : ℂ))⁻¹ ∂ν := by
    rw [← setIntegral_congr_fun measurableSet_Ioi hG₁_x,
      (integral_integral_swap hG₁_int).symm]
    refine integral_congr_ae ?_
    filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
    have hk : 0 < Real.pi * (u ^ 2 + t ^ 2) := by positivity
    have hfn : ∀ x ∈ Ioi (0 : ℝ), G₁ u x =
        ((Real.exp (-(Real.pi * (u ^ 2 + t ^ 2)) * x) : ℝ) : ℂ) := fun x hx =>
      hG₁_eq u x hu hx
    rw [setIntegral_congr_fun measurableSet_Ioi hfn, integral_complex_ofReal,
      integral_Ioi_exp_neg_mul hk]
    push_cast; ring
  have hD_swap : ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ * e x =
      (1 / (t : ℂ)) * measureDual ν t := by
    rw [← setIntegral_congr_fun measurableSet_Ioi hG₂_x,
      (integral_integral_swap hG₂_int).symm]
    have hae : (fun u : ℝ => ∫ x in Ioi (0 : ℝ), G₂ u x) =ᵐ[ν]
        fun u : ℝ => (1 / (t : ℂ)) * cexp (-(2 * Real.pi * (u : ℂ) * (t : ℂ))) := by
      filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
      have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
      have hfn : ∀ x ∈ Ioi (0 : ℝ), G₂ u x = ((x ^ (-(1 / 2 : ℝ)) *
          Real.exp (-(Real.pi * u ^ 2 / x) - Real.pi * t ^ 2 * x) : ℝ) : ℂ) := fun x hx =>
        hG₂_eq u x hu hx
      rw [setIntegral_congr_fun measurableSet_Ioi hfn, integral_complex_ofReal,
        integral_rpow_neg_half_mul_exp_theta_dual hu0 ht]
      rw [ofReal_mul, Complex.ofReal_exp]
      push_cast; rfl
    rw [integral_congr_ae hae, integral_const_mul, measureDual]
  have hser : measureSeries ν t =
      (t : ℂ) * ∫ u : ℝ, (((Real.pi * (u ^ 2 + t ^ 2) : ℝ) : ℂ))⁻¹ ∂ν := by
    unfold measureSeries
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    push_cast; ring
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  refine ⟨hθ_int, hD_int, by rw [hL_swap, hser], ?_⟩
  rw [hD_swap, ← mul_assoc, mul_one_div_cancel ht0, one_mul]

/-! ## 2. The Laplace identity with a defect -/

/-- **Laplace identity with a defect, on the positive axis.** If
`θ_ν(x) = x^{-1/2} θ_ν(1/x) - β + β x^{-1/2} + K(x)` with `K` the defect kernel of `g`, then
`L_ν(t) = F_ν(t) - β/(πt) + β + J(t)` for real `t > 0`. -/
theorem measureSeries_eq_of_theta_defect_ofReal {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {β : ℂ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    (htheta : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + -β + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) +
        RHTower.HamburgerStability.defectKernel g x)
    {t : ℝ} (ht : 0 < t) :
    measureSeries ν t = measureDual ν t + -β / (Real.pi * t) + β +
      RHTower.HamburgerStability.defectLaplace g t := by
  obtain ⟨-, hD_int₀, hser₀, hdual₀⟩ := laplace_measureTheta_pieces hsupp hmom ht
  obtain ⟨hK_int₀, hJ₀⟩ := RHTower.HamburgerStability.defectKernel_laplace hgm hgb ht
  let e : ℝ → ℂ := fun x => ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ)
  have hD_int : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ * e x) (Ioi 0) := hD_int₀
  have hK_int : IntegrableOn
      (fun x : ℝ => RHTower.HamburgerStability.defectKernel g x * e x) (Ioi 0) := hK_int₀
  have hser : (t : ℂ) * (∫ x in Ioi (0 : ℝ), measureTheta ν x * e x) = measureSeries ν t :=
    hser₀
  have hdual : (t : ℂ) * (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ *
      e x) = measureDual ν t := hdual₀
  have hJ : RHTower.HamburgerStability.defectLaplace g t = (t : ℂ) *
      ∫ x in Ioi (0 : ℝ), RHTower.HamburgerStability.defectKernel g x * e x := hJ₀
  have hB : 0 < Real.pi * t ^ 2 := by positivity
  have he_int : IntegrableOn e (Ioi 0) := (integrableOn_Ioi_exp_neg_mul hB).ofReal
  have hhe_eq : ∀ x ∈ Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x =
      ((x ^ ((1 / 2 : ℝ) - 1) * Real.exp (-((Real.pi * t ^ 2) * x)) : ℝ) : ℂ) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have h1 : (((1 / 2 : ℝ) - 1 : ℝ) : ℂ) = -(1 / 2 : ℂ) := by push_cast; norm_num
    simp only [e]
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hx0.le, h1,
      show -((Real.pi * t ^ 2) * x) = -(Real.pi * t ^ 2) * x by ring]
  have hhe_int : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x) (Ioi 0) := by
    have h : IntegrableOn (fun x : ℝ => x ^ ((1 / 2 : ℝ) - 1) *
        Real.exp (-(Real.pi * t ^ 2) * x ^ (1 : ℝ))) (Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) le_rfl hB
    have h' : IntegrableOn (fun x : ℝ => ((x ^ ((1 / 2 : ℝ) - 1) *
        Real.exp (-((Real.pi * t ^ 2) * x)) : ℝ) : ℂ)) (Ioi 0) := by
      have := Integrable.ofReal (𝕜 := ℂ) h
      simp only [Real.rpow_one, neg_mul] at this
      exact this
    exact h'.congr_fun (fun x hx => (hhe_eq x hx).symm) measurableSet_Ioi
  have hI0 : ∫ x in Ioi (0 : ℝ), e x = ((1 / (Real.pi * t ^ 2) : ℝ) : ℂ) := by
    rw [integral_complex_ofReal, integral_Ioi_exp_neg_mul hB]
  have hIh : ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x = ((1 / t : ℝ) : ℂ) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hhe_eq, integral_complex_ofReal,
      integral_Ioi_rpow_neg_half_mul_exp_neg_mul_sq ht]
  have hpt : ∀ x ∈ Ioi (0 : ℝ), measureTheta ν x * e x =
      ((x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ * e x +
        (-β * e x + β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * e x))) +
          RHTower.HamburgerStability.defectKernel g x * e x := by
    intro x hx; rw [htheta x hx]; ring
  have hpol_int : IntegrableOn
      (fun x : ℝ => -β * e x + β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * e x)) (Ioi 0) :=
    (he_int.const_mul (-β)).add (hhe_int.const_mul β)
  have hsum_int : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ * e x +
      (-β * e x + β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * e x))) (Ioi 0) := hD_int.add hpol_int
  have hsplit : ∫ x in Ioi (0 : ℝ), measureTheta ν x * e x =
      (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ * e x) +
        (-β * ∫ x in Ioi (0 : ℝ), e x) +
          β * (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x) +
            ∫ x in Ioi (0 : ℝ), RHTower.HamburgerStability.defectKernel g x * e x := by
    have he1 : IntegrableOn (fun x : ℝ => -β * e x) (Ioi 0) := he_int.const_mul (-β)
    have he2 : IntegrableOn (fun x : ℝ => β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * e x)) (Ioi 0) :=
      hhe_int.const_mul β
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add hsum_int hK_int,
      integral_add hD_int hpol_int, integral_add he1 he2, integral_const_mul, integral_const_mul]
    ring
  rw [← hser, ← hdual, hJ, hsplit, hI0, hIh]
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-- **Laplace identity with a defect, on the half-plane.** -/
theorem measureSeries_eq_of_theta_defect {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {β : ℂ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    (htheta : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + -β + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) +
        RHTower.HamburgerStability.defectKernel g x)
    {t : ℂ} (ht : 0 < t.re) :
    measureSeries ν t = measureDual ν t + -β / (Real.pi * t) + β +
      RHTower.HamburgerStability.defectLaplace g t := by
  set U : Set ℂ := {z : ℂ | 0 < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ (measureSeries ν) U :=
    (differentiableOn_measureSeries hsupp hmom).analyticOnNhd hUo
  have hg : AnalyticOnNhd ℂ (fun z : ℂ => measureDual ν z + -β / (Real.pi * z) + β +
      RHTower.HamburgerStability.defectLaplace g z) U := by
    refine DifferentiableOn.analyticOnNhd ?_ hUo
    refine (((differentiableOn_measureDual hsupp hmom).add ?_).add
      (differentiableOn_const _)).add
      (RHTower.HamburgerStability.differentiableOn_defectLaplace hgm.aestronglyMeasurable hgb)
    refine DifferentiableOn.div (differentiableOn_const _) (by fun_prop) fun z hz => ?_
    have hz' : 0 < z.re := hz
    refine mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) fun h0 => ?_
    rw [h0, zero_re] at hz'
    exact lt_irrefl _ hz'
  have h1U : (1 : ℂ) ∈ U := by simp [hU]
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), measureSeries ν z = measureDual ν z +
      -β / (Real.pi * z) + β + RHTower.HamburgerStability.defectLaplace g z := by
    let r : ℕ → ℝ := fun k => 1 + 1 / ((k : ℝ) + 1)
    have hr : ∀ k, 1 < r k := fun k => by
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      simp only [r]; linarith
    have hlim : Tendsto (fun k => ((r k : ℝ) : ℂ)) atTop (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
      · have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ)
        rw [add_zero] at h
        have h' := (Complex.continuous_ofReal.tendsto 1).comp h
        rw [Complex.ofReal_one] at h'
        exact h'
      · exact fun h => (hr k).ne' (Complex.ofReal_eq_one.mp h)
    exact hlim.frequently <| Frequently.of_forall fun k =>
      measureSeries_eq_of_theta_defect_ofReal hsupp hmom hgm hgb htheta
        (lt_trans zero_lt_one (hr k))
  have hconn : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hconn h1U hfreq ht

/-! ## 3. The Fejér pairing with a defect -/

theorem continuous_defectLaplace_line {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ}
    (hgm : AEStronglyMeasurable g volume) (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    {ε : ℝ} (hε : 0 < ε) :
    Continuous fun τ : ℝ =>
      RHTower.HamburgerStability.defectLaplace g ((ε : ℂ) + (τ : ℂ) * I) :=
  (RHTower.HamburgerStability.differentiableOn_defectLaplace hgm hgb).continuousOn.comp_continuous
    (by fun_prop) fun τ => by
      show 0 < ((ε : ℂ) + (τ : ℂ) * I).re
      simp [hε]

/-- The defect term of the Fejér pairing on `t = ε + iτ`. -/
def fejerDefectKernel (g : ℝ → ℂ) (ε τ : ℝ) : ℝ :=
  2 * (1 - |τ|) * (RHTower.HamburgerStability.defectLaplace g ((ε : ℂ) + (τ : ℂ) * I)).re

theorem continuous_fejerDefectKernel {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ}
    (hgm : AEStronglyMeasurable g volume) (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    {ε : ℝ} (hε : 0 < ε) : Continuous (fejerDefectKernel g ε) :=
  (continuous_const.mul (continuous_const.sub continuous_abs)).mul
    (Complex.continuous_re.comp (continuous_defectLaplace_line hgm hgb hε))

/-- Real, Fejér-weighted form of the defective Laplace identity on `t = ε + iτ`. -/
theorem integral_fejerSeriesKernel_eq_of_theta_defect {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {β : ℂ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    (htheta : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + -β + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) +
        RHTower.HamburgerStability.defectKernel g x)
    {ε : ℝ} (hε : 0 < ε) (τ : ℝ) :
    ∫ u, fejerSeriesKernel ε τ u ∂ν =
      ∫ u, fejerDualKernel ε τ u ∂ν + fejerPolarKernel (-β) β ε τ + fejerDefectKernel g ε τ := by
  have ht : 0 < ((ε : ℂ) + (τ : ℂ) * I).re := by simp [hε]
  have hser : ∫ u, fejerSeriesKernel ε τ u ∂ν =
      2 * (1 - |τ|) * (measureSeries ν ((ε : ℂ) + (τ : ℂ) * I)).re := by
    have h : ∫ u : ℝ, ((((ε : ℂ) + (τ : ℂ) * I)) /
        ((Real.pi : ℂ) * ((u : ℂ) ^ 2 + ((ε : ℂ) + (τ : ℂ) * I) ^ 2))).re ∂ν =
        (measureSeries ν ((ε : ℂ) + (τ : ℂ) * I)).re :=
      integral_re (integrable_measureSeries_integrand hsupp hmom ht)
    rw [← h, ← integral_const_mul]
    rfl
  have hdual : ∫ u, fejerDualKernel ε τ u ∂ν =
      2 * (1 - |τ|) * (measureDual ν ((ε : ℂ) + (τ : ℂ) * I)).re := by
    have h : ∫ u : ℝ, (cexp (-(2 * Real.pi * (u : ℂ) * ((ε : ℂ) + (τ : ℂ) * I)))).re ∂ν =
        (measureDual ν ((ε : ℂ) + (τ : ℂ) * I)).re :=
      integral_re (integrable_measureDual_integrand hsupp hmom ht)
    rw [← h, ← integral_const_mul]
    rfl
  rw [hser, hdual, measureSeries_eq_of_theta_defect hsupp hmom hgm hgb htheta ht,
    fejerPolarKernel, fejerDefectKernel]
  simp only [add_re]
  ring

/-- **Fejér pairing with a defect.** -/
theorem fejer_pairing_identity_of_theta_defect {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {β : ℂ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    (htheta : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + -β + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) +
        RHTower.HamburgerStability.defectKernel g x)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    2 * ∫ u : ℝ, Real.exp (-2 * Real.pi * u * ε) *
        (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 ∂ν =
      (∫ u : ℝ, (∫ τ in (-1 : ℝ)..1, fejerSeriesKernel ε τ u) ∂ν) -
        (∫ τ in (-1 : ℝ)..1, fejerPolarKernel (-β) β ε τ) -
          ∫ τ in (-1 : ℝ)..1, fejerDefectKernel g ε τ := by
  haveI : SigmaFinite ν := sigmaFinite_of_measure_Iio_one_eq_zero hsupp hmom
  have hL := integrable_fejerSeriesKernel hsupp hmom hε0 hε1
  have hD := integrable_fejerDualKernel hsupp hmom hε0
  have hD_ii : IntervalIntegrable (fun τ : ℝ => ∫ u, fejerDualKernel ε τ u ∂ν) volume (-1) 1 :=
    intervalIntegrable_iff.mpr hD.integral_prod_left
  have hP_ii : IntervalIntegrable (fejerPolarKernel (-β) β ε) volume (-1) 1 :=
    (continuous_fejerPolarKernel (-β) β hε0).intervalIntegrable _ _
  have hJ_ii : IntervalIntegrable (fejerDefectKernel g ε) volume (-1) 1 :=
    (continuous_fejerDefectKernel hgm.aestronglyMeasurable hgb hε0).intervalIntegrable _ _
  have hint : ∫ τ in (-1 : ℝ)..1, ∫ u, fejerSeriesKernel ε τ u ∂ν =
      (∫ τ in (-1 : ℝ)..1, ∫ u, fejerDualKernel ε τ u ∂ν) +
        (∫ τ in (-1 : ℝ)..1, fejerPolarKernel (-β) β ε τ) +
          ∫ τ in (-1 : ℝ)..1, fejerDefectKernel g ε τ := by
    calc ∫ τ in (-1 : ℝ)..1, ∫ u, fejerSeriesKernel ε τ u ∂ν
        = ∫ τ in (-1 : ℝ)..1, ((∫ u, fejerDualKernel ε τ u ∂ν) + fejerPolarKernel (-β) β ε τ +
            fejerDefectKernel g ε τ) :=
          intervalIntegral.integral_congr fun τ _ =>
            integral_fejerSeriesKernel_eq_of_theta_defect hsupp hmom hgm hgb htheta hε0 τ
      _ = (∫ τ in (-1 : ℝ)..1, ((∫ u, fejerDualKernel ε τ u ∂ν) +
            fejerPolarKernel (-β) β ε τ)) + ∫ τ in (-1 : ℝ)..1, fejerDefectKernel g ε τ :=
          intervalIntegral.integral_add (hD_ii.add hP_ii) hJ_ii
      _ = _ := by rw [intervalIntegral.integral_add hD_ii hP_ii]
  rw [intervalIntegral_integral_swap hL, intervalIntegral_integral_swap hD] at hint
  have hdual : ∫ u, (∫ τ in (-1 : ℝ)..1, fejerDualKernel ε τ u) ∂ν =
      2 * ∫ u : ℝ, Real.exp (-2 * Real.pi * u * ε) *
        (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 ∂ν := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
    rw [intervalIntegral_fejerDualKernel ε (lt_of_lt_of_le zero_lt_one hu).ne']
    ring
  rw [hdual] at hint
  linarith

/-! ## 4. The polar and defect terms -/

/-- `∫_{-1}^{1} F = ∫_0^1 (F(τ) + F(-τ))`. -/
theorem intervalIntegral_neg_one_one_eq {F : ℝ → ℝ} (hF : Continuous F) :
    ∫ τ in (-1 : ℝ)..1, F τ = ∫ τ in (0 : ℝ)..1, (F τ + F (-τ)) := by
  have h2 : ∫ τ in (0 : ℝ)..1, F (-τ) = ∫ τ in (-1 : ℝ)..0, F τ := by
    rw [intervalIntegral.integral_comp_neg]; norm_num
  have hFn : IntervalIntegrable (fun τ => F (-τ)) volume 0 1 :=
    (hF.comp continuous_neg).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hF.intervalIntegrable _ _) hFn, h2, add_comm,
    intervalIntegral.integral_add_adjacent_intervals (hF.intervalIntegrable _ _)
      (hF.intervalIntegrable _ _)]

/-- The Fejér polar kernel in real coordinates. -/
theorem fejerPolarKernel_eq_re_im (α β : ℂ) {ε : ℝ} (hε : 0 < ε) (τ : ℝ) :
    fejerPolarKernel α β ε τ =
      2 * (1 - |τ|) * ((α.re * ε + α.im * τ) / (Real.pi * (ε ^ 2 + τ ^ 2)) + β.re) := by
  have hpi := Real.pi_pos
  have hden : 0 < ε ^ 2 + τ ^ 2 := by positivity
  have hw : (Real.pi : ℂ) * ((ε : ℂ) + (τ : ℂ) * I) =
      ((Real.pi * ε : ℝ) : ℂ) + ((Real.pi * τ : ℝ) : ℂ) * I := by push_cast; ring
  unfold fejerPolarKernel
  congr 1
  rw [Complex.add_re, hw, Complex.div_re, Complex.normSq_add_mul_I]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    sub_zero, zero_add, add_zero]
  have h1 : (Real.pi * ε) ^ 2 + (Real.pi * τ) ^ 2 = Real.pi ^ 2 * (ε ^ 2 + τ ^ 2) := by ring
  rw [h1]
  field_simp

/-- With antisymmetric polar constants `(-β, β)` the Fejér polar term tends to `0` as `ε → 0⁺`:
the real part is the exact-case cancellation and the imaginary part is odd. -/
theorem tendsto_integral_fejerPolarKernel_neg (β : ℂ) :
    Tendsto (fun ε : ℝ => ∫ τ in (-1 : ℝ)..1, fejerPolarKernel (-β) β ε τ)
      (𝓝[>] 0) (𝓝 0) := by
  set ρ : ℝ := 2 * β.re
  have heq : ∀ ε : ℝ, 0 < ε → ∫ τ in (-1 : ℝ)..1, fejerPolarKernel (-β) β ε τ =
      ρ - (ρ / Real.pi) * ∫ τ in (-1 : ℝ)..1, (1 - |τ|) * (ε / (ε ^ 2 + τ ^ 2)) := by
    intro ε hε
    have hodd : ∫ τ in (-1 : ℝ)..1, 2 * (1 - |τ|) * (β.im * τ / (Real.pi * (ε ^ 2 + τ ^ 2))) =
        0 := by
      have hc : Continuous fun τ : ℝ =>
          2 * (1 - |τ|) * (β.im * τ / (Real.pi * (ε ^ 2 + τ ^ 2))) :=
        (continuous_const.mul (continuous_const.sub continuous_abs)).mul
          ((continuous_const.mul continuous_id).div (by fun_prop)
            fun τ => by have := Real.pi_pos; positivity)
      rw [intervalIntegral_neg_one_one_eq hc]
      refine (intervalIntegral.integral_congr fun τ _ => ?_).trans intervalIntegral.integral_zero
      simp only [abs_neg, neg_sq]
      ring
    have hsplit : ∀ τ : ℝ, fejerPolarKernel (-β) β ε τ =
        fejerPolarKernel ((-ρ / 2 : ℝ) : ℂ) ((ρ / 2 : ℝ) : ℂ) ε τ -
          2 * (1 - |τ|) * (β.im * τ / (Real.pi * (ε ^ 2 + τ ^ 2))) := by
      intro τ
      rw [fejerPolarKernel_eq_re_im _ _ hε, fejerPolarKernel_eq_re_im _ _ hε]
      simp only [Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, ρ]
      ring
    have hc1 : Continuous (fejerPolarKernel ((-ρ / 2 : ℝ) : ℂ) ((ρ / 2 : ℝ) : ℂ) ε) :=
      continuous_fejerPolarKernel _ _ hε
    have hc2 : Continuous fun τ : ℝ =>
        2 * (1 - |τ|) * (β.im * τ / (Real.pi * (ε ^ 2 + τ ^ 2))) :=
      (continuous_const.mul (continuous_const.sub continuous_abs)).mul
        ((continuous_const.mul continuous_id).div (by fun_prop)
          fun τ => by have := Real.pi_pos; positivity)
    rw [intervalIntegral.integral_congr fun τ _ => hsplit τ,
      intervalIntegral.integral_sub (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
      hodd, sub_zero, intervalIntegral_fejerPolarKernel hε]
  have hp := ((tendsto_fejer_polar.const_mul (ρ / Real.pi)).const_sub ρ)
  have hcancel : ρ - (ρ / Real.pi) * Real.pi = 0 := by
    rw [div_mul_cancel₀ _ Real.pi_ne_zero, sub_self]
  rw [hcancel] at hp
  exact hp.congr' (eventually_nhdsWithin_of_forall fun ε hε => (heq ε hε).symm)

/-- **The defect term is uniformly bounded.** `|∫_{-1}^{1} 2(1 - |τ|) Re J(ε + iτ) dτ| ≤ (12/π) ‖g‖₁`
for every `ε > 0`, from `‖J(τ)‖ ≤ (3/2π) ‖τ‖^{-1/2} ‖g‖₁` and `∫_0^1 τ^{-1/2} = 2`. -/
theorem abs_integral_fejerDefectKernel_le {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hgi : Integrable g) {ε : ℝ} (hε : 0 < ε) :
    |∫ τ in (-1 : ℝ)..1, fejerDefectKernel g ε τ| ≤ 12 / Real.pi * ∫ t, ‖g t‖ := by
  have hpi := Real.pi_pos
  set M : ℝ := ∫ t, ‖g t‖ with hM
  have hM0 : 0 ≤ M := integral_nonneg fun _ => norm_nonneg _
  have hFc := continuous_fejerDefectKernel hgm.aestronglyMeasurable hgb hε
  -- Pointwise bound off `τ = 0`.
  have hpt : ∀ τ : ℝ, 0 < |τ| → |τ| ≤ 1 →
      |fejerDefectKernel g ε τ| ≤ 3 / Real.pi * M * |τ| ^ (-(1 / 2 : ℝ)) := by
    intro τ hτ0 hτ1
    have hre : 0 < ((ε : ℂ) + (τ : ℂ) * I).re := by simp [hε]
    have hJ := RHTower.HamburgerStability.norm_defectLaplace_le hgm.aestronglyMeasurable hgb hre
    have habel : RHTower.HamburgerStability.abelMass g
        (2 * (((ε : ℂ) + (τ : ℂ) * I).re / ‖(ε : ℂ) + (τ : ℂ) * I‖)) ≤ M := by
      have hδ : 0 < 2 * (((ε : ℂ) + (τ : ℂ) * I).re / ‖(ε : ℂ) + (τ : ℂ) * I‖) :=
        mul_pos two_pos (RHTower.HamburgerStability.pos_re_div_norm hre)
      unfold RHTower.HamburgerStability.abelMass
      refine integral_mono
        (RHTower.HamburgerStability.integrable_abelMass hgm.aestronglyMeasurable hgb hδ)
        hgi.norm fun t => ?_
      refine mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr ?_)
      have := mul_nonneg hδ.le (abs_nonneg t)
      linarith
    have hnorm : |τ| ≤ ‖(ε : ℂ) + (τ : ℂ) * I‖ := by
      have h := Complex.abs_im_le_norm ((ε : ℂ) + (τ : ℂ) * I)
      simpa using h
    have hpow : ‖(ε : ℂ) + (τ : ℂ) * I‖ ^ (-(1 / 2 : ℝ)) ≤ |τ| ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hτ0 hnorm (by norm_num)
    have hw : |(1 - |τ|)| ≤ 1 := by
      rw [abs_of_nonneg (by linarith)]; linarith [abs_nonneg τ]
    have hJ' : ‖RHTower.HamburgerStability.defectLaplace g ((ε : ℂ) + (τ : ℂ) * I)‖ ≤
        3 / (2 * Real.pi) * |τ| ^ (-(1 / 2 : ℝ)) * M :=
      hJ.trans (mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity)) habel
        (integral_nonneg fun t => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
        (by positivity))
    unfold fejerDefectKernel
    rw [abs_mul, abs_mul, abs_two]
    calc 2 * |(1 - |τ|)| *
          |(RHTower.HamburgerStability.defectLaplace g ((ε : ℂ) + (τ : ℂ) * I)).re|
        ≤ 2 * 1 * ‖RHTower.HamburgerStability.defectLaplace g ((ε : ℂ) + (τ : ℂ) * I)‖ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hw (by norm_num)) (Complex.abs_re_le_norm _)
            (abs_nonneg _) (by norm_num)
      _ ≤ 2 * 1 * (3 / (2 * Real.pi) * |τ| ^ (-(1 / 2 : ℝ)) * M) :=
          mul_le_mul_of_nonneg_left hJ' (by norm_num)
      _ = 3 / Real.pi * M * |τ| ^ (-(1 / 2 : ℝ)) := by field_simp
  -- Fold onto `[0, 1]` and integrate the majorant.
  rw [intervalIntegral_neg_one_one_eq hFc, ← Real.norm_eq_abs]
  have hbound : ‖∫ τ in (0 : ℝ)..1, (fejerDefectKernel g ε τ + fejerDefectKernel g ε (-τ))‖ ≤
      ∫ τ in (0 : ℝ)..1, 6 / Real.pi * M * τ ^ (-(1 / 2 : ℝ)) := by
    refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      (Eventually.of_forall fun τ hτ => ?_)
      ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _)
    have hτ0 : 0 < |τ| := by rw [abs_of_pos hτ.1]; exact hτ.1
    have hτ1 : |τ| ≤ 1 := by rw [abs_of_pos hτ.1]; exact hτ.2
    have h1 := hpt τ hτ0 hτ1
    have h2 := hpt (-τ) (by rwa [abs_neg]) (by rwa [abs_neg])
    rw [abs_neg, abs_of_pos hτ.1] at h2
    rw [abs_of_pos hτ.1] at h1
    rw [Real.norm_eq_abs]
    calc |fejerDefectKernel g ε τ + fejerDefectKernel g ε (-τ)|
        ≤ |fejerDefectKernel g ε τ| + |fejerDefectKernel g ε (-τ)| := abs_add_le _ _
      _ ≤ 3 / Real.pi * M * τ ^ (-(1 / 2 : ℝ)) + 3 / Real.pi * M * τ ^ (-(1 / 2 : ℝ)) :=
          add_le_add h1 h2
      _ = 6 / Real.pi * M * τ ^ (-(1 / 2 : ℝ)) := by ring
  have hval : ∫ τ in (0 : ℝ)..1, 6 / Real.pi * M * τ ^ (-(1 / 2 : ℝ)) = 12 / Real.pi * M := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num)),
      show (-(1 / 2 : ℝ)) + 1 = 1 / 2 by norm_num, Real.one_rpow,
      Real.zero_rpow (by norm_num)]
    ring
  exact hbound.trans hval.le

/-! ## 5. Quantitative stability -/

/-- **Quantitative Hamburger stability for positive measures.** Let `ν ≥ 0` vanish on `(-∞, 1)`
with `∫ u^{-3/2} dν < ∞`, and let `E` be continuous on `1/2 ≤ Re s ≤ 3/2`, holomorphic inside and
`O(1/(1 + t²))`, with `Γ_ℝ(s) D_ν(s) = E(s) + β Γ_ℝ(s - 1)` on `Re s = 3/2` and
`E(s) - E(1 - s) = -β (Γ_ℝ(s - 1) - Γ_ℝ(-s)) + Γ_ℝ(s) g(Im s / 2)` on `Re s = 1/2`. If `g` is
measurable, polynomially bounded and integrable, the off-lattice mass of `ν` is at most
`(6/π) ‖g‖₁`: `∫ (sin(π u) / (π u))² dν(u) ≤ (6/π) ∫ ‖g‖`. -/
theorem integral_sinc_sq_le_of_critical_line_defect {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) ν)
    {E : ℂ → ℂ} {β : ℂ} {C : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ}
    (hEc : ContinuousOn E (verticalStrip (1 / 2) (3 / 2)))
    (hEd : DifferentiableOn ℂ E {s : ℂ | 1 / 2 < s.re ∧ s.re < 3 / 2})
    (hdecay : ∀ s ∈ verticalStrip (1 / 2) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (hR : ∀ s : ℂ, s.re = 3 / 2 →
      Complex.Gammaℝ s * measureDirichlet ν s = E s + β * Complex.Gammaℝ (s - 1))
    (hC : ∀ s : ℂ, s.re = 1 / 2 → E s - E (1 - s) =
      -(β * (Complex.Gammaℝ (s - 1) - Complex.Gammaℝ (-s))) + Complex.Gammaℝ s * g (s.im / 2))
    (hgm : Measurable g) (hgb : ∀ t : ℝ, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hgi : Integrable g) :
    ∫ u : ℝ, (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 ∂ν ≤ 6 / Real.pi * ∫ t, ‖g t‖ := by
  have hpi := Real.pi_pos
  have hmom2 : Integrable (fun u : ℝ => 1 / u ^ 2) ν :=
    integrable_inv_sq_of_integrable_rpow_neg_three_halves hsupp hmom
  haveI : SigmaFinite ν := sigmaFinite_of_measure_Iio_one_eq_zero hsupp hmom2
  -- The defective theta law.
  have hθm : MellinConvergent (measureTheta ν) (3 / 4) := by
    have h := hasMellin_measureTheta hsupp (s := (3 / 2 : ℂ)) (by norm_num)
      (by simpa using hmom) hmom2
    simpa [show ((3 / 2 : ℂ) / 2) = (3 / 4 : ℂ) by ring] using h.1
  have hR' : ∀ s : ℂ, s.re = 3 / 2 →
      mellin (measureTheta ν) (s / 2) = E s + β * Complex.Gammaℝ (s - 1) := by
    intro s hs
    have hm := hasMellin_measureTheta hsupp (s := s) (by linarith)
      (by rw [hs]; exact hmom) hmom2
    rw [hm.2]; exact hR s hs
  have him : ∀ t : ℝ, (2 * (((1 / 4 : ℝ) : ℂ) + t * I)).im / 2 = t := fun t => by simp
  have hdint : Integrable fun t : ℝ => Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) *
      g ((2 * (((1 / 4 : ℝ) : ℂ) + t * I)).im / 2) := by
    simp only [him]
    exact RHTower.HamburgerStability.integrable_Gammaℝ_mul hgm.aestronglyMeasurable hgb
  have htheta : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + -β + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) +
        RHTower.HamburgerStability.defectKernel g x := by
    intro x hx
    have h := critical_line_even_theta_relation_defect
      (d := fun s => Complex.Gammaℝ s * g (s.im / 2))
      (continuousOn_measureTheta hsupp hmom2) hθm hEc hEd hdecay hR' hC hdint hx
    simp only [him] at h
    unfold RHTower.HamburgerStability.defectKernel
    linear_combination h
  -- The pairing at `ε_k = 1/(k+1)`.
  set M : ℝ := ∫ t, ‖g t‖ with hM
  let εs : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hεs_pos : ∀ k : ℕ, 0 < εs k := fun k => by dsimp only [εs]; positivity
  have hεs_le : ∀ k : ℕ, εs k ≤ 1 := fun k => by
    dsimp only [εs]
    exact div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by positivity)
  have hεs_nhds : Tendsto εs atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall hεs_pos⟩
  -- Dual side: dominated convergence.
  have hlim_dual : Tendsto (fun k : ℕ => 2 * ∫ u : ℝ, Real.exp (-2 * Real.pi * u * εs k) *
      (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 ∂ν) atTop
      (𝓝 (2 * ∫ u : ℝ, (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 ∂ν)) := by
    refine Tendsto.const_mul 2 ?_
    refine tendsto_integral_of_dominated_convergence
      (fun u : ℝ => (1 / Real.pi ^ 2) * (1 / u ^ 2))
      (fun k => Measurable.aestronglyMeasurable (by fun_prop)) (hmom2.const_mul _)
      (fun k => ?_) ?_
    · filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
      have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
      have hexp_le : Real.exp (-2 * Real.pi * u * εs k) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 < 2 * Real.pi * u * εs k := mul_pos (by positivity) (hεs_pos k)
        linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hsin_le : (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 ≤
          (1 / Real.pi ^ 2) * (1 / u ^ 2) := by
        rw [div_pow, mul_pow]
        calc Real.sin (Real.pi * u) ^ 2 / (Real.pi ^ 2 * u ^ 2)
            ≤ 1 / (Real.pi ^ 2 * u ^ 2) :=
              div_le_div_of_nonneg_right (Real.sin_sq_le_one _) (by positivity)
          _ = (1 / Real.pi ^ 2) * (1 / u ^ 2) := by rw [one_div_mul_one_div]
      calc Real.exp (-2 * Real.pi * u * εs k) * (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2
          ≤ 1 * ((1 / Real.pi ^ 2) * (1 / u ^ 2)) :=
            mul_le_mul hexp_le hsin_le (sq_nonneg _) zero_le_one
        _ = (1 / Real.pi ^ 2) * (1 / u ^ 2) := one_mul _
    · filter_upwards with u
      have h0 : Tendsto (fun k : ℕ => -2 * Real.pi * u * εs k) atTop (𝓝 0) := by
        simpa only [mul_zero] using
          tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (-2 * Real.pi * u)
      have hc : Tendsto (fun k : ℕ => Real.exp (-2 * Real.pi * u * εs k)) atTop (𝓝 1) := by
        have h := (Real.continuous_exp.tendsto 0).comp h0
        rw [Real.exp_zero] at h
        exact h
      simpa only [one_mul] using hc.mul_const ((Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2)
  -- Series side: the uniform `O(√ε)` collar bound.
  have hlim_poisson : Tendsto (fun k : ℕ =>
      ∫ u : ℝ, (∫ τ in (-1 : ℝ)..1, fejerSeriesKernel (εs k) τ u) ∂ν) atTop (𝓝 0) := by
    set M₂ : ℝ := ∫ u : ℝ, 1 / u ^ 2 ∂ν
    have hmaj : Tendsto (fun k : ℕ => (24 * Real.sqrt (εs k) / Real.pi) * M₂) atTop (𝓝 0) := by
      have hsq : Tendsto (fun k : ℕ => Real.sqrt (εs k)) atTop (𝓝 0) := by
        have h := (Real.continuous_sqrt.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
        rw [Real.sqrt_zero] at h
        exact h
      simpa using ((hsq.const_mul 24).div_const Real.pi).mul_const M₂
    refine squeeze_zero' (Eventually.of_forall fun k => ?_) (Eventually.of_forall fun k => ?_) hmaj
    · refine integral_nonneg fun u => ?_
      exact intervalIntegral.integral_nonneg (by norm_num) fun τ hτ =>
        fejerSeriesKernel_nonneg (hεs_pos k) (abs_le.mpr hτ) u
    · have hε0 := hεs_pos k
      have hε1 := hεs_le k
      have hpt_le : ∀ᵐ u ∂ν, (∫ τ in (-1 : ℝ)..1, fejerSeriesKernel (εs k) τ u) ≤
          (24 * Real.sqrt (εs k) / Real.pi) * (1 / u ^ 2) := by
        filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
        exact intervalIntegral_fejerSeriesKernel_le hu hε0 hε1
      have hint_lhs : Integrable
          (fun u : ℝ => ∫ τ in (-1 : ℝ)..1, fejerSeriesKernel (εs k) τ u) ν := by
        refine (integrable_fejerSeriesKernel hsupp hmom2 hε0 hε1).integral_prod_right.congr
          (Eventually.of_forall fun u => ?_)
        show (∫ τ in uIoc (-1 : ℝ) 1, fejerSeriesKernel (εs k) τ u) =
          ∫ τ in (-1 : ℝ)..1, fejerSeriesKernel (εs k) τ u
        rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1),
          intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      calc ∫ u : ℝ, (∫ τ in (-1 : ℝ)..1, fejerSeriesKernel (εs k) τ u) ∂ν
          ≤ ∫ u : ℝ, (24 * Real.sqrt (εs k) / Real.pi) * (1 / u ^ 2) ∂ν :=
            integral_mono_ae hint_lhs (hmom2.const_mul _) hpt_le
        _ = (24 * Real.sqrt (εs k) / Real.pi) * M₂ := integral_const_mul _ _
  -- Polar side.
  have hlim_polar : Tendsto (fun k : ℕ =>
      ∫ τ in (-1 : ℝ)..1, fejerPolarKernel (-β) β (εs k) τ) atTop (𝓝 0) :=
    (tendsto_integral_fejerPolarKernel_neg β).comp hεs_nhds
  -- Assemble: the left side is at most `series − polar + (12/π) M`.
  have hle : ∀ k : ℕ, 2 * ∫ u : ℝ, Real.exp (-2 * Real.pi * u * εs k) *
      (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 ∂ν ≤
        (∫ u : ℝ, (∫ τ in (-1 : ℝ)..1, fejerSeriesKernel (εs k) τ u) ∂ν) -
          (∫ τ in (-1 : ℝ)..1, fejerPolarKernel (-β) β (εs k) τ) + 12 / Real.pi * M := by
    intro k
    rw [fejer_pairing_identity_of_theta_defect hsupp hmom2 hgm hgb htheta (hεs_pos k)
      (hεs_le k)]
    have hJ := abs_integral_fejerDefectKernel_le hgm hgb hgi (hεs_pos k)
    linarith [neg_abs_le (∫ τ in (-1 : ℝ)..1, fejerDefectKernel g (εs k) τ)]
  have hrhs : Tendsto (fun k : ℕ =>
      (∫ u : ℝ, (∫ τ in (-1 : ℝ)..1, fejerSeriesKernel (εs k) τ u) ∂ν) -
        (∫ τ in (-1 : ℝ)..1, fejerPolarKernel (-β) β (εs k) τ) + 12 / Real.pi * M) atTop
      (𝓝 (0 - 0 + 12 / Real.pi * M)) :=
    (hlim_poisson.sub hlim_polar).add_const _
  have h2 := le_of_tendsto_of_tendsto' hlim_dual hrhs hle
  have h12 : 12 / Real.pi * M = 2 * (6 / Real.pi * M) := by ring
  linarith

end GaloisForLFunctions.ArithmeticPositiveDuality
