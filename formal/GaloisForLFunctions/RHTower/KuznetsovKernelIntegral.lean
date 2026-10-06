import GaloisForLFunctions.RHTower.BesselInverseGaussianComplexRate
import GaloisForLFunctions.RHTower.CauchyBetaIntegral

/-!
# Kuznetsov's double integral

For `Re a₁ > ½`, `Re a₂ > 1`, `μ, ν, q > 0`, `α = a₁ − a₂`, `P = 4π²μν/q`,

`∫_0^∞ ∫_ℝ (1+ξ²)^{−a₂} y^{α−1} e^{−2πμ(1+iξ)y − 2πν/(q(1+iξ)y)} dξ dy
  = 2 P^{α/2} (2πμ)^{−α} K_α(2√P) · π 2^{2−a₁−a₂} Γ(a₁+a₂−1)/(Γ(a₁)Γ(a₂))`.

The integrand is dominated by the product `y^{Re α+δ−1} e^{−2πμy} · (1+ξ²)^{δ−Re a₂}` (from
`e^{−u} ≤ δ^δ u^{−δ}`), so the order of integration may be exchanged; the `y`-integral is the
inverse-Gaussian Mellin integral with the complex rate `2πμ(1+iξ)`, and
`(1+ξ²)^{−a₂}(1+iξ)^{−α} = (1+iξ)^{−a₁}(1−iξ)^{−a₂}` reduces the `ξ`-integral to Cauchy's beta
integral.  The bound `∫∫ |·| ≤ C q^δ` controls the sum over the moduli `c` (with `q = c²`).
-/

open Complex MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.RHTower.Kuznetsov

noncomputable section

/-! ## Principal powers -/

theorem ofReal_pos_mul_cpow' {r : ℝ} (hr : 0 < r) {x : ℂ} (hx : x ≠ 0) (s : ℂ) :
    ((r : ℂ) * x) ^ s = (r : ℂ) ^ s * x ^ s := by
  have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hrne hx), Complex.cpow_def_of_ne_zero hrne,
    Complex.cpow_def_of_ne_zero hx, Complex.log_ofReal_mul hr hx, ← Complex.exp_add,
    Complex.ofReal_log hr.le]
  congr 1
  ring

theorem one_add_I_mul_ne_zero (ξ : ℝ) : (1 : ℂ) + I * ξ ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this

theorem one_sub_I_mul_ne_zero (ξ : ℝ) : (1 : ℂ) - I * ξ ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this

/-- `(1+ξ²)^s = (1+iξ)^s (1−iξ)^s`. -/
theorem one_add_sq_cpow (ξ : ℝ) (s : ℂ) :
    (((1 + ξ ^ 2 : ℝ)) : ℂ) ^ s = (1 + I * ξ) ^ s * (1 - I * ξ) ^ s := by
  have h1 := one_add_I_mul_ne_zero ξ
  have h2 := one_sub_I_mul_ne_zero ξ
  have hprod : (((1 + ξ ^ 2 : ℝ)) : ℂ) = (1 + I * ξ) * (1 - I * ξ) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have ha1 : |(1 + I * ξ).arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by simp))
  have ha2 : |(1 - I * ξ).arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by simp))
  have hlog : Complex.log ((1 + I * ξ) * (1 - I * ξ)) =
      Complex.log (1 + I * ξ) + Complex.log (1 - I * ξ) := by
    refine Complex.log_mul h1 h2 ⟨?_, ?_⟩
    · have := abs_lt.mp ha1; have := abs_lt.mp ha2; linarith [Real.pi_pos]
    · have := abs_lt.mp ha1; have := abs_lt.mp ha2; linarith [Real.pi_pos]
  rw [hprod, Complex.cpow_def_of_ne_zero (mul_ne_zero h1 h2), Complex.cpow_def_of_ne_zero h1,
    Complex.cpow_def_of_ne_zero h2, hlog, ← Complex.exp_add]
  congr 1
  ring

/-! ## The exponential bound -/

/-- `e^{−u} ≤ δ^δ u^{−δ}` for `u, δ > 0`. -/
theorem exp_neg_le_rpow {u δ : ℝ} (hu : 0 < u) (hδ : 0 < δ) :
    Real.exp (-u) ≤ δ ^ δ * u ^ (-δ) := by
  have h1 : u / δ ≤ Real.exp (u / δ) := by
    have := Real.add_one_le_exp (u / δ - 1)
    have h2 : Real.exp (u / δ - 1) ≤ Real.exp (u / δ) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have h3 : (u / δ) ^ δ ≤ Real.exp u := by
    calc (u / δ) ^ δ ≤ Real.exp (u / δ) ^ δ :=
          Real.rpow_le_rpow (by positivity) h1 hδ.le
      _ = Real.exp u := by rw [← Real.exp_mul, div_mul_cancel₀ _ hδ.ne']
  rw [Real.div_rpow hu.le hδ.le] at h3
  have hupos : 0 < u ^ δ := Real.rpow_pos_of_pos hu δ
  have hdpos : 0 < δ ^ δ := Real.rpow_pos_of_pos hδ δ
  rw [Real.exp_neg, Real.rpow_neg hu.le, ← div_eq_mul_inv]
  rw [le_div_iff₀ hupos, inv_mul_le_iff₀ (Real.exp_pos u)]
  rw [div_le_iff₀ hdpos] at h3
  linarith [mul_comm (Real.exp u) (δ ^ δ)]

/-! ## The kernel -/

/-- The complex rate `2πμ(1+iξ)`. -/
def kuzRate (μ ξ : ℝ) : ℂ := ((2 * Real.pi * μ : ℝ) : ℂ) * (1 + I * ξ)

/-- The parameter `P = 4π²μν/q`. -/
def kuzParam (μ ν q : ℝ) : ℝ := 4 * Real.pi ^ 2 * μ * ν / q

/-- **Kuznetsov's kernel** `(1+ξ²)^{−a₂} y^{α−1} e^{−Ay − P/(Ay)}`, `A = 2πμ(1+iξ)`. -/
def kuzKernel (a₁ a₂ : ℂ) (μ ν q : ℝ) (p : ℝ × ℝ) : ℂ :=
  (((1 + p.2 ^ 2 : ℝ)) : ℂ) ^ (-a₂) *
    invGaussKernel (a₁ - a₂) (kuzRate μ p.2) (kuzParam μ ν q) p.1

theorem kuzRate_re (μ ξ : ℝ) : (kuzRate μ ξ).re = 2 * Real.pi * μ := by
  simp [kuzRate]

theorem normSq_kuzRate (μ ξ : ℝ) :
    Complex.normSq (kuzRate μ ξ) = (2 * Real.pi * μ) ^ 2 * (1 + ξ ^ 2) := by
  simp [kuzRate, Complex.normSq_apply]
  ring

theorem kuzParam_pos {μ ν q : ℝ} (hμ : 0 < μ) (hν : 0 < ν) (hq : 0 < q) : 0 < kuzParam μ ν q := by
  unfold kuzParam; positivity

/-- The pointwise majorant `δ^δ (q/(2πν))^δ · y^{Re α+δ−1} e^{−2πμy} · (1+ξ²)^{δ−Re a₂}`. -/
theorem norm_kuzKernel_le {a₁ a₂ : ℂ} {μ ν q δ : ℝ} (hμ : 0 < μ) (hν : 0 < ν) (hq : 0 < q)
    (hδ : 0 < δ) {y : ℝ} (hy : 0 < y) (ξ : ℝ) :
    ‖kuzKernel a₁ a₂ μ ν q (y, ξ)‖ ≤ δ ^ δ * (q / (2 * Real.pi * ν)) ^ δ *
      ((y ^ ((a₁ - a₂).re + δ - 1) * Real.exp (-(2 * Real.pi * μ * y))) *
        (1 + ξ ^ 2) ^ (δ - a₂.re)) := by
  have hξ : 0 < 1 + ξ ^ 2 := by positivity
  rw [kuzKernel, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hξ, norm_invGaussKernel _ _ _ hy,
    invGaussMajorant, kuzRate_re, normSq_kuzRate, Complex.neg_re]
  set b := 2 * Real.pi * ν / (q * (1 + ξ ^ 2) * y) with hb
  have hbpos : 0 < b := by rw [hb]; positivity
  have hexp : -(2 * Real.pi * μ * y) - kuzParam μ ν q * (2 * Real.pi * μ /
      ((2 * Real.pi * μ) ^ 2 * (1 + ξ ^ 2))) / y = -(2 * Real.pi * μ * y) + -b := by
    rw [hb, kuzParam]
    field_simp
    ring
  rw [hexp, Real.exp_add]
  have hbnd := exp_neg_le_rpow hbpos hδ
  have hb' : b ^ (-δ) = (q / (2 * Real.pi * ν)) ^ δ * (1 + ξ ^ 2) ^ δ * y ^ δ := by
    rw [hb, Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), inv_div,
      Real.div_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) hy.le,
      Real.mul_rpow hq.le hξ.le, Real.div_rpow hq.le (by positivity)]
    ring
  rw [hb'] at hbnd
  have hyσ : y ^ ((a₁ - a₂).re - 1) * y ^ δ = y ^ ((a₁ - a₂).re + δ - 1) := by
    rw [← Real.rpow_add hy]; ring_nf
  have hξσ : (1 + ξ ^ 2) ^ (-a₂.re) * (1 + ξ ^ 2) ^ δ = (1 + ξ ^ 2) ^ (δ - a₂.re) := by
    rw [← Real.rpow_add hξ]; ring_nf
  calc (1 + ξ ^ 2) ^ (-a₂.re) * (y ^ ((a₁ - a₂).re - 1) *
        (Real.exp (-(2 * Real.pi * μ * y)) * Real.exp (-b)))
      ≤ (1 + ξ ^ 2) ^ (-a₂.re) * (y ^ ((a₁ - a₂).re - 1) *
        (Real.exp (-(2 * Real.pi * μ * y)) *
          (δ ^ δ * ((q / (2 * Real.pi * ν)) ^ δ * (1 + ξ ^ 2) ^ δ * y ^ δ)))) := by
        gcongr
    _ = δ ^ δ * (q / (2 * Real.pi * ν)) ^ δ *
        ((y ^ ((a₁ - a₂).re - 1) * y ^ δ * Real.exp (-(2 * Real.pi * μ * y))) *
          ((1 + ξ ^ 2) ^ (-a₂.re) * (1 + ξ ^ 2) ^ δ)) := by ring
    _ = _ := by rw [hyσ, hξσ]

theorem measurable_kuzKernel (a₁ a₂ : ℂ) (μ ν q : ℝ) : Measurable (kuzKernel a₁ a₂ μ ν q) := by
  unfold kuzKernel invGaussKernel kuzRate
  fun_prop

theorem integrableOn_rpow_exp_kuz {τ μ : ℝ} (hτ : 0 < τ) (hμ : 0 < μ) :
    IntegrableOn (fun y : ℝ => y ^ (τ - 1) * Real.exp (-(2 * Real.pi * μ * y))) (Ioi 0) :=
  HTGeometry.integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith) (by positivity)

theorem integrable_one_add_sq_rpow {τ : ℝ} (hτ : 1 / 2 < τ) :
    Integrable (fun ξ : ℝ => (1 + ξ ^ 2) ^ (-τ)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2 * τ)
    (by simp; linarith)
  refine h.congr (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [Real.norm_eq_abs, sq_abs]
  congr 1
  ring

theorem ae_prod_fst_mem_Ioi :
    ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Ioi 0)).prod volume), p.1 ∈ Ioi (0 : ℝ) :=
  (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Ioi (0 : ℝ)))
    (ν := (volume : Measure ℝ))).ae (ae_restrict_mem measurableSet_Ioi)

/-- **Absolute convergence** of the double integral, with a bound linear in `q^δ`. -/
theorem integrable_kuzKernel {a₁ a₂ : ℂ} {μ ν q δ : ℝ} (hμ : 0 < μ) (hν : 0 < ν) (hq : 0 < q)
    (hδ : 0 < δ) (hδ₁ : a₂.re - a₁.re < δ) (hδ₂ : δ < a₂.re - 1 / 2) :
    Integrable (kuzKernel a₁ a₂ μ ν q) ((volume.restrict (Ioi 0)).prod volume) := by
  have hτ : 0 < (a₁ - a₂).re + δ := by rw [Complex.sub_re]; linarith
  have h1 := integrableOn_rpow_exp_kuz hτ hμ
  have h2 := integrable_one_add_sq_rpow (τ := a₂.re - δ) (by linarith)
  have hprod := (h1.mul_prod h2).const_mul (δ ^ δ * (q / (2 * Real.pi * ν)) ^ δ)
  refine hprod.mono' (measurable_kuzKernel a₁ a₂ μ ν q).aestronglyMeasurable ?_
  filter_upwards [ae_prod_fst_mem_Ioi] with p hp
  have := norm_kuzKernel_le (a₁ := a₁) (a₂ := a₂) hμ hν hq hδ hp p.2
  rwa [show δ - a₂.re = -(a₂.re - δ) by ring] at this

theorem integral_norm_kuzKernel_le {a₁ a₂ : ℂ} {μ ν q δ : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
    (hq : 0 < q) (hδ : 0 < δ) (hδ₁ : a₂.re - a₁.re < δ) (hδ₂ : δ < a₂.re - 1 / 2) :
    ∫ p, ‖kuzKernel a₁ a₂ μ ν q p‖ ∂((volume.restrict (Ioi 0)).prod volume) ≤
      δ ^ δ * (2 * Real.pi * ν)⁻¹ ^ δ *
        ((∫ y in Ioi (0 : ℝ), y ^ ((a₁ - a₂).re + δ - 1) * Real.exp (-(2 * Real.pi * μ * y))) *
          ∫ ξ : ℝ, (1 + ξ ^ 2) ^ (δ - a₂.re)) * q ^ δ := by
  have hτ : 0 < (a₁ - a₂).re + δ := by rw [Complex.sub_re]; linarith
  have h1 := integrableOn_rpow_exp_kuz hτ hμ
  have h2 := integrable_one_add_sq_rpow (τ := a₂.re - δ) (by linarith)
  simp only [show δ - a₂.re = -(a₂.re - δ) by ring]
  have hprod := (h1.mul_prod h2).const_mul (δ ^ δ * (q / (2 * Real.pi * ν)) ^ δ)
  have hle : ∫ p, ‖kuzKernel a₁ a₂ μ ν q p‖ ∂((volume.restrict (Ioi 0)).prod volume) ≤
      ∫ p, δ ^ δ * (q / (2 * Real.pi * ν)) ^ δ *
        ((p.1 ^ ((a₁ - a₂).re + δ - 1) * Real.exp (-(2 * Real.pi * μ * p.1))) *
          (1 + p.2 ^ 2) ^ (-(a₂.re - δ))) ∂((volume.restrict (Ioi 0)).prod volume) := by
    refine integral_mono_ae (integrable_kuzKernel hμ hν hq hδ hδ₁ hδ₂).norm hprod ?_
    filter_upwards [ae_prod_fst_mem_Ioi] with p hp
    have := norm_kuzKernel_le (a₁ := a₁) (a₂ := a₂) hμ hν hq hδ hp p.2
    rwa [show δ - a₂.re = -(a₂.re - δ) by ring] at this
  refine hle.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_prod_mul (fun y : ℝ =>
      y ^ ((a₁ - a₂).re + δ - 1) * Real.exp (-(2 * Real.pi * μ * y)))
    (fun ξ : ℝ => (1 + ξ ^ 2) ^ (-(a₂.re - δ))),
    Real.div_rpow hq.le (by positivity), div_eq_mul_inv, Real.inv_rpow (by positivity)]
  ring

/-! ## Evaluation -/

/-- The inner `y`-integral: the inverse-Gaussian Mellin integral with the rate `2πμ(1+iξ)`. -/
theorem integral_kuzKernel_y {a₁ a₂ : ℂ} {μ ν q : ℝ} (hμ : 0 < μ) (hν : 0 < ν) (hq : 0 < q)
    (ξ : ℝ) :
    ∫ y in Ioi (0 : ℝ), kuzKernel a₁ a₂ μ ν q (y, ξ) =
      2 * (kuzParam μ ν q : ℂ) ^ ((a₁ - a₂) / 2) * ((2 * Real.pi * μ : ℝ) : ℂ) ^ (-(a₁ - a₂)) *
        HTGeometry.modifiedBesselKOrder (2 * Real.sqrt (kuzParam μ ν q)) (a₁ - a₂) *
          ((1 + I * ξ) ^ (-a₁) * (1 - I * ξ) ^ (-a₂)) := by
  simp only [kuzKernel]
  rw [integral_const_mul, integral_invGaussKernel _ (kuzParam_pos hμ hν hq)
    (by rw [kuzRate_re]; positivity), kuzRate,
    ofReal_pos_mul_cpow' (by positivity) (one_add_I_mul_ne_zero ξ), one_add_sq_cpow]
  have hc : (1 + I * ξ) ^ (-a₂) * (1 + I * ξ) ^ (-(a₁ - a₂)) = (1 + I * ξ) ^ (-a₁) := by
    rw [← Complex.cpow_add _ _ (one_add_I_mul_ne_zero ξ)]
    congr 1; ring
  rw [← hc]
  ring

/-- The value `2 P^{α/2} (2πμ)^{−α} K_α(2√P) · π 2^{2−a₁−a₂} Γ(a₁+a₂−1)/(Γ(a₁)Γ(a₂))` of Kuznetsov's
double integral, `α = a₁ − a₂`, `P = 4π²μν/q`. -/
def kuzValue (a₁ a₂ : ℂ) (μ ν q : ℝ) : ℂ :=
  2 * (kuzParam μ ν q : ℂ) ^ ((a₁ - a₂) / 2) * ((2 * Real.pi * μ : ℝ) : ℂ) ^ (-(a₁ - a₂)) *
    HTGeometry.modifiedBesselKOrder (2 * Real.sqrt (kuzParam μ ν q)) (a₁ - a₂) *
      (Real.pi * 2 ^ (2 - (a₁ + a₂)) * Complex.Gamma (a₁ + a₂ - 1) /
        (Complex.Gamma a₁ * Complex.Gamma a₂))

/-- **Kuznetsov's double integral.** -/
theorem integral_integral_kuzKernel {a₁ a₂ : ℂ} (ha₁ : 1 / 2 < a₁.re) (ha₂ : 1 < a₂.re)
    {μ ν q : ℝ} (hμ : 0 < μ) (hν : 0 < ν) (hq : 0 < q) :
    ∫ y in Ioi (0 : ℝ), ∫ ξ : ℝ, kuzKernel a₁ a₂ μ ν q (y, ξ) = kuzValue a₁ a₂ μ ν q := by
  unfold kuzValue
  set δ := (max 0 (a₂.re - a₁.re) + (a₂.re - 1 / 2)) / 2 with hδdef
  have hm0 := le_max_left 0 (a₂.re - a₁.re)
  have hm1 := le_max_right 0 (a₂.re - a₁.re)
  have hm2 : max 0 (a₂.re - a₁.re) < a₂.re - 1 / 2 := max_lt (by linarith) (by linarith)
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hδ₁ : a₂.re - a₁.re < δ := by rw [hδdef]; linarith
  have hδ₂ : δ < a₂.re - 1 / 2 := by rw [hδdef]; linarith
  have hint := integrable_kuzKernel (a₁ := a₁) (a₂ := a₂) hμ hν hq hδ hδ₁ hδ₂
  rw [integral_integral_swap (f := fun y ξ => kuzKernel a₁ a₂ μ ν q (y, ξ)) hint]
  simp_rw [integral_kuzKernel_y hμ hν hq]
  rw [integral_const_mul, integral_one_add_I_mul_cpow (by linarith) ha₂]

end

end GaloisForLFunctions.RHTower.Kuznetsov
