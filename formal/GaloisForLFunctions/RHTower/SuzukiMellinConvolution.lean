import Mathlib.Analysis.MellinTransform

open Complex MeasureTheory Set

noncomputable section

namespace RHTower

/-- Multiplicative convolution on the positive half-line, with Haar element `dy / y`. -/
def positiveMellinConvolution (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y in Ioi (0 : ℝ), f y * g (x / y) / y

private theorem measurable_mellinProductKernel
    {f g : ℝ → ℂ} (hf : Measurable f) (hg : Measurable g) (s : ℂ) :
    Measurable fun p : ℝ × ℝ =>
      (p.2 : ℂ) ^ (s - 1) * (f p.1 * g (p.2 / p.1) / p.1) := by
  fun_prop

private theorem mellinProductKernel_integrable
    {f g : ℝ → ℂ} (hfmeas : Measurable f) (hgmeas : Measurable g) {s : ℂ}
    (hf : MellinConvergent f s) (hg : MellinConvergent g s) :
    Integrable (fun p : ℝ × ℝ =>
      (p.2 : ℂ) ^ (s - 1) * (f p.1 * g (p.2 / p.1) / p.1))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let F : ℝ × ℝ → ℂ := fun p =>
    (p.2 : ℂ) ^ (s - 1) * (f p.1 * g (p.2 / p.1) / p.1)
  have hFmeas : AEStronglyMeasurable F (mu.prod mu) := by
    exact (measurable_mellinProductKernel hfmeas hgmeas s).aestronglyMeasurable
  rw [integrable_prod_iff hFmeas]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hypos : 0 < y := hy
    have hscale : MellinConvergent (fun x : ℝ => g (x / y)) s := by
      have h := (MellinConvergent.comp_mul_left (f := g) (s := s)
        (a := y⁻¹) (inv_pos.mpr hypos)).2 hg
      convert h using 1
      funext x
      rw [div_eq_mul_inv, mul_comm]
    have hconst := hscale.const_smul (f y / y)
    have hconv : IntegrableOn (fun x : ℝ =>
        (x : ℂ) ^ (s - 1) * (f y * g (x / y) / y)) (Ioi 0) := by
      refine hconst.congr ?_
      filter_upwards with x
      simp only [smul_eq_mul]
      ring
    simpa only [mu, IntegrableOn] using hconv
  · have hbaseF : IntegrableOn (fun y : ℝ =>
        (y : ℂ) ^ (s - 1) * f y) (Ioi 0) := hf
    have hbaseG : IntegrableOn (fun x : ℝ =>
        (x : ℂ) ^ (s - 1) * g x) (Ioi 0) := hg
    have hnormF : IntegrableOn (fun y : ℝ =>
        ‖(y : ℂ) ^ (s - 1) * f y‖) (Ioi 0) := hbaseF.norm
    have hnormG : IntegrableOn (fun x : ℝ =>
        ‖(x : ℂ) ^ (s - 1) * g x‖) (Ioi 0) := hbaseG.norm
    let C : ℝ := ∫ x in Ioi (0 : ℝ), ‖(x : ℂ) ^ (s - 1) * g x‖
    have hslice : ∀ y : ℝ, 0 < y →
        (∫ x in Ioi (0 : ℝ), ‖F (y, x)‖) =
          ‖(y : ℂ) ^ (s - 1) * f y‖ * C := by
      intro y hy
      have hyC : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
      have hcpow : (y : ℂ) ^ (s - 1) ≠ 0 := by
        exact cpow_ne_zero_iff.mpr (Or.inl hyC)
      have hchange := integral_comp_mul_left_Ioi
        (g := fun x : ℝ => ‖(x : ℂ) ^ (s - 1) * g x‖) 0 hy
      rw [mul_zero] at hchange
      have hpoint : ∀ x : ℝ, 0 < x →
          ‖F (y, y * x)‖ =
            ‖(y : ℂ) ^ (s - 1) * f y‖ / y *
              ‖(x : ℂ) ^ (s - 1) * g x‖ := by
        intro x hx
        simp only [F, norm_mul, norm_div, norm_real]
        rw [mul_div_cancel_left₀ x hy.ne', ofReal_mul,
          mul_cpow_ofReal_nonneg hy.le hx.le, norm_mul]
        have hyNorm : ‖(y : ℂ) ^ (s - 1)‖ ≠ 0 := norm_ne_zero_iff.mpr hcpow
        field_simp
        rw [Real.norm_of_nonneg hy.le]
        field_simp
      calc
        (∫ x in Ioi (0 : ℝ), ‖F (y, x)‖)
            = y * ∫ x in Ioi (0 : ℝ), ‖F (y, y * x)‖ := by
                rw [integral_comp_mul_left_Ioi (g := fun x : ℝ => ‖F (y, x)‖) 0 hy,
                  mul_zero]
                simp only [smul_eq_mul]
                field_simp
        _ = y * ∫ x in Ioi (0 : ℝ),
              (‖(y : ℂ) ^ (s - 1) * f y‖ / y) *
                ‖(x : ℂ) ^ (s - 1) * g x‖ := by
              congr 1
              apply setIntegral_congr_fun measurableSet_Ioi
              intro x hx
              exact hpoint x hx
        _ = ‖(y : ℂ) ^ (s - 1) * f y‖ * C := by
              rw [integral_const_mul]
              dsimp only [C]
              field_simp
    have houter : IntegrableOn (fun y : ℝ =>
        ‖(y : ℂ) ^ (s - 1) * f y‖ * C) (Ioi 0) := hnormF.mul_const C
    refine houter.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    symm
    change (∫ x in Ioi (0 : ℝ), ‖F (y, x)‖) = _
    exact hslice y hy

/-- Mellin's product theorem for multiplicative convolution, including absolute convergence. -/
theorem hasMellin_positiveMellinConvolution
    {f g : ℝ → ℂ} (hfmeas : Measurable f) (hgmeas : Measurable g) {s : ℂ}
    (hf : MellinConvergent f s) (hg : MellinConvergent g s) :
    HasMellin (positiveMellinConvolution f g) s (mellin f s * mellin g s) := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let F : ℝ × ℝ → ℂ := fun p =>
    (p.2 : ℂ) ^ (s - 1) * (f p.1 * g (p.2 / p.1) / p.1)
  have hF : Integrable F (mu.prod mu) := by
    exact mellinProductKernel_integrable hfmeas hgmeas hf hg
  have hinner : ∀ y : ℝ, 0 < y →
      (∫ x in Ioi (0 : ℝ), F (y, x)) =
        (y : ℂ) ^ (s - 1) * f y * mellin g s := by
    intro y hy
    have hyC : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
    have hscale0 := mellin_comp_mul_left g s (a := y⁻¹) (inv_pos.mpr hy)
    have hscale : mellin (fun x : ℝ => g (x / y)) s =
        (y : ℂ) ^ s * mellin g s := by
      have hfun : (fun x : ℝ => g (x / y)) = fun x => g (y⁻¹ * x) := by
        funext x
        rw [div_eq_mul_inv, mul_comm]
      rw [hfun, hscale0]
      congr 1
      rw [ofReal_inv, inv_cpow (y : ℂ) (-s) (by
        rw [arg_ofReal_of_nonneg hy.le]
        exact Real.pi_ne_zero.symm), cpow_neg, inv_inv]
    have hpow : (y : ℂ) ^ s / y = (y : ℂ) ^ (s - 1) := by
      rw [cpow_sub s 1 hyC, cpow_one]
    calc
      (∫ x in Ioi (0 : ℝ), F (y, x))
          = (f y / y) * ∫ x in Ioi (0 : ℝ),
              (x : ℂ) ^ (s - 1) * g (x / y) := by
            rw [← integral_const_mul]
            apply setIntegral_congr_fun measurableSet_Ioi
            intro x hx
            simp only [F]
            ring
      _ = (f y / y) * mellin (fun x : ℝ => g (x / y)) s := by
            rfl
      _ = (f y / y) * ((y : ℂ) ^ s * mellin g s) := by rw [hscale]
      _ = (y : ℂ) ^ (s - 1) * f y * mellin g s := by
            calc
              (f y / y) * ((y : ℂ) ^ s * mellin g s)
                  = ((y : ℂ) ^ s / y) * f y * mellin g s := by ring
              _ = (y : ℂ) ^ (s - 1) * f y * mellin g s := by rw [hpow]
  constructor
  · rw [MellinConvergent]
    refine hF.integral_prod_right.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change (∫ y in Ioi (0 : ℝ), F (y, x)) =
      (x : ℂ) ^ (s - 1) * positiveMellinConvolution f g x
    rw [positiveMellinConvolution, ← integral_const_mul]
  · rw [mellin]
    simp only [positiveMellinConvolution]
    simp only [smul_eq_mul]
    calc
    (∫ x in Ioi (0 : ℝ),
        (x : ℂ) ^ (s - 1) * ∫ y in Ioi (0 : ℝ), f y * g (x / y) / y)
        = ∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), F (y, x) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          change (x : ℂ) ^ (s - 1) *
              (∫ y in Ioi (0 : ℝ), f y * g (x / y) / y) =
            ∫ y in Ioi (0 : ℝ),
              (x : ℂ) ^ (s - 1) * (f y * g (x / y) / y)
          rw [integral_const_mul]
    _ = ∫ p, F p ∂(mu.prod mu) := by
          exact (integral_prod_symm F hF).symm
    _ = ∫ y in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), F (y, x) := by
          exact integral_prod F hF
    _ = ∫ y in Ioi (0 : ℝ),
          ((y : ℂ) ^ (s - 1) * f y) * mellin g s := by
          apply setIntegral_congr_ae measurableSet_Ioi
          filter_upwards with y
          intro hy
          exact hinner y hy
    _ = (∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) * f y) * mellin g s := by
          rw [integral_mul_const]
    _ = mellin f s * mellin g s := rfl

/-- Value-only form of Mellin's multiplicative-convolution product theorem. -/
theorem mellin_positiveMellinConvolution
    {f g : ℝ → ℂ} (hfmeas : Measurable f) (hgmeas : Measurable g) {s : ℂ}
    (hf : MellinConvergent f s) (hg : MellinConvergent g s) :
    mellin (positiveMellinConvolution f g) s = mellin f s * mellin g s :=
  (hasMellin_positiveMellinConvolution hfmeas hgmeas hf hg).2

end RHTower
