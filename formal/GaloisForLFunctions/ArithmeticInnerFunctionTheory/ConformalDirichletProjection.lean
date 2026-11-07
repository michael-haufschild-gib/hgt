import GaloisForLFunctions.ArithmeticInnerFunctionTheory.NearExtremalMollifiersAreRigid

/-!+# Conformal coordinates for Dirichlet modes

The chart centred at one sends a Dirichlet mode with logarithmic frequency `t` to
`exp(-t/(1-z))`. Its Hardy coefficients are the conformal–Dirichlet mixed moments.
Horizontal translation acts by an explicit fractional linear map on the disc.
-/

open Complex Metric Filter Topology MeasureTheory Set Finset
open scoped Real ComplexConjugate

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open _root_.RHTower

noncomputable section

/-- Translation by `δ` in the half-plane, expressed in the chart centred at one. -/
def translatedDiscCoord (δ : ℝ) (z : ℂ) : ℂ :=
  ((δ : ℂ) + (1 - (δ : ℂ)) * z) / (1 + (δ : ℂ) - (δ : ℂ) * z)

theorem blaschkeCoord_one_translate {δ : ℝ} {z : ℂ} (hz : z ≠ 1)
    (hden : 1 + (δ : ℂ) - (δ : ℂ) * z ≠ 0) :
    blaschkeCoord 1 (discChart 1 z + (δ : ℂ)) = translatedDiscCoord δ z := by
  have hz' : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
  rw [blaschkeCoord_one, discChart_one, translatedDiscCoord]
  field_simp
  <;> ring

@[simp] theorem translatedDiscCoord_zero (z : ℂ) : translatedDiscCoord 0 z = z := by
  simp [translatedDiscCoord]

@[simp] theorem translatedDiscCoord_at_zero (δ : ℝ) :
    translatedDiscCoord δ 0 = (δ : ℂ) / (1 + (δ : ℂ)) := by
  simp [translatedDiscCoord]

/-- Nonnegative translation has no pole on the closed disc. -/
theorem translatedDiscCoord_den_ne_zero {δ : ℝ} (hδ : 0 ≤ δ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    1 + (δ : ℂ) - (δ : ℂ) * z ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  have hzre : z.re ≤ 1 := (Complex.re_le_norm z).trans hz
  simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re] at hr
  nlinarith only [hδ, hzre, hr]

/-- The Dirichlet mode in the disc chart, with logarithmic frequency `t`. -/
def dirichletDisc (t : ℝ) (z : ℂ) : ℂ := Complex.exp (-(t : ℂ) * (1 - z)⁻¹)

theorem dirichletDisc_zero (t : ℝ) : dirichletDisc t 0 = Complex.exp (-(t : ℂ)) := by
  simp [dirichletDisc]

theorem differentiableAt_dirichletDisc (t : ℝ) {z : ℂ} (hz : z ≠ 1) :
    DifferentiableAt ℂ (dirichletDisc t) z := by
  have hi : DifferentiableAt ℂ (fun u : ℂ => (1 - u)⁻¹) z :=
    ((differentiableAt_const _).sub differentiableAt_id).inv (sub_ne_zero.mpr hz.symm)
  exact Complex.differentiable_exp.differentiableAt.comp z (hi.const_mul _)

theorem measurable_dirichletDisc (t : ℝ) : Measurable (dirichletDisc t) := by
  unfold dirichletDisc
  fun_prop

/-- The singular boundary value at one is harmless: the whole closed disc is bounded by one. -/
theorem norm_dirichletDisc_le_one {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖dirichletDisc t z‖ ≤ 1 := by
  by_cases hz1 : z = 1
  · simp [dirichletDisc, hz1]
  have hr := one_half_le_re_inv hz hz1
  rw [dirichletDisc, Complex.norm_exp, Real.exp_le_one_iff]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
    Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
  nlinarith only [ht, hr]

theorem isHardyDisc_dirichletDisc {t : ℝ} (ht : 0 ≤ t) : IsHardyDisc (dirichletDisc t) := by
  refine ⟨fun z hz => (differentiableAt_dirichletDisc t hz).differentiableWithinAt,
    measurable_dirichletDisc t, ?_, ?_, ?_⟩
  · refine ⟨4, by norm_num, fun z hz hz1 => ?_⟩
    have hd : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1.symm)
    have h2 : ‖1 - z‖ ≤ 2 := by
      calc ‖1 - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
        _ ≤ 2 := by rw [norm_one]; linarith
    have h4 : ‖1 - z‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (1 - z)]
    exact (norm_dirichletDisc_le_one ht hz).trans ((le_div_iff₀ (by positivity)).mpr (by simpa using h4))
  · refine ⟨1, fun x hx hx1 => norm_dirichletDisc_le_one ht ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ x)]
    exact hx1.le
  · have hm : Measurable (fun θ : ℝ => ‖dirichletDisc t (circleMap 0 1 θ)‖ ^ 2) :=
      ((measurable_dirichletDisc t).comp (continuous_circleMap 0 1).measurable).norm.pow_const 2
    refine (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0
      (2 * Real.pi)).mono_fun hm.aestronglyMeasurable (Eventually.of_forall fun θ => ?_)
    have hn := norm_dirichletDisc_le_one ht (norm_circleMap_zero_one θ).le
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_one]
    nlinarith only [hn, norm_nonneg (dirichletDisc t (circleMap 0 1 θ))]

/-- Peeling is an exact finite Taylor decomposition away from the origin. -/
theorem peel_decomposition (Φ : ℂ → ℂ) (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    Φ z = (∑ k ∈ Finset.range n, z ^ k * taylorCoeff Φ k) + z ^ n * peel Φ n z := by
  induction n with
  | zero => simp [peel_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, peel_succ, dslope_of_ne _ hz, slope_def_module,
      sub_zero, smul_eq_mul, pow_succ]
    rw [taylorCoeff]
    calc Φ z = (∑ k ∈ Finset.range n, z ^ k * taylorCoeff Φ k) + z ^ n * peel Φ n z := ih
      _ = _ := by field_simp; ring

/-- The squared distance to the first `n` conformal coefficients is the exact Parseval tail. -/
theorem IsHardyDisc.projection_remainder {Φ : ℂ → ℂ} (h : IsHardyDisc Φ) (n : ℕ) :
    Real.circleAverage (fun z =>
      ‖Φ z - ∑ k ∈ Finset.range n, z ^ k * taylorCoeff Φ k‖ ^ 2) 0 1 =
        Real.circleAverage (fun z => ‖Φ z‖ ^ 2) 0 1 -
          ∑ k ∈ Finset.range n, ‖taylorCoeff Φ k‖ ^ 2 := by
  have he : Real.circleAverage (fun z =>
      ‖Φ z - ∑ k ∈ Finset.range n, z ^ k * taylorCoeff Φ k‖ ^ 2) 0 1 =
      Real.circleAverage (fun z => ‖peel Φ n z‖ ^ 2) 0 1 := by
    apply Real.circleAverage_congr_sphere
    intro z hz
    have hn : ‖z‖ = 1 := by simpa using hz
    have hz0 : z ≠ 0 := by intro he; simp [he] at hn
    have hd := peel_decomposition Φ n hz0
    have hd' : Φ z - ∑ k ∈ Finset.range n, z ^ k * taylorCoeff Φ k = z ^ n * peel Φ n z := by
      linear_combination hd
    rw [hd', norm_mul, norm_pow, hn, one_pow, one_mul]
  rw [he, h.circleAverage_norm_sq_eq n]
  ring

private theorem circleAverage_conj_pow_succ (n : ℕ) :
    Real.circleAverage (fun z : ℂ => conj (z ^ (n + 1))) 0 1 = 0 := by
  have hi : CircleIntegrable (fun z : ℂ => z ^ (n + 1)) 0 1 :=
    (continuous_id.pow _).continuousOn.circleIntegrable (by norm_num)
  have hd : DiffContOnCl ℂ (fun z : ℂ => z ^ (n + 1)) (ball 0 |(1 : ℝ)|) :=
    ⟨by fun_prop, by fun_prop⟩
  have hm : Real.circleAverage (fun z : ℂ => z ^ (n + 1)) 0 1 = 0 := by
    simpa using hd.circleAverage
  have hc := (Complex.conjCLE : ℂ →L[ℝ] ℂ).circleAverage_comp_comm hi
  simpa only [Function.comp_def, Complex.conjCLE_apply, hm, map_zero] using hc

theorem IsHardyDisc.circleIntegrable_conj_pow_mul {Φ : ℂ → ℂ} (h : IsHardyDisc Φ) (n : ℕ) :
    CircleIntegrable (fun z => conj (z ^ n) * Φ z) 0 1 := by
  exact h.circleIntegrable.mul_of_continuousOn (by fun_prop)

/-- A conformal monomial reads precisely one Hardy coefficient. -/
theorem IsHardyDisc.circleAverage_conj_pow_mul {Φ : ℂ → ℂ} (h : IsHardyDisc Φ) (n : ℕ) :
    Real.circleAverage (fun z => conj (z ^ n) * Φ z) 0 1 = taylorCoeff Φ n := by
  induction n generalizing Φ with
  | zero => simpa [taylorCoeff, peel_zero] using h.circleAverage_eq
  | succ n ih =>
    have hb : Real.circleAverage (fun z => conj (z ^ (n + 1)) * Φ z) 0 1 =
        Real.circleAverage (fun z => Φ 0 * conj (z ^ (n + 1)) +
          conj (z ^ n) * dslope Φ 0 z) 0 1 := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      have hn : ‖z‖ = 1 := by simpa using hz
      have hz0 : z ≠ 0 := by intro he; simp [he] at hn
      have hcz : conj z * z = 1 := by rw [Complex.conj_mul', hn]; norm_num
      have hd : dslope Φ 0 z * z = Φ z - Φ 0 := by
        rw [dslope_of_ne _ hz0, slope_def_module, sub_zero, smul_eq_mul]
        field_simp
      rw [pow_succ, map_mul]
      linear_combination -(conj (z ^ n) * conj z) * hd +
        (conj (z ^ n) * dslope Φ 0 z) * hcz
    have hconst : CircleIntegrable (fun z : ℂ => Φ 0 * conj (z ^ (n + 1))) 0 1 :=
      (by fun_prop : Continuous (fun z : ℂ => Φ 0 * conj (z ^ (n + 1)))).continuousOn.circleIntegrable
        (by norm_num)
    rw [hb, Real.circleAverage_fun_add hconst (h.dslope.circleIntegrable_conj_pow_mul n)]
    have hc : Real.circleAverage (fun z : ℂ => Φ 0 * conj (z ^ (n + 1))) 0 1 = 0 := by
      change Real.circleAverage (fun z : ℂ => Φ 0 • conj (z ^ (n + 1))) 0 1 = 0
      rw [Real.circleAverage_fun_smul, circleAverage_conj_pow_succ, smul_zero]
    rw [hc, zero_add, ih h.dslope]
    unfold taylorCoeff peel
    rw [Function.iterate_succ_apply]
    rfl

/-- Complex change of variables from the unit circle to the Poisson line. -/
theorem circleAverage_complex_eq_poisson {F : ℝ → ℂ} {g : ℂ → ℂ}
    (hg : CircleIntegrable g 0 1)
    (hline : ∀ τ : ℝ, g (circleMap 0 1 (criticalLineAngle τ)) = F τ) :
    Integrable (fun τ : ℝ => F τ * (halfPlanePoissonKernel 1 τ : ℂ)) ∧
      Real.circleAverage g 0 1 =
        ∫ τ : ℝ, F τ * (halfPlanePoissonKernel 1 τ : ℂ) := by
  have hr := circleAverage_shift_eq_poisson (s0 := 1) (by norm_num)
    (fun τ => (F τ).re) (fun z => (g z).re) (fun τ => by simpa using congrArg Complex.re (hline τ))
  have hi := circleAverage_shift_eq_poisson (s0 := 1) (by norm_num)
    (fun τ => (F τ).im) (fun z => (g z).im) (fun τ => by simpa using congrArg Complex.im (hline τ))
  have hgr : CircleIntegrable (fun z => (g z).re) 0 1 :=
    ⟨Complex.reCLM.integrable_comp hg.1, Complex.reCLM.integrable_comp hg.2⟩
  have hgi : CircleIntegrable (fun z => (g z).im) 0 1 :=
    ⟨Complex.imCLM.integrable_comp hg.1, Complex.imCLM.integrable_comp hg.2⟩
  have hint : Integrable (fun τ : ℝ => F τ * (halfPlanePoissonKernel 1 τ : ℂ)) := by
    refine (((hr.1.mp hgr).ofReal).add (((hi.1.mp hgi).ofReal).mul_const I)).congr ?_
    exact Eventually.of_forall fun τ => by
      apply Complex.ext <;> simp <;> ring
  refine ⟨hint, ?_⟩
  apply Complex.ext
  · have hc := Complex.reCLM.circleAverage_comp_comm hg
    rw [← integral_re hint]
    simp only [RCLike.re_eq_complex_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    rw [← hr.2]
    exact hc.symm
  · have hc := Complex.imCLM.circleAverage_comp_comm hg
    rw [← integral_im hint]
    simp only [RCLike.im_eq_complex_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_add]
    rw [← hi.2]
    exact hc.symm

/-- A logarithmic Dirichlet mode on the line `Re s = ½ + δ`. -/
def dirichletLineMode (t δ τ : ℝ) : ℂ :=
  Complex.exp (-(t : ℂ) * (1 / 2 + (δ : ℂ) + (τ : ℂ) * I))

/-- Horizontal translation acts diagonally on Dirichlet modes. -/
theorem dirichletLineMode_shift (t δ τ : ℝ) :
    dirichletLineMode t δ τ = (Real.exp (-δ * t) : ℂ) * dirichletLineMode t 0 τ := by
  rw [dirichletLineMode, dirichletLineMode, ← Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem dirichletDisc_circleMap (t τ : ℝ) :
    dirichletDisc t (circleMap 0 1 (criticalLineAngle τ)) = dirichletLineMode t 0 τ := by
  rw [dirichletDisc, ← discChart_one, discChart_circleMap, dirichletLineMode]
  congr 1
  norm_num

/-- Exact mixed inner product of a conformal monomial and a Dirichlet mode. -/
theorem integral_conformal_dirichlet_mode {t : ℝ} (ht : 0 ≤ t) (δ : ℝ) (k : ℕ) :
    (∫ τ : ℝ, conj (blaschkeCoord 1 (1 / 2 + (τ : ℂ) * I) ^ k) *
        dirichletLineMode t δ τ * (halfPlanePoissonKernel 1 τ : ℂ)) =
      (Real.exp (-δ * t) : ℂ) * taylorCoeff (dirichletDisc t) k := by
  have hH := isHardyDisc_dirichletDisc ht
  have hchange := circleAverage_complex_eq_poisson (hH.circleIntegrable_conj_pow_mul k)
    (F := fun τ => conj (blaschkeCoord 1 (1 / 2 + (τ : ℂ) * I) ^ k) *
      dirichletLineMode t 0 τ) (fun τ => by
        have hb := blaschkeCoord_line (w := 1) (by norm_num) τ
        norm_num at hb
        rw [dirichletDisc_circleMap, hb])
  have he : (fun τ : ℝ => conj (blaschkeCoord 1 (1 / 2 + (τ : ℂ) * I) ^ k) *
      dirichletLineMode t δ τ * (halfPlanePoissonKernel 1 τ : ℂ)) =
      fun τ => (Real.exp (-δ * t) : ℂ) *
        (conj (blaschkeCoord 1 (1 / 2 + (τ : ℂ) * I) ^ k) *
          dirichletLineMode t 0 τ * (halfPlanePoissonKernel 1 τ : ℂ)) := by
    funext τ
    rw [dirichletLineMode_shift]
    ring
  rw [he, integral_const_mul, ← hchange.2, hH.circleAverage_conj_pow_mul]

theorem norm_dirichletLineMode (t δ τ : ℝ) :
    ‖dirichletLineMode t δ τ‖ = Real.exp (-(1 / 2 + δ) * t) := by
  rw [dirichletLineMode, Complex.norm_exp]
  congr 1
  norm_num [Complex.mul_re]
  ring

/-- Dirichlet modes have constant boundary modulus; the conformal energy is `exp(-t)`. -/
theorem circleAverage_norm_sq_dirichletDisc (t : ℝ) :
    Real.circleAverage (fun z => ‖dirichletDisc t z‖ ^ 2) 0 1 = Real.exp (-t) := by
  have hline (τ : ℝ) :
      ‖dirichletDisc t (circleMap 0 1 (criticalLineAngle τ))‖ ^ 2 = Real.exp (-t) := by
    rw [dirichletDisc_circleMap, norm_dirichletLineMode, ← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have h1 := circleAverage_shift_eq_poisson (s0 := 1) (by norm_num)
    (fun _ => Real.exp (-t)) (fun z => ‖dirichletDisc t z‖ ^ 2) (fun τ => by simpa using hline τ)
  have h2 := circleAverage_shift_eq_poisson (s0 := 1) (by norm_num)
    (fun _ => Real.exp (-t)) (fun _ => Real.exp (-t)) (fun _ => rfl)
  rw [h1.2, ← h2.2, Real.circleAverage_const]

/-- Exact conformal projection error for one Dirichlet frequency. -/
theorem dirichletDisc_projection_remainder {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    Real.circleAverage (fun z =>
      ‖dirichletDisc t z - ∑ k ∈ Finset.range n, z ^ k * taylorCoeff (dirichletDisc t) k‖ ^ 2)
      0 1 = Real.exp (-t) - ∑ k ∈ Finset.range n, ‖taylorCoeff (dirichletDisc t) k‖ ^ 2 := by
  rw [(isHardyDisc_dirichletDisc ht).projection_remainder, circleAverage_norm_sq_dirichletDisc]

/-- Every finite Laguerre coefficient energy is bounded by the exact Dirichlet energy. -/
theorem dirichletDisc_coefficient_energy_le {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    ∑ k ∈ Finset.range n, ‖taylorCoeff (dirichletDisc t) k‖ ^ 2 ≤ Real.exp (-t) := by
  simpa only [circleAverage_norm_sq_dirichletDisc] using
    (isHardyDisc_dirichletDisc ht).sum_norm_sq_le n

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
