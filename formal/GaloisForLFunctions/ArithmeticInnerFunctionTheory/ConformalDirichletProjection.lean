import GaloisForLFunctions.ArithmeticInnerFunctionTheory.NearExtremalMollifiersAreRigid
import GaloisForLFunctions.HTGeometry.ReflectedDividedDifference
import GaloisForLFunctions.HTGeometry.CaratheodoryCoefficient

/-! # Conformal coordinates for Dirichlet modes

The chart centred at one sends a Dirichlet mode with logarithmic frequency `t` to
`exp(-t/(1-z))`. Its Hardy coefficients are the conformal–Dirichlet mixed moments.
Horizontal translation acts by an explicit fractional linear map on the disc.
-/

open Complex Metric Filter Topology MeasureTheory Set Finset
open scoped Real ComplexConjugate NNReal

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open _root_.RHTower

noncomputable section

/-- Translation by `δ` in the half-plane, expressed in the chart centred at one. -/
def translatedDiscCoord (δ : ℝ) (z : ℂ) : ℂ :=
  ((δ : ℂ) + (1 - (δ : ℂ)) * z) / (1 + (δ : ℂ) - (δ : ℂ) * z)

theorem blaschkeCoord_one_translate {δ : ℝ} {z : ℂ} (hz : z ≠ 1) :
    blaschkeCoord 1 (discChart 1 z + (δ : ℂ)) = translatedDiscCoord δ z := by
  have hz' : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
  rw [blaschkeCoord_one, discChart_one, translatedDiscCoord]
  field_simp
  ring

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

/-- Bounded holomorphic disc data belong to the Hardy class used by the Szegő budgets. -/
theorem isHardyDisc_of_bounded {Φ : ℂ → ℂ} {M : ℝ}
    (hdiff : DifferentiableOn ℂ Φ {1}ᶜ) (hm : Measurable Φ)
    (hb : ∀ z, ‖z‖ ≤ 1 → ‖Φ z‖ ≤ M) : IsHardyDisc Φ := by
  have hM : 0 ≤ M := (norm_nonneg (Φ 0)).trans (hb 0 (by simp))
  refine ⟨hdiff, hm, ?_, ?_, ?_⟩
  · refine ⟨4 * M, by positivity, fun z hz hz1 => ?_⟩
    have hd : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1.symm)
    have h2 : ‖1 - z‖ ≤ 2 := by
      calc ‖1 - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
        _ ≤ 2 := by rw [norm_one]; linarith
    have h4 : ‖1 - z‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (1 - z)]
    refine (hb z hz).trans ((le_div_iff₀ (by positivity)).mpr ?_)
    nlinarith only [mul_le_mul_of_nonneg_right h4 hM]
  · refine ⟨M, fun x hx hx1 => hb x ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ x)]
    exact hx1.le
  · have hmeas : Measurable (fun θ : ℝ => ‖Φ (circleMap 0 1 θ)‖ ^ 2) :=
      (hm.comp (continuous_circleMap 0 1).measurable).norm.pow_const 2
    refine (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M ^ 2) volume 0
      (2 * Real.pi)).mono_fun hmeas.aestronglyMeasurable (Eventually.of_forall fun θ => ?_)
    have hn := hb _ (norm_circleMap_zero_one θ).le
    change ‖‖Φ (circleMap 0 1 θ)‖ ^ 2‖ ≤ ‖M ^ 2‖
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hn 2

theorem isHardyDisc_dirichletDisc {t : ℝ} (ht : 0 ≤ t) : IsHardyDisc (dirichletDisc t) :=
  isHardyDisc_of_bounded
    (fun _ hz => (differentiableAt_dirichletDisc t hz).differentiableWithinAt)
    (measurable_dirichletDisc t) (fun _ hz => norm_dirichletDisc_le_one ht hz)

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
      Real.circleAverage (fun z => ‖ArithmeticInnerFunctionTheory.peel Φ n z‖ ^ 2) 0 1 := by
    apply Real.circleAverage_congr_sphere
    intro z hz
    have hn : ‖z‖ = 1 := by simpa using hz
    have hz0 : z ≠ 0 := by intro he; simp [he] at hn
    have hd := peel_decomposition Φ n hz0
    have hd' : Φ z - ∑ k ∈ Finset.range n, z ^ k * taylorCoeff Φ k =
        z ^ n * ArithmeticInnerFunctionTheory.peel Φ n z := by
      linear_combination hd
    dsimp only
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
  change Real.circleAverage (fun z : ℂ => conj (z ^ (n + 1))) 0 1 =
    conj (Real.circleAverage (fun z : ℂ => z ^ (n + 1)) 0 1) at hc
  simpa only [hm, map_zero] using hc

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
          conj (z ^ n) * _root_.dslope Φ 0 z) 0 1 := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      have hn : ‖z‖ = 1 := by simpa using hz
      have hz0 : z ≠ 0 := by intro he; simp [he] at hn
      have hcz : conj z * z = 1 := by rw [Complex.conj_mul', hn]; norm_num
      have hd : _root_.dslope Φ 0 z * z = Φ z - Φ 0 := by
        rw [dslope_of_ne _ hz0, slope_def_module, sub_zero, smul_eq_mul]
        field_simp
      dsimp only
      rw [pow_succ, map_mul]
      linear_combination -(conj (z ^ n) * conj z) * hd +
        (conj (z ^ n) * _root_.dslope Φ 0 z) * hcz
    have hconst : CircleIntegrable (fun z : ℂ => Φ 0 * conj (z ^ (n + 1))) 0 1 :=
      (by fun_prop : Continuous (fun z : ℂ => Φ 0 * conj (z ^ (n + 1)))).continuousOn.circleIntegrable
        (by norm_num)
    rw [hb, Real.circleAverage_fun_add hconst (h.dslope.circleIntegrable_conj_pow_mul n)]
    have hc : Real.circleAverage (fun z : ℂ => Φ 0 * conj (z ^ (n + 1))) 0 1 = 0 := by
      change Real.circleAverage (fun z : ℂ => Φ 0 • conj (z ^ (n + 1))) 0 1 = 0
      rw [Real.circleAverage_fun_smul, circleAverage_conj_pow_succ, smul_zero]
    rw [hc, zero_add, ih h.dslope]
    unfold taylorCoeff ArithmeticInnerFunctionTheory.peel
    rw [Function.iterate_succ_apply]

/-- Complex change of variables from the unit circle to the Poisson line. -/
theorem circleAverage_complex_eq_poisson {F : ℝ → ℂ} {g : ℂ → ℂ}
    (hg : CircleIntegrable g 0 1)
    (hline : ∀ τ : ℝ, g (circleMap 0 1 (criticalLineAngle τ)) = F τ) :
    Integrable (fun τ : ℝ => F τ * (halfPlanePoissonKernel 1 τ : ℂ)) ∧
      Real.circleAverage g 0 1 =
        ∫ τ : ℝ, F τ * (halfPlanePoissonKernel 1 τ : ℂ) := by
  have hr := circleAverage_shift_eq_poisson (s0 := 1) (by norm_num)
    (fun τ => (F τ).re) (fun z => (g z).re) (fun τ => by
      convert congrArg Complex.re (hline τ) using 1
      norm_num)
  have hi := circleAverage_shift_eq_poisson (s0 := 1) (by norm_num)
    (fun τ => (F τ).im) (fun z => (g z).im) (fun τ => by
      convert congrArg Complex.im (hline τ) using 1
      norm_num)
  have hgr : CircleIntegrable (fun z => (g z).re) 0 1 :=
    ⟨Complex.reCLM.integrable_comp hg.1, Complex.reCLM.integrable_comp hg.2⟩
  have hgi : CircleIntegrable (fun z => (g z).im) 0 1 :=
    ⟨Complex.imCLM.integrable_comp hg.1, Complex.imCLM.integrable_comp hg.2⟩
  have hint : Integrable (fun τ : ℝ => F τ * (halfPlanePoissonKernel 1 τ : ℂ)) := by
    refine (((hr.1.mp hgr).ofReal).add (((hi.1.mp hgi).ofReal).mul_const I)).congr ?_
    exact Eventually.of_forall fun τ => by
      apply Complex.ext <;> simp
  refine ⟨hint, ?_⟩
  apply Complex.ext
  · have hc := Complex.reCLM.circleAverage_comp_comm hg
    change RCLike.re (Real.circleAverage g 0 1) = RCLike.re (∫ τ : ℝ, F τ * (halfPlanePoissonKernel 1 τ : ℂ))
    rw [← integral_re hint]
    simp only [RCLike.re_eq_complex_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    rw [← hr.2]
    exact hc.symm
  · have hc := Complex.imCLM.circleAverage_comp_comm hg
    change RCLike.im (Real.circleAverage g 0 1) = RCLike.im (∫ τ : ℝ, F τ * (halfPlanePoissonKernel 1 τ : ℂ))
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
  rw [dirichletLineMode, dirichletLineMode, Complex.ofReal_exp, ← Complex.exp_add]
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
      fun τ : ℝ => (Real.exp (-δ * t) : ℂ) *
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

theorem differentiableOn_translatedDiscCoord {δ : ℝ} (hδ : 0 ≤ δ) :
    DifferentiableOn ℂ (translatedDiscCoord δ) (closedBall 0 1) := by
  intro z hz
  have hn : ‖z‖ ≤ 1 := by simpa using hz
  have hnum : DifferentiableAt ℂ (fun u : ℂ => (δ : ℂ) + (1 - (δ : ℂ)) * u) z := by fun_prop
  have hden : DifferentiableAt ℂ (fun u : ℂ => 1 + (δ : ℂ) - (δ : ℂ) * u) z := by fun_prop
  exact (hnum.div hden (translatedDiscCoord_den_ne_zero hδ hn)).differentiableWithinAt

theorem translatedDiscCoord_circleMap (δ τ : ℝ) :
    translatedDiscCoord δ (circleMap 0 1 (criticalLineAngle τ)) =
      blaschkeCoord 1 (1 / 2 + (δ : ℂ) + (τ : ℂ) * I) := by
  have h := blaschkeCoord_one_translate (δ := δ) (circleMap_criticalLineAngle_ne_one τ)
  rw [discChart_circleMap] at h
  norm_num at h
  rw [show (1 / 2 : ℂ) + (τ : ℂ) * I + (δ : ℂ) =
    1 / 2 + (δ : ℂ) + (τ : ℂ) * I by ring] at h
  exact h.symm

/-- Conformal polynomial exponentials are outer even on translated lines. Their Poisson
logarithmic mean is exactly the value at the translated centre. -/
theorem integral_log_polyMollifier_shifted (Q : Polynomial ℂ) {δ : ℝ} (hδ : 0 ≤ δ) :
    Integrable (fun τ : ℝ =>
      Real.log ‖polyMollifier 1 Q (1 / 2 + (δ : ℂ) + (τ : ℂ) * I)‖ *
        halfPlanePoissonKernel 1 τ) ∧
      (∫ τ : ℝ, Real.log ‖polyMollifier 1 Q (1 / 2 + (δ : ℂ) + (τ : ℂ) * I)‖ *
        halfPlanePoissonKernel 1 τ) = (Q.eval ((δ : ℂ) / (1 + (δ : ℂ)))).re := by
  let g : ℂ → ℂ := fun z => Q.eval (translatedDiscCoord δ z)
  have hd : DifferentiableOn ℂ g (closedBall 0 1) :=
    Q.differentiable.comp_differentiableOn (differentiableOn_translatedDiscCoord hδ)
  have hdc : DiffContOnCl ℂ g (ball 0 |(1 : ℝ)|) := by
    rw [abs_one]
    refine ⟨hd.mono ball_subset_closedBall, ?_⟩
    rw [closure_ball 0 one_ne_zero]
    exact hd.continuousOn
  have hg : CircleIntegrable g 0 1 :=
    (hd.continuousOn.mono sphere_subset_closedBall).circleIntegrable zero_le_one
  have hgr : CircleIntegrable (fun z => (g z).re) 0 1 :=
    ⟨Complex.reCLM.integrable_comp hg.1, Complex.reCLM.integrable_comp hg.2⟩
  have hc := circleAverage_shift_eq_poisson (s0 := 1) (by norm_num)
    (fun τ => Real.log ‖polyMollifier 1 Q (1 / 2 + (δ : ℂ) + (τ : ℂ) * I)‖)
    (fun z => (g z).re) (fun τ => by
      simp only [g, translatedDiscCoord_circleMap, polyMollifier, Complex.norm_exp,
        Real.log_exp]
      norm_num)
  refine ⟨hc.1.mp hgr, ?_⟩
  rw [← hc.2]
  have hm := Complex.reCLM.circleAverage_comp_comm hg
  rw [hdc.circleAverage] at hm
  simpa only [Function.comp_def, Complex.reCLM_apply, g, translatedDiscCoord_at_zero] using hm

/-- The fixed chart used by both Szegő budgets has zero logarithmic cost when `Q(0)=0`. -/
theorem integral_log_polyMollifier_one {Q : Polynomial ℂ} (hQ : Q.coeff 0 = 0) :
    (∫ τ : ℝ, Real.log ‖polyMollifier 1 Q (1 / 2 + (τ : ℂ) * I)‖ *
      halfPlanePoissonKernel 1 τ) = 0 := by
  simpa [← Polynomial.coeff_zero_eq_eval_zero, hQ] using
    (integral_log_polyMollifier_shifted Q (δ := 0) le_rfl).2

/-- Finite polynomial recurrence for the Laguerre jets of `exp(-t/(1-z))`.
The variable is the reciprocal coordinate `w=(1-z)⁻¹`. -/
def laguerreJetPoly (t : ℝ) : ℕ → Polynomial ℂ
  | 0 => 1
  | n + 1 => Polynomial.X ^ 2 *
      ((laguerreJetPoly t n).derivative - Polynomial.C (t : ℂ) * laguerreJetPoly t n)

private theorem hasDerivAt_reciprocalCoord {z : ℂ} (hz : z ≠ 1) :
    HasDerivAt (fun u : ℂ => (1 - u)⁻¹) ((1 - z)⁻¹ ^ 2) z := by
  have h : HasDerivAt (fun u : ℂ => (1 - u)⁻¹) (-(-(1 : ℂ)) / (1 - z) ^ 2) z :=
    ((hasDerivAt_id z).const_sub 1).inv (sub_ne_zero.mpr hz.symm)
  apply h.congr_deriv
  simp only [neg_neg, one_div, inv_pow]

theorem hasDerivAt_dirichletDisc (t : ℝ) {z : ℂ} (hz : z ≠ 1) :
    HasDerivAt (dirichletDisc t) (dirichletDisc t z * (-(t : ℂ) * (1 - z)⁻¹ ^ 2)) z := by
  exact (Complex.hasDerivAt_exp _).comp z ((hasDerivAt_reciprocalCoord hz).const_mul _)

private theorem hasDerivAt_dirichletDisc_jet (t : ℝ) (n : ℕ) {z : ℂ} (hz : z ≠ 1) :
    HasDerivAt (fun u : ℂ => dirichletDisc t u * (laguerreJetPoly t n).eval (1 - u)⁻¹)
      (dirichletDisc t z * (laguerreJetPoly t (n + 1)).eval (1 - z)⁻¹) z := by
  have h := (hasDerivAt_dirichletDisc t hz).mul
    (((laguerreJetPoly t n).hasDerivAt _).comp z (hasDerivAt_reciprocalCoord hz))
  apply h.congr_deriv
  simp only [Function.comp_apply, laguerreJetPoly, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_C]
  ring

/-- Every derivative is an exponential times a finite polynomial in the reciprocal coordinate. -/
theorem iteratedDeriv_dirichletDisc (t : ℝ) (n : ℕ) {z : ℂ} (hz : z ≠ 1) :
    iteratedDeriv n (dirichletDisc t) z =
      dirichletDisc t z * (laguerreJetPoly t n).eval (1 - z)⁻¹ := by
  induction n generalizing z with
  | zero => simp [laguerreJetPoly]
  | succ n ih =>
    have he : iteratedDeriv n (dirichletDisc t) =ᶠ[𝓝 z]
        (fun u : ℂ => dirichletDisc t u * (laguerreJetPoly t n).eval (1 - u)⁻¹) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hz] with u hu
      exact ih hu
    rw [iteratedDeriv_succ, he.deriv_eq]
    exact (hasDerivAt_dirichletDisc_jet t n hz).deriv

/-- Exact finite formula for every conformal–Dirichlet coefficient. -/
theorem taylorCoeff_dirichletDisc (t : ℝ) (n : ℕ) :
    taylorCoeff (dirichletDisc t) n =
      Complex.exp (-(t : ℂ)) * (laguerreJetPoly t n).eval 1 / (n.factorial : ℂ) := by
  have hd : DifferentiableOn ℂ (dirichletDisc t) ({1}ᶜ : Set ℂ) :=
    fun z hz => (differentiableAt_dirichletDisc t hz).differentiableWithinAt
  have ha : AnalyticAt ℂ (dirichletDisc t) 0 :=
    hd.analyticAt (isOpen_compl_singleton.mem_nhds (by simp))
  rw [taylorCoeff, peel, _root_.HTGeometry.iterate_dslope_self_eq_iteratedDeriv_div_factorial ha,
    iteratedDeriv_dirichletDisc t n (by norm_num), dirichletDisc_zero]
  simp

/-- Explicit cross Gram matrix, with all entries given by finite Laguerre jet polynomials. -/
theorem integral_conformal_dirichlet_mode_eq_laguerre {t : ℝ} (ht : 0 ≤ t) (δ : ℝ) (k : ℕ) :
    (∫ τ : ℝ, conj (blaschkeCoord 1 (1 / 2 + (τ : ℂ) * I) ^ k) *
        dirichletLineMode t δ τ * (halfPlanePoissonKernel 1 τ : ℂ)) =
      (Real.exp (-δ * t) : ℂ) *
        (Complex.exp (-(t : ℂ)) * (laguerreJetPoly t k).eval 1 / (k.factorial : ℂ)) := by
  rw [integral_conformal_dirichlet_mode ht, taylorCoeff_dirichletDisc]

/-- Analyticity on a larger disc gives an absolutely summable Taylor expansion on the
closed unit disc, with the same coefficients as the removable-slope definition. -/
theorem summable_taylor_of_larger_disc {g : ℂ → ℂ} {R : ℝ≥0} (hR : 1 < (R : ℝ))
    (hd : DifferentiableOn ℂ g (closedBall 0 R)) :
    Summable (fun k => ‖taylorCoeff g k‖) ∧
      ∀ z : ℂ, ‖z‖ ≤ 1 → HasSum (fun k => z ^ k * taylorCoeff g k) (g z) := by
  have hp := hd.hasFPowerSeriesOnBall (show 0 < R by exact_mod_cast (lt_trans one_pos hR))
  let p := cauchyPowerSeries g 0 R
  have hcoeff (k : ℕ) : taylorCoeff g k = p.coeff k := by
    have h1 := hp.hasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope k
    have h2 := h1.coeff_zero (1 : Fin 0 → ℂ)
    have h3 := p.coeff_iterate_fslope k 0
    rw [zero_add] at h3
    exact h2.symm.trans h3
  have hmem : (1 : ℂ) ∈ Metric.eball 0 p.radius := by
    have hlt : (1 : ENNReal) < (R : ENNReal) := by exact_mod_cast hR
    simpa using hlt.trans_le hp.r_le
  refine ⟨?_, fun z hz => ?_⟩
  · simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, one_pow, one_smul,
      hcoeff] using p.summable_norm_apply hmem
  · have hzR : z ∈ Metric.eball (0 : ℂ) R := by
      rw [Metric.eball_coe, Metric.mem_ball, dist_zero_right]
      exact hz.trans_lt hR
    have hs := hp.hasSum hzR
    rw [zero_add] at hs
    simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul, hcoeff] using hs

/-- Pairing an absolutely convergent conformal series with Hardy data reads its coefficient
pairing. Integrability follows from the same absolute majorant. -/
theorem hasSum_circleAverage_conj_series_mul {Φ g : ℂ → ℂ} (h : CircleIntegrable Φ 0 1)
    {a : ℕ → ℂ} (ha : Summable (fun k => ‖a k‖))
    (hg : ∀ z : ℂ, ‖z‖ = 1 → HasSum (fun k => z ^ k * a k) (g z)) :
    HasSum (fun k => conj (a k) * Real.circleAverage (fun z => conj (z ^ k) * Φ z) 0 1)
      (Real.circleAverage (fun z => conj (g z) * Φ z) 0 1) := by
  let μ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  let F : ℕ → ℝ → ℂ := fun k θ =>
    conj (a k) * (conj (circleMap 0 1 θ ^ k) * Φ (circleMap 0 1 θ))
  have hki (k : ℕ) : CircleIntegrable (fun z => conj (z ^ k) * Φ z) 0 1 :=
    h.mul_of_continuousOn (by fun_prop)
  have hint (k : ℕ) : Integrable (F k) μ :=
    ((hki k).const_smul (a := conj (a k))).1
  have hnorm (k : ℕ) : (∫ θ, ‖F k θ‖ ∂μ) =
      ‖a k‖ * ∫ θ, ‖Φ (circleMap 0 1 θ)‖ ∂μ := by
    simp only [F, norm_mul, Complex.norm_conj, norm_pow, norm_circleMap_zero_one,
      one_pow, one_mul]
    rw [integral_const_mul]
  have hsum : Summable (fun k => ∫ θ, ‖F k θ‖ ∂μ) := by
    simpa only [hnorm] using ha.mul_right (∫ θ, ‖Φ (circleMap 0 1 θ)‖ ∂μ)
  have hs := hasSum_integral_of_summable_integral_norm hint hsum
  have hpoint (θ : ℝ) : (∑' k, F k θ) = conj (g (circleMap 0 1 θ)) * Φ (circleMap 0 1 θ) := by
    have ht := ((RCLike.hasSum_conj' ℂ).mpr (hg _ (norm_circleMap_zero_one θ))).mul_right
      (Φ (circleMap 0 1 θ))
    have he : (fun k => conj (circleMap 0 1 θ ^ k * a k) * Φ (circleMap 0 1 θ)) =
        fun k => F k θ := by
      funext k
      simp only [F, map_mul]
      ring
    rw [he] at ht
    exact ht.tsum_eq
  simp_rw [hpoint] at hs
  have hterm (k : ℕ) : (2 * Real.pi)⁻¹ • (∫ θ, F k θ ∂μ) =
      conj (a k) * Real.circleAverage (fun z => conj (z ^ k) * Φ z) 0 1 := by
    rw [show (∫ θ, F k θ ∂μ) = ∫ θ in 0..2 * Real.pi, F k θ from
      (intervalIntegral.integral_of_le Real.two_pi_pos.le).symm]
    change Real.circleAverage (fun z => conj (a k) • (conj (z ^ k) * Φ z)) 0 1 = _
    rw [Real.circleAverage_fun_smul, smul_eq_mul]
  have hm := hs.const_smul ((2 * Real.pi)⁻¹ : ℝ)
  simp_rw [hterm] at hm
  simpa only [Real.circleAverage_def, intervalIntegral.integral_of_le Real.two_pi_pos.le] using hm

theorem IsHardyDisc.hasSum_conj_taylor_mul {Φ g : ℂ → ℂ} (h : IsHardyDisc Φ)
    {a : ℕ → ℂ} (ha : Summable (fun k => ‖a k‖))
    (hg : ∀ z : ℂ, ‖z‖ = 1 → HasSum (fun k => z ^ k * a k) (g z)) :
    HasSum (fun k => conj (a k) * taylorCoeff Φ k)
      (Real.circleAverage (fun z => conj (g z) * Φ z) 0 1) := by
  simpa only [h.circleAverage_conj_pow_mul] using
    hasSum_circleAverage_conj_series_mul h.circleIntegrable ha hg

/-- For functions holomorphic on the closed disc, the Cauchy coefficient gives the same
mixed moment without requiring a holomorphic continuation outside that disc. -/
theorem circleAverage_conj_pow_mul_of_differentiableOn {g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ g (closedBall 0 1)) (k : ℕ) :
    Real.circleAverage (fun z => conj (z ^ k) * g z) 0 1 = taylorCoeff g k := by
  have hp := hd.hasFPowerSeriesOnBall (R := (1 : ℝ≥0)) (by norm_num)
  have hcoeff : taylorCoeff g k = (cauchyPowerSeries g 0 1).coeff k := by
    have h1 := hp.hasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope k
    have h2 := h1.coeff_zero (1 : Fin 0 → ℂ)
    have h3 := (cauchyPowerSeries g 0 1).coeff_iterate_fslope k 0
    rw [zero_add] at h3
    exact h2.symm.trans h3
  calc Real.circleAverage (fun z => conj (z ^ k) * g z) 0 1 =
      Real.circleAverage (fun z => z⁻¹ ^ k * g z) 0 1 := by
        apply Real.circleAverage_congr_sphere
        intro z hz
        have hn : ‖z‖ = 1 := by simpa using hz
        have hz0 : z ≠ 0 := by intro he; simp [he] at hn
        have hcz : conj z * z = 1 := by rw [Complex.conj_mul', hn]; norm_num
        have hi : z⁻¹ = conj z := by
          calc z⁻¹ = (conj z * z) * z⁻¹ := by rw [hcz, one_mul]
            _ = conj z := by rw [mul_assoc, mul_inv_cancel₀ hz0, mul_one]
        dsimp only
        rw [hi, map_pow]
    _ = GaloisForLFunctions.HTGeometry.cauchyCoeff g 1 k :=
      (GaloisForLFunctions.HTGeometry.cauchyCoeff_eq_circleAverage g one_pos k).symm
    _ = taylorCoeff g k := hcoeff.symm

#print axioms integral_conformal_dirichlet_mode_eq_laguerre
#print axioms dirichletDisc_projection_remainder
#print axioms integral_log_polyMollifier_shifted
#print axioms summable_taylor_of_larger_disc
#print axioms hasSum_circleAverage_conj_series_mul

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
