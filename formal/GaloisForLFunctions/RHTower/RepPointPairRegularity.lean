import GaloisForLFunctions.RHTower.RepPointPairSymmetry
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Regularity and equivariance of the twisted point-pair operators

`L_φ F` is equivariant, `(L_φ F)(Az) = ρ(A)(L_φ F)(z)` (`ppApply_smul_point`), and for a `C¹` kernel `φ`
with bounded derivative it is `C¹` in the complex chart (`isChartC1_ppApply`): near `ζ₀` it is the finite
sum `½ Σ_{B ∈ S} ∫_𝒟 φ(U(ζ, Bz')) ρ(B) F(z')` over the near translates (`chartFun_ppApply_local`), each
term differentiated under the integral sign (`hasFDerivAt_ppTermc`) with the chart derivative
`φ'(U) dU` of `U(ζ,w) = |ζ-w|²/(4 Im ζ Im w)` (`hasFDerivAt_pairUc`).  On the support `U ≤ R` the
hyperbolic gradient of `U` is bounded, `Im ζ |∂ₓU| ≤ 2R+1`, `Im ζ |∂ᵧU| ≤ 3R+2` (`pairUcDeriv_bounds`),
which dominates the derivative uniformly near `ζ₀`.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology
open scoped MatrixGroups ENNReal InnerProductSpace

namespace GaloisForLFunctions.RHTower.RepPointPair

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type} [Fintype ι] {ρ : SL(2, ℤ) →* (EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)}

/-- The chart representative of a field on the upper half-plane. -/
def chartFun {E : Type*} (F : ℍ → E) : ℂ → E := F ∘ ofComplex

/-- `C¹` regularity of a field in the complex chart. -/
def IsChartC1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℍ → E) : Prop :=
  ContDiffOn ℝ 1 (chartFun F) {z : ℂ | 0 < z.im}

theorem rho_mul (A B : SL(2, ℤ)) (v : EuclideanSpace ℂ ι) : ρ (A * B) v = ρ A (ρ B v) := by
  rw [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply]

theorem ppTerm_smul_point (φ : ℝ → ℝ) (F : ℍ → EuclideanSpace ℂ ι) (A B : SL(2, ℤ)) (z : ℍ) :
    ppTerm ρ φ F (A • z) (A * B) = ρ A (ppTerm ρ φ F z B) := by
  unfold ppTerm
  have h := (ρ A).toContinuousLinearEquiv.integral_comp_comm (μ := volume.restrict fd)
    (fun z' => ((φ (pairU z (B • z')) : ℝ) : ℂ) • ρ B (F z'))
  simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun z' => ?_)
  simp only
  rw [mul_smul, pairU_smul_int, rho_mul, map_smul]

/-- **Equivariance.** `(L_φ F)(Az) = ρ(A) (L_φ F)(z)`. -/
theorem ppApply_smul_point {φ : ℝ → ℝ} {R : ℝ} (hφR : KernelSupport φ R) (F : ℍ → EuclideanSpace ℂ ι)
    (A : SL(2, ℤ)) (z : ℍ) : ppApply ρ φ F (A • z) = ρ A (ppApply ρ φ F z) := by
  unfold ppApply
  rw [map_smul]
  congr 1
  rw [← (Equiv.mulLeft A).tsum_eq]
  simp only [Equiv.coe_mulLeft, ppTerm_smul_point]
  have hs : Summable (fun B => ppTerm ρ φ F z B) :=
    summable_of_ne_finset_zero (s := ppNearSet z R) fun B hB =>
      ppTerm_eq_zero hφR F z (by simpa [ppNearSet] using hB)
  exact ((ρ A).toContinuousLinearEquiv.toContinuousLinearMap.map_tsum hs).symm


/-- The point-pair invariant in the complex chart: `U(ζ, w) = ((Re ζ - Re w)² + (Im ζ - Im w)²)/(4 Im ζ Im w)`. -/
def pairUc (ζ : ℂ) (w : ℍ) : ℝ := ((ζ.re - w.re) ^ 2 + (ζ.im - w.im) ^ 2) / (4 * ζ.im * w.im)

theorem pairUc_ofComplex {ζ : ℂ} (hζ : 0 < ζ.im) (w : ℍ) :
    pairUc ζ w = pairU (UpperHalfPlane.ofComplex ζ) w := by
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hζ]
  show _ = dist ((⟨ζ, hζ⟩ : ℍ) : ℂ) (w : ℂ) ^ 2 / (4 * ζ.im * w.im)
  rw [Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply, pairUc]
  have e1 : ((⟨ζ, hζ⟩ : ℍ) : ℂ) = ζ := rfl
  rw [e1]
  simp only [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

/-- The chart derivative of `U(·, w)`. -/
def pairUcDeriv (ζ : ℂ) (w : ℍ) : ℂ →L[ℝ] ℝ :=
  ((ζ.re - w.re) / (2 * ζ.im * w.im)) • Complex.reCLM +
    ((ζ.im ^ 2 - w.im ^ 2 - (ζ.re - w.re) ^ 2) / (4 * ζ.im ^ 2 * w.im)) • Complex.imCLM

theorem hasFDerivAt_pairUc {ζ : ℂ} (hζ : 0 < ζ.im) (w : ℍ) :
    HasFDerivAt (fun ζ => pairUc ζ w) (pairUcDeriv ζ w) ζ := by
  have hw := w.im_pos
  have hre : HasFDerivAt (fun ζ : ℂ => ζ.re - w.re) Complex.reCLM ζ :=
    (Complex.reCLM.hasFDerivAt).sub_const _
  have him : HasFDerivAt (fun ζ : ℂ => ζ.im - w.im) Complex.imCLM ζ :=
    (Complex.imCLM.hasFDerivAt).sub_const _
  have hnum : HasFDerivAt (fun ζ : ℂ => (ζ.re - w.re) * (ζ.re - w.re) +
      (ζ.im - w.im) * (ζ.im - w.im))
      (((ζ.re - w.re) • Complex.reCLM + (ζ.re - w.re) • Complex.reCLM) +
        ((ζ.im - w.im) • Complex.imCLM + (ζ.im - w.im) • Complex.imCLM)) ζ :=
    (hre.mul hre).add (him.mul him)
  have hinv : HasFDerivAt (fun ζ : ℂ => (ζ.im)⁻¹) ((-(ζ.im ^ 2)⁻¹) • Complex.imCLM) ζ :=
    (hasDerivAt_inv hζ.ne').comp_hasFDerivAt ζ Complex.imCLM.hasFDerivAt
  have h := (hnum.mul_const ((4 * w.im)⁻¹)).mul hinv
  have e : (fun ζ => pairUc ζ w) = fun ζ : ℂ => ((ζ.re - w.re) * (ζ.re - w.re) +
      (ζ.im - w.im) * (ζ.im - w.im)) * (4 * w.im)⁻¹ * (ζ.im)⁻¹ := by
    funext ζ; unfold pairUc; rw [div_eq_mul_inv, mul_inv, mul_inv]; ring
  rw [e]
  refine h.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp [pairUcDeriv]
  field_simp
  ring

theorem deriv_eq_zero_of_kernelSupport {φ : ℝ → ℝ} {R : ℝ} (hφR : KernelSupport φ R) {u : ℝ}
    (hu : R < u) : deriv φ u = 0 := by
  have h : φ =ᶠ[𝓝 u] fun _ => 0 := by
    filter_upwards [Ioi_mem_nhds hu] with v hv using hφR v hv
  rw [h.deriv_eq, deriv_const]

/-- On the support, `|Re(ζ - w)| ≤ √(4R Im ζ Im w)` and `Im w ≍ Im ζ`. -/
theorem pairUc_le_bounds {ζ : ℂ} (hζ : 0 < ζ.im) {w : ℍ} {R : ℝ} (h : pairUc ζ w ≤ R) :
    ζ.im / (4 * R + 2) ≤ w.im ∧ w.im ≤ (4 * R + 2) * ζ.im ∧
      (ζ.re - w.re) ^ 2 ≤ 4 * R * ζ.im * w.im := by
  rw [pairUc_ofComplex hζ] at h
  obtain ⟨h1, h2, -⟩ := pairU_le_bounds h
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hζ] at h1 h2
  refine ⟨h1, h2, ?_⟩
  have hw := w.im_pos
  have h' : pairUc ζ w ≤ R := by rwa [pairUc_ofComplex hζ]
  unfold pairUc at h'
  rw [div_le_iff₀ (by positivity)] at h'
  nlinarith [sq_nonneg (ζ.im - w.im)]

theorem abs_mul_derivX_le {x y v R : ℝ} (hy : 0 < y) (hv : 0 < v) (hR : 0 ≤ R)
    (hx : x ^ 2 ≤ 4 * R * y * v) (hyv : y ≤ (4 * R + 2) * v) :
    |y * (x / (2 * y * v))| ≤ 2 * R + 1 := by
  rw [show y * (x / (2 * y * v)) = x / (2 * v) by field_simp, abs_div,
    abs_of_pos (by positivity : (0:ℝ) < 2 * v), div_le_iff₀ (by positivity)]
  have h4 : x ^ 2 ≤ ((2 * R + 1) * (2 * v)) ^ 2 := by nlinarith
  have := abs_le_of_sq_le_sq' h4 (by positivity)
  exact abs_le.2 ⟨this.1, this.2⟩

theorem abs_mul_derivY_le {x y v R : ℝ} (hy : 0 < y) (hv : 0 < v)
    (hx : x ^ 2 ≤ 4 * R * y * v) (hyv : y ≤ (4 * R + 2) * v) (hvy : v ≤ (4 * R + 2) * y) :
    |y * ((y ^ 2 - v ^ 2 - x ^ 2) / (4 * y ^ 2 * v))| ≤ 3 * R + 2 := by
  rw [show y * ((y ^ 2 - v ^ 2 - x ^ 2) / (4 * y ^ 2 * v)) = (y ^ 2 - v ^ 2 - x ^ 2) / (4 * y * v) by
    field_simp]
  rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 4 * y * v), div_le_iff₀ (by positivity), abs_le]
  constructor <;> nlinarith [sq_nonneg x, mul_pos hy hv]

/-- **The hyperbolic gradient of `U` is bounded on the support**: `Im ζ |∂ₓU| ≤ 2R+1`,
`Im ζ |∂ᵧU| ≤ 3R+2`. -/
theorem pairUcDeriv_bounds {ζ : ℂ} (hζ : 0 < ζ.im) {w : ℍ} {R : ℝ} (h : pairUc ζ w ≤ R) :
    |ζ.im * pairUcDeriv ζ w 1| ≤ 2 * R + 1 ∧ |ζ.im * pairUcDeriv ζ w Complex.I| ≤ 3 * R + 2 := by
  have hR : 0 ≤ R := by
    have : 0 ≤ pairUc ζ w := by unfold pairUc; have := w.im_pos; positivity
    linarith
  obtain ⟨h1, h2, h3⟩ := pairUc_le_bounds hζ h
  have hw := w.im_pos
  have hyv : ζ.im ≤ (4 * R + 2) * w.im := by rw [div_le_iff₀ (by linarith)] at h1; linarith
  have e1 : pairUcDeriv ζ w 1 = (ζ.re - w.re) / (2 * ζ.im * w.im) := by simp [pairUcDeriv]
  have e2 : pairUcDeriv ζ w Complex.I =
      (ζ.im ^ 2 - w.im ^ 2 - (ζ.re - w.re) ^ 2) / (4 * ζ.im ^ 2 * w.im) := by simp [pairUcDeriv]
  rw [e1, e2]
  exact ⟨abs_mul_derivX_le hζ hw hR h3 hyv, abs_mul_derivY_le hζ hw h3 hyv h2⟩

theorem norm_pairUcDeriv_le {ζ : ℂ} (hζ : 0 < ζ.im) {w : ℍ} {R : ℝ} (h : pairUc ζ w ≤ R) :
    ‖pairUcDeriv ζ w‖ ≤ (5 * R + 3) / ζ.im := by
  have hR : 0 ≤ R := by
    have : 0 ≤ pairUc ζ w := by unfold pairUc; have := w.im_pos; positivity
    linarith
  obtain ⟨h1, h2⟩ := pairUcDeriv_bounds hζ h
  have ha : |pairUcDeriv ζ w 1| ≤ (2 * R + 1) / ζ.im := by
    rw [le_div_iff₀ hζ]
    calc |pairUcDeriv ζ w 1| * ζ.im = |ζ.im * pairUcDeriv ζ w 1| := by
          rw [abs_mul, abs_of_pos hζ, mul_comm]
      _ ≤ 2 * R + 1 := h1
  have hb : |pairUcDeriv ζ w Complex.I| ≤ (3 * R + 2) / ζ.im := by
    rw [le_div_iff₀ hζ]
    calc |pairUcDeriv ζ w Complex.I| * ζ.im = |ζ.im * pairUcDeriv ζ w Complex.I| := by
          rw [abs_mul, abs_of_pos hζ, mul_comm]
      _ ≤ 3 * R + 2 := h2
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by apply Complex.ext <;> simp
  have hlin : pairUcDeriv ζ w v = v.re * pairUcDeriv ζ w 1 + v.im * pairUcDeriv ζ w Complex.I := by
    conv_lhs => rw [hv]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [hlin, Real.norm_eq_abs]
  have hre : |v.re| ≤ ‖v‖ := Complex.abs_re_le_norm v
  have him : |v.im| ≤ ‖v‖ := Complex.abs_im_le_norm v
  calc |v.re * pairUcDeriv ζ w 1 + v.im * pairUcDeriv ζ w Complex.I|
      ≤ |v.re| * |pairUcDeriv ζ w 1| + |v.im| * |pairUcDeriv ζ w Complex.I| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ ‖v‖ * ((2 * R + 1) / ζ.im) + ‖v‖ * ((3 * R + 2) / ζ.im) := by
        gcongr
    _ = (5 * R + 3) / ζ.im * ‖v‖ := by ring


variable (ρ) in
/-- One translate of the point-pair operator in the complex chart. -/
def ppTermc (φ : ℝ → ℝ) (F : ℍ → EuclideanSpace ℂ ι) (B : SL(2, ℤ)) (ζ : ℂ) : EuclideanSpace ℂ ι :=
  ∫ z' in fd, φ (pairUc ζ (B • z')) • ρ B (F z')

variable (ρ) in
/-- Its chart derivative. -/
def ppTermcDeriv (φ : ℝ → ℝ) (F : ℍ → EuclideanSpace ℂ ι) (B : SL(2, ℤ)) (ζ : ℂ) : ℂ →L[ℝ] EuclideanSpace ℂ ι :=
  ∫ z' in fd, (deriv φ (pairUc ζ (B • z')) • pairUcDeriv ζ (B • z')).smulRight (ρ B (F z'))

theorem continuous_pairUc_right {ζ : ℂ} (hζ : 0 < ζ.im) : Continuous (fun w : ℍ => pairUc ζ w) := by
  unfold pairUc
  have hre : Continuous (fun w : ℍ => w.re) := UpperHalfPlane.continuous_re
  have him : Continuous (fun w : ℍ => w.im) := UpperHalfPlane.continuous_im
  refine Continuous.div (by fun_prop) (continuous_const.mul him) fun w => ?_
  have := w.im_pos; positivity


section Diff

variable {φ : ℝ → ℝ} {M M' R : ℝ} (hφd : Differentiable ℝ φ) (hφ'c : Continuous (deriv φ))
  (hφM : ∀ u, |φ u| ≤ M) (hφ'M : ∀ u, |deriv φ u| ≤ M') (hR : 0 ≤ R) (hφR : KernelSupport φ R)

include hφd hφ'c hφM hφ'M hR hφR in
/-- **Differentiation of one translate under the integral sign.** -/
theorem hasFDerivAt_ppTermc {F : ℍ → EuclideanSpace ℂ ι} (hF : MemLp F 2 cellMeasure) (B : SL(2, ℤ))
    {ζ₀ : ℂ} (hζ₀ : 0 < ζ₀.im) :
    HasFDerivAt (ppTermc ρ φ F B) (ppTermcDeriv ρ φ F B ζ₀) ζ₀ := by
  have hF1 : Integrable (fun z' => ρ B (F z')) cellMeasure :=
    (ρ B).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp
      (hF.integrable one_le_two)
  have hε : 0 < ζ₀.im / 2 := by linarith
  have hball : ∀ ζ ∈ Metric.ball ζ₀ (ζ₀.im / 2), ζ₀.im / 2 < ζ.im := by
    intro ζ hζ
    have h1 := (Complex.abs_im_le_norm (ζ - ζ₀))
    rw [Metric.mem_ball, dist_eq_norm] at hζ
    rw [Complex.sub_im] at h1
    have := abs_lt.1 (h1.trans_lt hζ)
    linarith
  have hM' : 0 ≤ M' := (abs_nonneg _).trans (hφ'M 0)
  unfold ppTermc ppTermcDeriv
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := volume.restrict fd)
    (F := fun ζ z' => φ (pairUc ζ (B • z')) • ρ B (F z'))
    (F' := fun ζ z' => (deriv φ (pairUc ζ (B • z')) • pairUcDeriv ζ (B • z')).smulRight
      (ρ B (F z'))) (bound := fun z' =>
    M' * ((5 * R + 3) / (ζ₀.im / 2)) * ‖ρ B (F z')‖)
    (Metric.ball_mem_nhds ζ₀ hε) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [Metric.ball_mem_nhds ζ₀ hε] with ζ hζ
    have hk : Continuous (fun z' : ℍ => φ (pairUc ζ (B • z'))) :=
      hφd.continuous.comp ((continuous_pairUc_right (by linarith [hball ζ hζ])).comp
        (continuous_smul_int B))
    exact hk.aestronglyMeasurable.smul hF1.1
  · refine hF1.bdd_smul (φ := fun z' => φ (pairUc ζ₀ (B • z'))) M ?_
      (Eventually.of_forall fun z' => ?_)
    · exact (hφd.continuous.comp ((continuous_pairUc_right hζ₀).comp
        (continuous_smul_int B))).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact hφM _
  · have hk : Continuous (fun z' : ℍ => deriv φ (pairUc ζ₀ (B • z')) • pairUcDeriv ζ₀ (B • z')) := by
      have hU := (continuous_pairUc_right hζ₀).comp (continuous_smul_int B)
      have hre : Continuous (fun w : ℍ => w.re) := UpperHalfPlane.continuous_re
      have him : Continuous (fun w : ℍ => w.im) := UpperHalfPlane.continuous_im
      have ha : Continuous (fun w : ℍ => (ζ₀.re - w.re) / (2 * ζ₀.im * w.im)) := by
        refine Continuous.div (by fun_prop) (by fun_prop) fun w => ?_
        have := w.im_pos; positivity
      have hb : Continuous (fun w : ℍ =>
          (ζ₀.im ^ 2 - w.im ^ 2 - (ζ₀.re - w.re) ^ 2) / (4 * ζ₀.im ^ 2 * w.im)) := by
        refine Continuous.div (by fun_prop) (by fun_prop) fun w => ?_
        have := w.im_pos; positivity
      have hD : Continuous (fun w : ℍ => pairUcDeriv ζ₀ w) :=
        (ha.smul continuous_const).add (hb.smul continuous_const)
      exact (hφ'c.comp hU).smul (hD.comp (continuous_smul_int B))
    exact (ContinuousLinearMap.smulRightL ℝ ℂ (EuclideanSpace ℂ ι)).continuous₂.comp_aestronglyMeasurable₂
      hk.aestronglyMeasurable hF1.1
  · refine Eventually.of_forall fun z' ζ hζ => ?_
    have hζ' := hball ζ hζ
    have hpos : 0 < ζ.im := by linarith
    rw [ContinuousLinearMap.norm_smulRight_apply]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [norm_smul, Real.norm_eq_abs]
    by_cases hU : pairUc ζ (B • z') ≤ R
    · refine mul_le_mul (hφ'M _) ?_ (norm_nonneg _) hM'
      refine (norm_pairUcDeriv_le hpos hU).trans ?_
      exact div_le_div_of_nonneg_left (by linarith) hε hζ'.le
    · rw [deriv_eq_zero_of_kernelSupport hφR (lt_of_not_ge hU), abs_zero, zero_mul]
      have : 0 ≤ (5 * R + 3) / (ζ₀.im / 2) := by positivity
      positivity
  · exact (hF1.norm.const_mul _)
  · refine Eventually.of_forall fun z' ζ hζ => ?_
    have hpos : 0 < ζ.im := by linarith [hball ζ hζ]
    exact ((hφd _).hasDerivAt.comp_hasFDerivAt ζ (hasFDerivAt_pairUc hpos (B • z'))).smul_const _


theorem continuous_pairUc_left (w : ℍ) :
    ContinuousOn (fun ζ : ℂ => pairUc ζ w) {ζ | 0 < ζ.im} := by
  have hw := w.im_pos
  unfold pairUc
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun ζ hζ => ?_
  have : 0 < ζ.im := hζ
  positivity

theorem continuousOn_pairUcDeriv (w : ℍ) :
    ContinuousOn (fun ζ : ℂ => pairUcDeriv ζ w) {ζ | 0 < ζ.im} := by
  have hw := w.im_pos
  have ha : ContinuousOn (fun ζ : ℂ => (ζ.re - w.re) / (2 * ζ.im * w.im)) {ζ | 0 < ζ.im} := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun ζ hζ => ?_
    have : 0 < ζ.im := hζ; positivity
  have hb : ContinuousOn (fun ζ : ℂ => (ζ.im ^ 2 - w.im ^ 2 - (ζ.re - w.re) ^ 2) /
      (4 * ζ.im ^ 2 * w.im)) {ζ | 0 < ζ.im} := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun ζ hζ => ?_
    have : 0 < ζ.im := hζ; positivity
  exact (ha.smul continuousOn_const).add (hb.smul continuousOn_const)

include hφ'c hφ'M hR hφR in
/-- **The chart derivative of one translate is continuous.** -/
theorem continuousOn_ppTermcDeriv {F : ℍ → EuclideanSpace ℂ ι} (hF : MemLp F 2 cellMeasure)
    (B : SL(2, ℤ)) : ContinuousOn (ppTermcDeriv ρ φ F B) {ζ | 0 < ζ.im} := by
  have hF1 : Integrable (fun z' => ρ B (F z')) cellMeasure :=
    (ρ B).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp
      (hF.integrable one_le_two)
  have hM' : 0 ≤ M' := (abs_nonneg _).trans (hφ'M 0)
  intro ζ₀ hζ₀
  have hζ₀' : 0 < ζ₀.im := hζ₀
  have hε : 0 < ζ₀.im / 2 := by linarith
  have hball : ∀ ζ ∈ Metric.ball ζ₀ (ζ₀.im / 2), ζ₀.im / 2 < ζ.im := by
    intro ζ hζ
    have h1 := (Complex.abs_im_le_norm (ζ - ζ₀))
    rw [Metric.mem_ball, dist_eq_norm] at hζ
    rw [Complex.sub_im] at h1
    have := abs_lt.1 (h1.trans_lt hζ)
    linarith
  refine ContinuousAt.continuousWithinAt ?_
  unfold ppTermcDeriv
  refine continuousAt_of_dominated (bound := fun z' =>
    M' * ((5 * R + 3) / (ζ₀.im / 2)) * ‖ρ B (F z')‖) ?_ ?_ ?_ ?_
  · filter_upwards [Metric.ball_mem_nhds ζ₀ hε] with ζ hζ
    have hpos : 0 < ζ.im := by linarith [hball ζ hζ]
    have hU := (continuous_pairUc_right hpos).comp (continuous_smul_int B)
    have hk : Continuous (fun z' : ℍ => deriv φ (pairUc ζ (B • z')) • pairUcDeriv ζ (B • z')) := by
      have hre : Continuous (fun w : ℍ => w.re) := UpperHalfPlane.continuous_re
      have him : Continuous (fun w : ℍ => w.im) := UpperHalfPlane.continuous_im
      have ha : Continuous (fun w : ℍ => (ζ.re - w.re) / (2 * ζ.im * w.im)) := by
        refine Continuous.div (by fun_prop) (by fun_prop) fun w => ?_
        have := w.im_pos; positivity
      have hb : Continuous (fun w : ℍ =>
          (ζ.im ^ 2 - w.im ^ 2 - (ζ.re - w.re) ^ 2) / (4 * ζ.im ^ 2 * w.im)) := by
        refine Continuous.div (by fun_prop) (by fun_prop) fun w => ?_
        have := w.im_pos; positivity
      have hD : Continuous (fun w : ℍ => pairUcDeriv ζ w) :=
        (ha.smul continuous_const).add (hb.smul continuous_const)
      exact (hφ'c.comp hU).smul (hD.comp (continuous_smul_int B))
    exact (ContinuousLinearMap.smulRightL ℝ ℂ (EuclideanSpace ℂ ι)).continuous₂.comp_aestronglyMeasurable₂
      hk.aestronglyMeasurable hF1.1
  · filter_upwards [Metric.ball_mem_nhds ζ₀ hε] with ζ hζ
    refine Eventually.of_forall fun z' => ?_
    have hζ' := hball ζ hζ
    have hpos : 0 < ζ.im := by linarith
    rw [ContinuousLinearMap.norm_smulRight_apply]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [norm_smul, Real.norm_eq_abs]
    by_cases hU : pairUc ζ (B • z') ≤ R
    · refine mul_le_mul (hφ'M _) ?_ (norm_nonneg _) hM'
      refine (norm_pairUcDeriv_le hpos hU).trans ?_
      exact div_le_div_of_nonneg_left (by linarith) hε hζ'.le
    · rw [deriv_eq_zero_of_kernelSupport hφR (lt_of_not_ge hU), abs_zero, zero_mul]
      have : 0 ≤ (5 * R + 3) / (ζ₀.im / 2) := by positivity
      positivity
  · exact (hF1.norm.const_mul _)
  · refine Eventually.of_forall fun z' => ?_
    have hc1 : ContinuousAt (fun ζ : ℂ => pairUc ζ (B • z')) ζ₀ :=
      (continuous_pairUc_left (B • z')).continuousAt (isOpen_lt continuous_const
        Complex.continuous_im |>.mem_nhds hζ₀')
    have hc2 : ContinuousAt (fun ζ : ℂ => pairUcDeriv ζ (B • z')) ζ₀ :=
      (continuousOn_pairUcDeriv (B • z')).continuousAt (isOpen_lt continuous_const
        Complex.continuous_im |>.mem_nhds hζ₀')
    have hc : ContinuousAt (fun ζ : ℂ => deriv φ (pairUc ζ (B • z')) • pairUcDeriv ζ (B • z')) ζ₀ :=
      (hφ'c.continuousAt.comp hc1).smul hc2
    have hL : Continuous (fun c : ℂ →L[ℝ] ℝ => c.smulRight (ρ B (F z'))) :=
      ((ContinuousLinearMap.smulRightL ℝ ℂ (EuclideanSpace ℂ ι)).flip (ρ B (F z'))).continuous
    exact hL.continuousAt.comp hc


omit hφd hφ'c hφM hφ'M hR hφR in
theorem ppTerm_ofComplex (φ : ℝ → ℝ) (F : ℍ → EuclideanSpace ℂ ι) (B : SL(2, ℤ)) {ζ : ℂ} (hζ : 0 < ζ.im) :
    ppTerm ρ φ F (UpperHalfPlane.ofComplex ζ) B = ppTermc ρ φ F B ζ := by
  unfold ppTerm ppTermc
  refine integral_congr_ae (Eventually.of_forall fun z' => ?_)
  simp only
  rw [← pairUc_ofComplex hζ, Complex.coe_smul]

omit hφd hφ'c hφM hφ'M hR hφR in
/-- A Euclidean ball of radius `Im ζ₀/2` lies within hyperbolic distance `1` of `ζ₀`. -/
theorem dist_ofComplex_le_one {ζ₀ ζ : ℂ} (hζ₀ : 0 < ζ₀.im) (hζ : ‖ζ - ζ₀‖ < ζ₀.im / 2) :
    dist (UpperHalfPlane.ofComplex ζ₀) (UpperHalfPlane.ofComplex ζ) ≤ 1 := by
  have him : ζ₀.im / 2 < ζ.im := by
    have h1 := Complex.abs_im_le_norm (ζ - ζ₀)
    rw [Complex.sub_im] at h1
    have := abs_lt.1 (h1.trans_lt hζ)
    linarith
  have hζp : 0 < ζ.im := by linarith
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hζ₀, UpperHalfPlane.ofComplex_apply_of_im_pos hζp]
  have hc := UpperHalfPlane.cosh_dist (⟨ζ₀, hζ₀⟩ : ℍ) ⟨ζ, hζp⟩
  have e1 : ((⟨ζ₀, hζ₀⟩ : ℍ) : ℂ) = ζ₀ := rfl
  have e2 : ((⟨ζ, hζp⟩ : ℍ) : ℂ) = ζ := rfl
  have e3 : (⟨ζ₀, hζ₀⟩ : ℍ).im = ζ₀.im := rfl
  have e4 : (⟨ζ, hζp⟩ : ℍ).im = ζ.im := rfl
  rw [e1, e2, e3, e4, dist_comm ζ₀ ζ, dist_eq_norm] at hc
  have hsq : ‖ζ - ζ₀‖ ^ 2 ≤ (ζ₀.im / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hζ.le 2
  have hq : ‖ζ - ζ₀‖ ^ 2 / (2 * ζ₀.im * ζ.im) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hcosh1 : 1 + 1 / 4 ≤ Real.cosh 1 := by
    rw [Real.cosh_eq]
    have := Real.exp_one_gt_d9
    have := Real.exp_pos (-1)
    linarith
  have hle : Real.cosh (dist (⟨ζ₀, hζ₀⟩ : ℍ) ⟨ζ, hζp⟩) ≤ Real.cosh 1 := by linarith
  rw [Real.cosh_le_cosh, abs_of_nonneg dist_nonneg, abs_one] at hle
  exact hle


include hφR in
/-- **Local finite representation in the chart.** -/
theorem chartFun_ppApply_local (F : ℍ → EuclideanSpace ℂ ι) {ζ₀ ζ : ℂ} (hζ₀ : 0 < ζ₀.im)
    (hζ : ‖ζ - ζ₀‖ < ζ₀.im / 2) :
    chartFun (ppApply ρ φ F) ζ = (1 / 2 : ℂ) •
      ∑ B ∈ ppNearSet (UpperHalfPlane.ofComplex ζ₀) (2 * (1 + 2 * R)), ppTermc ρ φ F B ζ := by
  have him : ζ₀.im / 2 < ζ.im := by
    have h1 := Complex.abs_im_le_norm (ζ - ζ₀)
    rw [Complex.sub_im] at h1
    have := abs_lt.1 (h1.trans_lt hζ)
    linarith
  have hζp : 0 < ζ.im := by linarith
  have hd := dist_ofComplex_le_one hζ₀ hζ
  show ppApply ρ φ F (UpperHalfPlane.ofComplex ζ) = _
  unfold ppApply
  congr 1
  rw [tsum_eq_sum (s := ppNearSet (UpperHalfPlane.ofComplex ζ₀) (2 * (1 + 2 * R)))]
  · exact Finset.sum_congr rfl fun B _ => ppTerm_ofComplex φ F B hζp
  · intro B hB
    refine ppTerm_eq_zero hφR F _ ?_
    rintro ⟨z', hz', h⟩
    apply hB
    simp only [ppNearSet, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨z', hz', pairU_le_of_dist_le hd h⟩

include hφd hφ'c hφM hφ'M hR hφR in
/-- **`L_φ F` is `C¹` in the chart.** -/
theorem isChartC1_ppApply {F : ℍ → EuclideanSpace ℂ ι} (hF : MemLp F 2 cellMeasure) :
    IsChartC1 (ppApply ρ φ F) := by
  intro ζ₀ hζ₀
  have hζ₀' : 0 < ζ₀.im := hζ₀
  refine ContDiffAt.contDiffWithinAt ?_
  set S := ppNearSet (UpperHalfPlane.ofComplex ζ₀) (2 * (1 + 2 * R))
  have hε : 0 < ζ₀.im / 2 := by linarith
  have hball : ∀ ζ ∈ Metric.ball ζ₀ (ζ₀.im / 2), 0 < ζ.im := by
    intro ζ hζ
    have h1 := (Complex.abs_im_le_norm (ζ - ζ₀))
    rw [Metric.mem_ball, dist_eq_norm] at hζ
    rw [Complex.sub_im] at h1
    have := abs_lt.1 (h1.trans_lt hζ)
    linarith
  rw [contDiffAt_one_iff]
  refine ⟨fun ζ => (1 / 2 : ℂ) • ∑ B ∈ S, ppTermcDeriv ρ φ F B ζ, Metric.ball ζ₀ (ζ₀.im / 2),
    Metric.ball_mem_nhds ζ₀ hε, ?_, fun ζ hζ => ?_⟩
  · exact (continuousOn_finsetSum _ fun B _ =>
      (continuousOn_ppTermcDeriv (ρ := ρ) hφ'c hφ'M hR hφR hF B).mono fun ζ hζ => hball ζ hζ).const_smul
        (1 / 2 : ℂ)
  · have hζp := hball ζ hζ
    have hg0 := (HasFDerivAt.sum (u := S) fun B _ =>
      hasFDerivAt_ppTermc (ρ := ρ) hφd hφ'c hφM hφ'M hR hφR hF B hζp).const_smul (1 / 2 : ℂ)
    have hg : HasFDerivAt (fun ζ' => (1 / 2 : ℂ) • ∑ B ∈ S, ppTermc ρ φ F B ζ')
        ((1 / 2 : ℂ) • ∑ B ∈ S, ppTermcDeriv ρ φ F B ζ) ζ := by
      have e : (fun ζ' => (1 / 2 : ℂ) • ∑ B ∈ S, ppTermc ρ φ F B ζ') =
          (1 / 2 : ℂ) • ∑ i ∈ S, ppTermc ρ φ F i := by
        funext ζ'; simp [Finset.sum_apply]
      rw [e]; exact hg0
    refine hg.congr_of_eventuallyEq ?_
    filter_upwards [Metric.isOpen_ball.mem_nhds hζ] with ζ' hζ'
    rw [Metric.mem_ball, dist_eq_norm] at hζ'
    exact chartFun_ppApply_local hφR F hζ₀' hζ'

end Diff

end

end GaloisForLFunctions.RHTower.RepPointPair
