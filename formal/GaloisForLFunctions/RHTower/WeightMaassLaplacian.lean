import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The weight-`k` Maass Laplacian of `y^{k/2}` times a holomorphic function

For the weight-`k` Laplacian `Δ_k F = -y²(F_xx + F_yy) + i k y F_x` and a holomorphic `f` on the
upper half-plane, `Δ_k (y^{k/2} f) = (k/2)(1 - k/2) y^{k/2} f`
(`weightLaplacian_rpowIm_mul`).

The directional derivatives of `y^p h(z)` are `y^p h'(z) v + p y^{p-1} (Im v) h(z)`
(`fderiv_rpowIm_mul_apply`). In direction `1` only the holomorphic part survives. In direction
`i` there is an extra `p y^{p-1} h`. The mixed terms `2ip y^{p+1} f'` cancel against the
first-order term `i k y F_x` exactly when `p = k/2`, which leaves `-p(p-1) y^p f`.

Also included is the Gaussian bound `|θ(τ)| ≤ 1 + 1/√(Im τ)` for the Jacobi theta function
(`norm_jacobiTheta_le`), from `Σ_{n≥1} e^{-bn²} ≤ ∫₀^∞ e^{-bt²} dt = √(π/b)/2`
(`gaussian_tail_le`).
-/

open Complex Filter MeasureTheory Set
open scoped Topology Real

namespace GaloisForLFunctions.RHTower.WeightMaassLaplacian

noncomputable section


/-- The weight-`k` Maass Laplacian `Δ_k F = -y²(F_xx + F_yy) + i k y F_x` in the complex chart. -/
def weightLaplacian (k : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  -(z.im : ℂ) ^ 2 * (fderiv ℝ (fun w => fderiv ℝ F w 1) z 1 +
    fderiv ℝ (fun w => fderiv ℝ F w I) z I) + I * k * z.im * fderiv ℝ F z 1

theorem hasFDerivAt_rpowIm (p : ℝ) {w : ℂ} (hw : 0 < w.im) :
    HasFDerivAt (fun u : ℂ => ((u.im ^ p : ℝ) : ℂ))
      (ofRealCLM.comp ((p * w.im ^ (p - 1)) • imCLM)) w := by
  have h1 : HasFDerivAt (fun u : ℂ => u.im) imCLM w := imCLM.hasFDerivAt
  have h2 : HasDerivAt (fun y : ℝ => y ^ p) (p * w.im ^ (p - 1)) w.im :=
    Real.hasDerivAt_rpow_const (Or.inl hw.ne')
  have h3 := h2.comp_hasFDerivAt w h1
  exact ofRealCLM.hasFDerivAt.comp w h3

/-- Directional derivative of `y^p h(z)` for holomorphic `h`. -/
theorem fderiv_rpowIm_mul_apply (p : ℝ) {h : ℂ → ℂ} {w : ℂ} (hw : 0 < w.im)
    (hh : DifferentiableAt ℂ h w) (v : ℂ) :
    fderiv ℝ (fun u => ((u.im ^ p : ℝ) : ℂ) * h u) w v =
      (w.im ^ p : ℝ) * (deriv h w * v) + h w * ((p * w.im ^ (p - 1) * v.im : ℝ) : ℂ) := by
  have hG := hasFDerivAt_rpowIm p hw
  have hH : HasFDerivAt h ((fderiv ℂ h w).restrictScalars ℝ) w :=
    hh.hasFDerivAt.restrictScalars ℝ
  have hP := hG.mul hH
  rw [show (fun u => ((u.im ^ p : ℝ) : ℂ) * h u) =
    (fun u : ℂ => ((u.im ^ p : ℝ) : ℂ)) * h from rfl, hP.fderiv]
  have hv : (fderiv ℂ h w) v = deriv h w * v := by
    have := (fderiv ℂ h w).map_smul v 1
    simp only [smul_eq_mul, mul_one] at this
    rw [this, fderiv_apply_one_eq_deriv]; ring
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.comp_apply,
    ofRealCLM_apply, imCLM_apply, smul_eq_mul, hv]

theorem differentiableAt_rpowIm_mul (p : ℝ) {h : ℂ → ℂ} {w : ℂ} (hw : 0 < w.im)
    (hh : DifferentiableAt ℂ h w) :
    DifferentiableAt ℝ (fun u => ((u.im ^ p : ℝ) : ℂ) * h u) w :=
  ((hasFDerivAt_rpowIm p hw).mul (hh.hasFDerivAt.restrictScalars ℝ)).differentiableAt

theorem isOpen_upper : IsOpen {w : ℂ | 0 < w.im} :=
  isOpen_lt continuous_const Complex.continuous_im

/-- **Weight-`k` Maass Laplacian of `y^{k/2} f` for holomorphic `f`:**
`Δ_k (y^{k/2} f) = (k/2)(1 - k/2) y^{k/2} f`. -/
theorem weightLaplacian_rpowIm_mul (k : ℝ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {w : ℂ | 0 < w.im}) {z : ℂ} (hz : 0 < z.im) :
    weightLaplacian k (fun u => ((u.im ^ (k / 2) : ℝ) : ℂ) * f u) z =
      ((k / 2 * (1 - k / 2) : ℝ) : ℂ) * (((z.im ^ (k / 2) : ℝ) : ℂ) * f z) := by
  set p := k / 2 with hpdef
  have hA := hf.analyticOnNhd isOpen_upper
  have hfd : ∀ w, 0 < w.im → DifferentiableAt ℂ f w := fun w hw =>
    (hA w hw).differentiableAt
  have hf'd : ∀ w, 0 < w.im → DifferentiableAt ℂ (deriv f) w := fun w hw =>
    (hA w hw).deriv.differentiableAt
  -- first derivatives on the half-plane
  have e1 : (fun w => fderiv ℝ (fun u => ((u.im ^ p : ℝ) : ℂ) * f u) w 1) =ᶠ[𝓝 z]
      (fun w => ((w.im ^ p : ℝ) : ℂ) * deriv f w) := by
    filter_upwards [isOpen_upper.mem_nhds hz] with w hw
    rw [fderiv_rpowIm_mul_apply p hw (hfd w hw)]
    simp
  have eI : (fun w => fderiv ℝ (fun u => ((u.im ^ p : ℝ) : ℂ) * f u) w I) =ᶠ[𝓝 z]
      (fun w => ((w.im ^ p : ℝ) : ℂ) * (I * deriv f w) +
        ((w.im ^ (p - 1) : ℝ) : ℂ) * ((p : ℂ) * f w)) := by
    filter_upwards [isOpen_upper.mem_nhds hz] with w hw
    rw [fderiv_rpowIm_mul_apply p hw (hfd w hw)]
    simp only [Complex.I_im, mul_one]
    push_cast
    ring
  -- second derivatives
  have hdI : DifferentiableAt ℂ (fun w => I * deriv f w) z :=
    (differentiableAt_const I).mul (hf'd z hz)
  have hdp : DifferentiableAt ℂ (fun w => (p : ℂ) * f w) z :=
    (differentiableAt_const _).mul (hfd z hz)
  have s1 : fderiv ℝ (fun w => fderiv ℝ (fun u => ((u.im ^ p : ℝ) : ℂ) * f u) w 1) z 1 =
      ((z.im ^ p : ℝ) : ℂ) * deriv (deriv f) z := by
    rw [e1.fderiv_eq, fderiv_rpowIm_mul_apply p hz (hf'd z hz)]
    simp
  have sI : fderiv ℝ (fun w => fderiv ℝ (fun u => ((u.im ^ p : ℝ) : ℂ) * f u) w I) z I =
      -((z.im ^ p : ℝ) : ℂ) * deriv (deriv f) z +
        2 * I * (p : ℂ) * ((z.im ^ (p - 1) : ℝ) : ℂ) * deriv f z +
        (p : ℂ) * ((p - 1 : ℝ) : ℂ) * ((z.im ^ (p - 1 - 1) : ℝ) : ℂ) * f z := by
    rw [eI.fderiv_eq]
    rw [show (fun w => ((w.im ^ p : ℝ) : ℂ) * (I * deriv f w) +
        ((w.im ^ (p - 1) : ℝ) : ℂ) * ((p : ℂ) * f w)) =
        (fun w => ((w.im ^ p : ℝ) : ℂ) * (I * deriv f w)) +
          (fun w => ((w.im ^ (p - 1) : ℝ) : ℂ) * ((p : ℂ) * f w)) from rfl]
    rw [fderiv_add (differentiableAt_rpowIm_mul p hz hdI) (differentiableAt_rpowIm_mul (p - 1) hz hdp)]
    rw [add_apply, fderiv_rpowIm_mul_apply p hz hdI,
      fderiv_rpowIm_mul_apply (p - 1) hz hdp]
    have d1 : deriv (fun w => I * deriv f w) z = I * deriv (deriv f) z := by
      rw [deriv_const_mul _ (hf'd z hz)]
    have d2 : deriv (fun w => (p : ℂ) * f w) z = (p : ℂ) * deriv f z := by
      rw [deriv_const_mul _ (hfd z hz)]
    rw [d1, d2]
    simp only [Complex.I_im, mul_one]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  unfold weightLaplacian
  rw [s1, sI, fderiv_rpowIm_mul_apply p hz (hfd z hz)]
  simp only [Complex.one_im, mul_zero, Complex.ofReal_zero, mul_one, add_zero]
  have hy : 0 < z.im := hz
  set Y := z.im ^ p with hYdef
  have r1 : z.im ^ (p - 1) = Y * z.im⁻¹ := by
    rw [Real.rpow_sub_one hy.ne', div_eq_mul_inv]
  have r2 : z.im ^ (p - 1 - 1) = Y * (z.im⁻¹) ^ 2 := by
    rw [Real.rpow_sub_one hy.ne', Real.rpow_sub_one hy.ne', ← hYdef]
    field_simp
  rw [r1, r2]
  have hyC : (z.im : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hk : (k : ℂ) = 2 * p := by rw [hpdef]; push_cast; ring
  rw [hk]
  push_cast
  field_simp
  ring_nf


/-- The Gaussian tail `Σ_{n≥1} e^{-b n²} ≤ √(π/b)/2`. -/
theorem gaussian_tail_le {b : ℝ} (hb : 0 < b) :
    ∑' n : ℕ, Real.exp (-b * ((n : ℝ) + 1) ^ 2) ≤ √(π / b) / 2 := by
  have hanti : AntitoneOn (fun t : ℝ => Real.exp (-b * t ^ 2)) (Ici 0) := by
    intro s hs t ht hst
    apply Real.exp_le_exp.mpr
    have : s ^ 2 ≤ t ^ 2 := by nlinarith [mem_Ici.mp hs]
    nlinarith
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-b * t ^ 2)) (Ioi 0) :=
    (integrable_exp_neg_mul_sq hb).integrableOn
  apply Real.tsum_le_of_sum_range_le (fun n => (Real.exp_pos _).le)
  intro a
  have h1 := AntitoneOn.sum_le_integral (x₀ := 0) (a := a)
    (f := fun t : ℝ => Real.exp (-b * t ^ 2)) (hanti.mono (by
      intro t ht; exact mem_Ici.mpr ht.1))
  simp only [zero_add, Nat.cast_add, Nat.cast_one] at h1
  calc ∑ i ∈ Finset.range a, Real.exp (-b * ((i : ℝ) + 1) ^ 2)
      ≤ ∫ x in (0 : ℝ)..a, Real.exp (-b * x ^ 2) := h1
    _ ≤ ∫ x in Ioi (0 : ℝ), Real.exp (-b * x ^ 2) := by
        rw [intervalIntegral.integral_of_le (Nat.cast_nonneg a)]
        exact setIntegral_mono_set hint (Eventually.of_forall fun x => (Real.exp_pos _).le)
          (Eventually.of_forall Ioc_subset_Ioi_self)
    _ = √(π / b) / 2 := integral_gaussian_Ioi b

theorem summable_gaussian_tail {b : ℝ} (hb : 0 < b) :
    Summable fun n : ℕ => Real.exp (-b * ((n : ℝ) + 1) ^ 2) := by
  have hg : Summable fun n : ℕ => Real.exp (-b) ^ n :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hb))
  refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_) hg
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have : (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  nlinarith

/-- `|θ(τ)| ≤ 1 + 1/√(Im τ)` for the Jacobi theta function `θ(τ) = Σ e^{πi n² τ}`. -/
theorem norm_jacobiTheta_le {τ : ℂ} (hτ : 0 < τ.im) : ‖jacobiTheta τ‖ ≤ 1 + 1 / √τ.im := by
  rw [jacobiTheta_eq_tsum_nat hτ]
  have hb : 0 < π * τ.im := mul_pos Real.pi_pos hτ
  have hterm : ∀ n : ℕ, ‖Complex.exp (((π : ℝ) : ℂ) * I * ((n : ℂ) + 1) ^ 2 * τ)‖ =
      Real.exp (-(π * τ.im) * ((n : ℝ) + 1) ^ 2) := by
    intro n
    rw [Complex.norm_exp]
    congr 1
    have e : ((n : ℂ) + 1) ^ 2 = (((n : ℝ) + 1) ^ 2 : ℝ) := by push_cast; ring
    rw [e]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hsum := summable_gaussian_tail hb
  have hsumN : Summable fun n : ℕ => ‖Complex.exp (((π : ℝ) : ℂ) * I * ((n : ℂ) + 1) ^ 2 * τ)‖ := by
    simp_rw [hterm]; exact hsum
  have htail := gaussian_tail_le hb
  have hsq : √(π / (π * τ.im)) = 1 / √τ.im := by
    rw [div_mul_eq_div_div, div_self Real.pi_ne_zero, one_div, Real.sqrt_inv, one_div]
  calc ‖1 + 2 * ∑' n : ℕ, Complex.exp (((π : ℝ) : ℂ) * I * ((n : ℂ) + 1) ^ 2 * τ)‖
      ≤ ‖(1 : ℂ)‖ + ‖(2 : ℂ)‖ * ‖∑' n : ℕ, Complex.exp (((π : ℝ) : ℂ) * I * ((n : ℂ) + 1) ^ 2 * τ)‖ := by
        rw [← norm_mul]; exact norm_add_le _ _
    _ ≤ 1 + 2 * ∑' n : ℕ, Real.exp (-(π * τ.im) * ((n : ℝ) + 1) ^ 2) := by
        rw [norm_one, Complex.norm_two]
        gcongr
        calc ‖∑' n : ℕ, Complex.exp (((π : ℝ) : ℂ) * I * ((n : ℂ) + 1) ^ 2 * τ)‖
            ≤ ∑' n : ℕ, ‖Complex.exp (((π : ℝ) : ℂ) * I * ((n : ℂ) + 1) ^ 2 * τ)‖ :=
              norm_tsum_le_tsum_norm hsumN
          _ = _ := by simp_rw [hterm]
    _ ≤ 1 + 2 * (√(π / (π * τ.im)) / 2) := by gcongr
    _ = 1 + 1 / √τ.im := by rw [hsq]; ring

end

end GaloisForLFunctions.RHTower.WeightMaassLaplacian
