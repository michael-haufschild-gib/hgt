import GaloisForLFunctions.RHTower.CauchyTransformHardy
import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy
import GaloisForLFunctions.HTGeometry.CauchyKernelLineMass
import GaloisForLFunctions.HTGeometry.GoldenRuleAmplitude

/-!
# The normalized Cauchy transform of an arbitrary L² density

The paper's reconstruction integral has an L² density on the whole real line,
not an integrable density against a finite measure. Cauchy–Schwarz supplies its
integrability, a relative kernel bound supplies a locally uniform integrable
majorant, and the corpus's Cauchy-dominated holomorphy theorem proves analyticity.
The exact kernel mass gives the usual inverse-square-root height bound.
-/

open MeasureTheory Complex Set Filter Topology Metric
open GaloisForLFunctions.HTGeometry
namespace RHTower.FokasLenells
noncomputable section

/-- Points above or below the real axis, with positivity discharged by an exponential height. -/
def halfPlanePoint (upper : Bool) (r a : ℝ) : ℂ :=
  (r:ℂ)+(if upper then (Real.exp a:ℝ) else -Real.exp a)*I

theorem halfPlanePoint_im (upper : Bool) (r a : ℝ) :
    (halfPlanePoint upper r a).im = if upper then Real.exp a else -Real.exp a := by
  cases upper <;> simp only [halfPlanePoint,Bool.false_eq_true,↓reduceIte,Complex.add_im,
    Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    zero_mul,mul_one,add_zero,zero_add]

theorem halfPlanePoint_im_ne_zero (upper : Bool) (r a : ℝ) :
    (halfPlanePoint upper r a).im ≠ 0 := by
  rw [halfPlanePoint_im]
  cases upper <;> simpa only [Bool.false_eq_true,↓reduceIte,neg_ne_zero] using Real.exp_ne_zero a

theorem abs_halfPlanePoint_im (upper : Bool) (r a : ℝ) :
    |(halfPlanePoint upper r a).im| = Real.exp a := by
  rw [halfPlanePoint_im]
  cases upper <;> simp [abs_of_pos (Real.exp_pos a)]

/-- The paper's Cauchy integral, defined for every L² input without extra assumptions. -/
def cauchyExtension (u : SoninL2) (z : ℂ) : ℂ :=
  (2*(Real.pi:ℂ)*I)⁻¹ * ∫ s : ℝ, (u : ℝ → ℂ) s / ((s:ℂ)-z)

private theorem cauchy_integrable (u : SoninL2) {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (fun s : ℝ => (u : ℝ → ℂ) s / ((s:ℂ)-z)) volume := by
  have h := (Lp.memLp u).integrable_mul (memLp_cauchyKernel hz)
  change Integrable (fun s : ℝ => (u : ℝ → ℂ) s * ((s:ℂ)-z)⁻¹) volume at h
  simpa only [div_eq_mul_inv] using h

/-- The reconstruction integral is absolutely integrable at every point in either half-plane. -/
theorem cauchyExtension_integrable (u : SoninL2) (upper : Bool) (r a : ℝ) :
    Integrable (fun s : ℝ => (u : ℝ → ℂ) s / ((s:ℂ)-halfPlanePoint upper r a)) volume :=
  cauchy_integrable u (halfPlanePoint_im_ne_zero upper r a)

private theorem relative_cauchy_kernel_bound {w z : ℂ} (hw : w.im ≠ 0)
    (hz : z ∈ ball w (|w.im|/2)) (s : ℝ) :
    ‖((s:ℂ)-z)⁻¹‖ ≤ 2*‖((s:ℂ)-w)⁻¹‖ := by
  have hi : |w.im| ≤ ‖(s:ℂ)-w‖ := by
    simpa only [Complex.sub_im,Complex.ofReal_im,zero_sub,abs_neg] using
      Complex.abs_im_le_norm ((s:ℂ)-w)
  have hd : ‖z-w‖ < |w.im|/2 := by simpa only [Metric.mem_ball,dist_eq_norm] using hz
  have ht : ‖(s:ℂ)-w‖ ≤ ‖(s:ℂ)-z‖+‖z-w‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le ((s:ℂ)-z) (z-w)
  have hpw : 0 < ‖(s:ℂ)-w‖ := lt_of_lt_of_le (abs_pos.mpr hw) hi
  have hpz : 0 < ‖(s:ℂ)-z‖ := by linarith
  have h := (div_le_div_iff₀ hpz hpw).mpr (show (1:ℝ)*‖(s:ℂ)-w‖ ≤ 2*‖(s:ℂ)-z‖ by linarith)
  simpa only [norm_inv,one_div,div_eq_mul_inv,one_mul] using h

/-- Arbitrary L² Cauchy densities give genuine holomorphic functions off the real axis. -/
theorem analyticOnNhd_cauchyExtension (u : SoninL2) :
    AnalyticOnNhd ℂ (cauchyExtension u) {z : ℂ | z.im ≠ 0} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_ne_fun Complex.continuous_im continuous_const)
  intro w hw
  have hr : 0 < |w.im|/2 := by exact div_pos (abs_pos.mpr hw) (by positivity)
  have hmaj : Integrable (fun s : ℝ => 2*(‖(u : ℝ → ℂ) s‖*‖((s:ℂ)-w)⁻¹‖)) volume := by
    have h := ((Lp.memLp u).norm.integrable_mul (memLp_cauchyKernel hw).norm).const_mul (2:ℝ)
    exact h
  have hh := differentiableAt_integral_of_cauchy_dominated
    (F := fun z s => (u : ℝ → ℂ) s / ((s:ℂ)-z)) (z₀ := w) hr
    (fun z _ => by
      have hm := (Lp.aestronglyMeasurable u).mul
        (Complex.measurable_ofReal.sub (measurable_const (a := z))).inv.aestronglyMeasurable
      change AEStronglyMeasurable (fun s : ℝ => (u : ℝ → ℂ) s*((s:ℂ)-z)⁻¹) volume at hm
      simpa only [div_eq_mul_inv] using hm)
    (fun s z hz => ((differentiableAt_const ((u : ℝ → ℂ) s)).div
      (differentiableAt_const (s:ℂ) |>.sub differentiableAt_id)
      (by
        have hi : 0 < ‖(s:ℂ)-z‖ := by
          have h2 : |w.im| ≤ ‖(s:ℂ)-w‖ := by
            simpa using Complex.abs_im_le_norm ((s:ℂ)-w)
          have h3 : ‖(s:ℂ)-w‖ ≤ ‖(s:ℂ)-z‖+‖z-w‖ := by
            simpa only [sub_add_sub_cancel] using norm_add_le ((s:ℂ)-z) (z-w)
          have h4 : ‖z-w‖ < |w.im|/2 := by simpa only [Metric.mem_ball,dist_eq_norm] using hz
          have h5 := abs_pos.mpr hw
          linarith
        exact norm_pos_iff.mp hi)).differentiableWithinAt)
    (fun s z hz => by
      rw [norm_div,div_eq_mul_inv,← norm_inv]
      calc
        ‖(u : ℝ → ℂ) s‖*‖((s:ℂ)-z)⁻¹‖ ≤
            ‖(u : ℝ → ℂ) s‖*(2*‖((s:ℂ)-w)⁻¹‖) :=
          mul_le_mul_of_nonneg_left (relative_cauchy_kernel_bound hw hz s) (norm_nonneg _)
        _ = _ := by ring) hmaj
  exact (hh.const_mul _).differentiableWithinAt

private theorem integral_cauchy_eq_inner (u : SoninL2) {z : ℂ} (hz : z.im ≠ 0) :
    (∫ s : ℝ, (u : ℝ → ℂ) s / ((s:ℂ)-z)) =
      inner ℂ ((memLp_cauchyKernel (conj_im_ne hz)).toLp
        (fun s : ℝ => ((s:ℂ)-(starRingEnd ℂ) z)⁻¹)) u := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_cauchyKernel (conj_im_ne hz)).coeFn_toLp] with s hs
  rw [RCLike.inner_apply,hs,map_inv₀,map_sub,Complex.conj_ofReal,Complex.conj_conj,div_eq_mul_inv]

private theorem norm_cauchy_kernel_sq {z : ℂ} (hz : z.im ≠ 0) :
    ‖(memLp_cauchyKernel hz).toLp (fun s : ℝ => ((s:ℂ)-z)⁻¹)‖^(2 : ℕ) = Real.pi/|z.im| := by
  rw [lpTwo_norm_sq_eq_integral]
  calc
    (∫ s : ℝ, ‖((memLp_cauchyKernel hz).toLp (fun s : ℝ => ((s:ℂ)-z)⁻¹) : ℝ → ℂ) s‖^(2 : ℕ)) =
        ∫ s : ℝ, (|z.im|^(2 : ℕ)+(s-z.re)^(2 : ℕ))⁻¹ := by
      apply integral_congr_ae
      filter_upwards [(memLp_cauchyKernel hz).coeFn_toLp] with s hs
      rw [hs,norm_sq_cauchyKernel,sq_abs,add_comm]
    _ = _ := integral_inv_sq_add_sq_shift (abs_pos.mpr hz)

private theorem norm_cauchy_extension_le (u : SoninL2) {z : ℂ} (hz : z.im ≠ 0) :
    ‖cauchyExtension u z‖ ≤ (2*Real.pi)⁻¹ * Real.sqrt (Real.pi/|z.im|) * ‖u‖ := by
  have hk : ‖(memLp_cauchyKernel (conj_im_ne hz)).toLp
      (fun s : ℝ => ((s:ℂ)-(starRingEnd ℂ) z)⁻¹)‖ = Real.sqrt (Real.pi/|z.im|) := by
    have he := norm_cauchy_kernel_sq (conj_im_ne hz)
    rw [Complex.conj_im,abs_neg] at he
    rw [← he,Real.sqrt_sq (norm_nonneg _)]
  rw [cauchyExtension,norm_mul,integral_cauchy_eq_inner u hz]
  have hn : ‖(2*(Real.pi:ℂ)*I)⁻¹‖ = (2*Real.pi)⁻¹ := by
    simp only [norm_inv,norm_mul,Complex.norm_I,mul_one,norm_ofNat,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hn,mul_assoc]
  exact mul_le_mul_of_nonneg_left
    ((norm_inner_le_norm _ _).trans_eq (by rw [hk])) (by positivity)

/-- The exact Cauchy-kernel mass yields an explicit point-evaluation bound at every height. -/
theorem cauchyExtension_bound (u : SoninL2) (upper : Bool) (r a : ℝ) :
    ‖cauchyExtension u (halfPlanePoint upper r a)‖ ≤
      (2*Real.pi)⁻¹ * Real.sqrt (Real.pi/Real.exp a) * ‖u‖ := by
  simpa only [abs_halfPlanePoint_im] using
    norm_cauchy_extension_le u (halfPlanePoint_im_ne_zero upper r a)

/-- Cauchy evaluation is a bounded linear functional on the whole L² carrier. -/
def cauchyEvaluation (upper : Bool) (r a : ℝ) : SoninL2 →L[ℂ] ℂ :=
  (2*(Real.pi:ℂ)*I)⁻¹ • innerSL ℂ
    ((memLp_cauchyKernel (conj_im_ne (halfPlanePoint_im_ne_zero upper r a))).toLp
      (fun s : ℝ => ((s:ℂ)-(starRingEnd ℂ) (halfPlanePoint upper r a))⁻¹))

theorem cauchyEvaluation_apply (upper : Bool) (r a : ℝ) (u : SoninL2) :
    cauchyEvaluation upper r a u = cauchyExtension u (halfPlanePoint upper r a) := by
  change (2*(Real.pi:ℂ)*I)⁻¹ * inner ℂ _ u = _
  rw [← integral_cauchy_eq_inner u (halfPlanePoint_im_ne_zero upper r a)]
  rfl

theorem norm_cauchyEvaluation_le (upper : Bool) (r a : ℝ) :
    ‖cauchyEvaluation upper r a‖ ≤ (2*Real.pi)⁻¹ * Real.sqrt (Real.pi/Real.exp a) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  rw [cauchyEvaluation_apply]
  exact cauchyExtension_bound u upper r a

/-- L² perturbations control complex values uniformly along each horizontal line. -/
theorem cauchyExtension_lipschitz (u v : SoninL2) (upper : Bool) (r a : ℝ) :
    ‖cauchyExtension u (halfPlanePoint upper r a)-cauchyExtension v (halfPlanePoint upper r a)‖ ≤
      (2*Real.pi)⁻¹ * Real.sqrt (Real.pi/Real.exp a) * ‖u-v‖ := by
  rw [← cauchyEvaluation_apply,← cauchyEvaluation_apply,← map_sub,cauchyEvaluation_apply]
  exact cauchyExtension_bound (u-v) upper r a

theorem cauchyExtension_add (u v : SoninL2) (upper : Bool) (r a : ℝ) :
    cauchyExtension (u+v) (halfPlanePoint upper r a) =
      cauchyExtension u (halfPlanePoint upper r a)+cauchyExtension v (halfPlanePoint upper r a) := by
  simp only [← cauchyEvaluation_apply,map_add]

theorem cauchyExtension_smul (c : ℂ) (u : SoninL2) (upper : Bool) (r a : ℝ) :
    cauchyExtension (c • u) (halfPlanePoint upper r a) =
      c*cauchyExtension u (halfPlanePoint upper r a) := by
  simp only [← cauchyEvaluation_apply,map_smul,smul_eq_mul]

/-- The Cauchy extension vanishes as height tends to infinity, with arbitrary horizontal drift. -/
theorem cauchyExtension_tendsto_vertical_infinity (u : SoninL2) (upper : Bool) (r : ℝ → ℝ) :
    Tendsto (fun a : ℝ => cauchyExtension u (halfPlanePoint upper (r a) a)) atTop (𝓝 0) := by
  have ht : Tendsto (fun a : ℝ => Real.pi/Real.exp a) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,← Real.exp_neg,mul_zero] using
      Real.tendsto_exp_neg_atTop_nhds_zero.const_mul Real.pi
  have hs : Tendsto (fun a : ℝ => (2*Real.pi)⁻¹*Real.sqrt (Real.pi/Real.exp a)*‖u‖) atTop (𝓝 0) := by
    simpa using ((Real.continuous_sqrt.tendsto 0).comp ht).const_mul ((2*Real.pi)⁻¹) |>.mul_const ‖u‖
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  exact squeeze_zero (fun a => norm_nonneg _) (fun a => cauchyExtension_bound u upper (r a) a) hs

end
end RHTower.FokasLenells
