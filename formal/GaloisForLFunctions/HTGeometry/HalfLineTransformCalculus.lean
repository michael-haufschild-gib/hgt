import GaloisForLFunctions.HTGeometry.OscillatoryPacketFourier
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Half-line exponential and sine transforms

* `∫₀^∞ e^{wu} f(u) du` is holomorphic on `Re w < σ` whenever `e^{σu} f` is integrable, with
  derivative the transform of `u f(u)` (dominated differentiation).
* For a *causal source* `f` (smooth, all derivatives integrable on `(0, ∞)` and tending to zero)
  two integrations by parts give `c_f(γ) = f(0)/γ - c_{f''}(γ)/γ²` for the sine transform
  `c_f(γ) = ∫₀^∞ f sin(γu)`, hence the jet expansion
  `c_f = Σ_{j<m} (-1)^j f^{(2j)}(0)/γ^{2j+1} + (-1)^m c_{f^{(2m)}}/γ^{2m}`; with the
  Riemann–Lebesgue lemma, `γ^{2m+1} c_f(γ) → (-1)^m f^{(2m)}(0)` at the first nonzero even jet.
* All even jets vanish iff `c_f` decays faster than every power; an analytic germ with vanishing
  even jets is odd.
-/
open Complex Filter Topology Set MeasureTheory
open scoped ContDiff

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Exponential transforms on the half-line -/

/-- The half-line exponential transform `∫₀^∞ e^{wu} f(u) du`. -/
def halfLineExpTransform (f : ℝ → ℂ) (w : ℂ) : ℂ := ∫ u in Ioi (0 : ℝ), cexp (w * u) * f u

theorem integrableOn_cexp_mul_of_moment {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0))) {σ : ℝ}
    (hmom : IntegrableOn (fun u => Real.exp (σ * u) * ‖f u‖) (Ioi 0)) {w : ℂ} (hw : w.re ≤ σ) :
    IntegrableOn (fun u : ℝ => cexp (w * u) * f u) (Ioi 0) := by
  refine hmom.mono' ((by fun_prop : Continuous fun u : ℝ => cexp (w * u)).aestronglyMeasurable.mul hf)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun u hu => ?_))
  have hu : (0 : ℝ) ≤ u := le_of_lt hu
  rw [norm_mul, Complex.norm_exp]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  exact mul_le_mul_of_nonneg_right hw hu

/-- **Differentiation in the strip of convergence.** If `e^{σu} f` is integrable, the transform
is holomorphic on `Re w < σ` with derivative the transform of `u f(u)`. -/
theorem hasDerivAt_halfLineExpTransform {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0))) {σ : ℝ}
    (hmom : IntegrableOn (fun u => Real.exp (σ * u) * ‖f u‖) (Ioi 0)) {w : ℂ} (hw : w.re < σ) :
    HasDerivAt (halfLineExpTransform f) (halfLineExpTransform (fun u => u * f u) w) w := by
  set ε := (σ - w.re) / 2
  have hε : 0 < ε := by simp only [ε]; linarith
  set F : ℂ → ℝ → ℂ := fun z u => cexp (z * u) * f u
  set F' : ℂ → ℝ → ℂ := fun z u => cexp (z * u) * (u * f u)
  have hmeasF : ∀ z, AEStronglyMeasurable (F z) (volume.restrict (Ioi 0)) := fun z =>
    (by fun_prop : Continuous fun u : ℝ => cexp (z * u)).aestronglyMeasurable.mul hf
  have hmeasF' : AEStronglyMeasurable (F' w) (volume.restrict (Ioi 0)) :=
    (by fun_prop : Continuous fun u : ℝ => cexp (w * u)).aestronglyMeasurable.mul
      ((by fun_prop : Continuous fun u : ℝ => (u : ℂ)).aestronglyMeasurable.mul hf)
  have hbound : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))), ∀ z ∈ Metric.ball w ε,
      ‖F' z u‖ ≤ ε⁻¹ * (Real.exp (σ * u) * ‖f u‖) := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun u hu z hz => ?_)
    have hu : (0 : ℝ) ≤ u := le_of_lt hu
    have hzre : z.re ≤ w.re + ε := by
      have := Complex.abs_re_le_norm (z - w)
      rw [Metric.mem_ball, dist_eq_norm] at hz
      simp only [sub_re] at this
      linarith [abs_le.mp this |>.2]
    simp only [F']
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
    have hre : (z * (u : ℂ)).re = z.re * u := by simp
    rw [hre]
    have hlin : u ≤ ε⁻¹ * Real.exp (ε * u) := by
      rw [le_inv_mul_iff₀ hε]; linarith [Real.add_one_le_exp (ε * u)]
    calc Real.exp (z.re * u) * (u * ‖f u‖)
        ≤ Real.exp ((w.re + ε) * u) * (ε⁻¹ * Real.exp (ε * u) * ‖f u‖) := by
          gcongr
      _ = ε⁻¹ * (Real.exp (((w.re + ε) + ε) * u) * ‖f u‖) := by
          rw [show ((w.re + ε) + ε) * u = (w.re + ε) * u + ε * u by ring, Real.exp_add]; ring
      _ = ε⁻¹ * (Real.exp (σ * u) * ‖f u‖) := by
          congr 3; simp only [ε]; ring
  have hdiff : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))), ∀ z ∈ Metric.ball w ε,
      HasDerivAt (fun z => F z u) (F' z u) z := by
    refine ae_of_all _ fun u z _ => ?_
    have h := (((hasDerivAt_id z).mul_const (u : ℂ)).cexp).mul_const (f u)
    refine h.congr_deriv ?_
    simp only [F', id]; ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds w hε)
    (Eventually.of_forall hmeasF) (integrableOn_cexp_mul_of_moment hf hmom (by linarith))
    hmeasF' hbound (hmom.const_mul _) hdiff
  have e : halfLineExpTransform (fun u => u * f u) w = ∫ u in Ioi (0 : ℝ), F' w u := by
    rw [halfLineExpTransform]
  rw [e]
  exact key.2

/-! ## The sine transform and its jet expansion -/

/-- A causal source: a smooth function whose derivatives are all integrable on `(0, ∞)` and tend
to zero at `+∞`. -/
structure CausalSource (f : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ f
  integrableOn : ∀ n, IntegrableOn (iteratedDeriv n f) (Ioi 0)
  tendsto : ∀ n, Tendsto (iteratedDeriv n f) atTop (𝓝 0)

/-- The half-line sine transform `c_f(γ) = ∫₀^∞ f(u) sin(γu) du`. -/
def halfLineSine (f : ℝ → ℝ) (γ : ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), f u * Real.sin (γ * u)

/-- The half-line cosine transform. -/
def halfLineCos (f : ℝ → ℝ) (γ : ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), f u * Real.cos (γ * u)

namespace CausalSource

variable {f : ℝ → ℝ}

theorem iteratedDeriv_iteratedDeriv (m n : ℕ) :
    _root_.iteratedDeriv m (_root_.iteratedDeriv n f) = _root_.iteratedDeriv (m + n) f := by
  simp only [iteratedDeriv_eq_iterate]
  funext x
  rw [Function.iterate_add_apply]

theorem iteratedDeriv (hf : CausalSource f) (n : ℕ) : CausalSource (_root_.iteratedDeriv n f) := by
  refine ⟨?_, fun m => ?_, fun m => ?_⟩
  · rw [iteratedDeriv_eq_iterate]; exact hf.contDiff.iterate_deriv n
  · rw [iteratedDeriv_iteratedDeriv]; exact hf.integrableOn (m + n)
  · rw [iteratedDeriv_iteratedDeriv]; exact hf.tendsto (m + n)

theorem continuous (hf : CausalSource f) : Continuous f := hf.contDiff.continuous

theorem hasDerivAt (hf : CausalSource f) (x : ℝ) : HasDerivAt f (deriv f x) x :=
  (hf.contDiff.differentiable (by simp) x).hasDerivAt

theorem continuous_deriv (hf : CausalSource f) : Continuous (deriv f) :=
  hf.contDiff.continuous_deriv (by simp)

theorem integrableOn_self (hf : CausalSource f) : IntegrableOn f (Ioi 0) := by
  simpa using hf.integrableOn 0

theorem integrableOn_deriv (hf : CausalSource f) : IntegrableOn (deriv f) (Ioi 0) := by
  simpa [iteratedDeriv_one] using hf.integrableOn 1

theorem tendsto_self (hf : CausalSource f) : Tendsto f atTop (𝓝 0) := by
  simpa using hf.tendsto 0

theorem tendsto_deriv (hf : CausalSource f) : Tendsto (deriv f) atTop (𝓝 0) := by
  simpa [iteratedDeriv_one] using hf.tendsto 1

theorem integrableOn_mul_sin (hf : CausalSource f) (γ : ℝ) :
    IntegrableOn (fun u => f u * Real.sin (γ * u)) (Ioi 0) := by
  refine hf.integrableOn_self.norm.mono' ((hf.continuous.mul (by fun_prop)).aestronglyMeasurable)
    (ae_of_all _ fun u => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)

theorem integrableOn_deriv_mul_cos (hf : CausalSource f) (γ : ℝ) :
    IntegrableOn (fun u => deriv f u * Real.cos (γ * u)) (Ioi 0) := by
  refine hf.integrableOn_deriv.norm.mono' ((hf.continuous_deriv.mul (by fun_prop)).aestronglyMeasurable)
    (ae_of_all _ fun u => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

/-- First integration by parts: `c_f(γ) = f(0)/γ + (1/γ) ∫₀^∞ f' cos(γu)`. -/
theorem halfLineSine_eq_cos (hf : CausalSource f) {γ : ℝ} (hγ : γ ≠ 0) :
    halfLineSine f γ = f 0 / γ + halfLineCos (deriv f) γ / γ := by
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun u => -Real.cos (γ * u) / γ) (Real.sin (γ * x)) x := by
    intro x _
    have h := (((hasDerivAt_id x).const_mul γ).cos.neg).div_const γ
    refine h.congr_deriv ?_
    simp only [id]; field_simp
  have hbd : ∀ u, |-Real.cos (γ * u) / γ| ≤ 1 / |γ| := fun u => by
    rw [abs_div, abs_neg]; exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)
  have hlim0 : Tendsto (f * fun u => -Real.cos (γ * u) / γ) (𝓝[>] 0) (𝓝 (-(f 0) / γ)) := by
    have hc : Continuous (f * fun u => -Real.cos (γ * u) / γ) := hf.continuous.mul (by fun_prop)
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    convert this using 2
    simp [Pi.mul_apply]; ring
  have hlimtop : Tendsto (f * fun u => -Real.cos (γ * u) / γ) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun u => ?_) ((hf.tendsto_self.norm.mul_const (1 / |γ|)).trans_eq
      (by simp))
    rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs (-_ / _)]
    exact mul_le_mul_of_nonneg_left (hbd u) (norm_nonneg _)
  have huv' : IntegrableOn (f * fun u => Real.sin (γ * u)) (Ioi 0) := hf.integrableOn_mul_sin γ
  have hu'v : IntegrableOn (deriv f * fun u => -Real.cos (γ * u) / γ) (Ioi 0) := by
    refine IntegrableOn.congr_fun ((hf.integrableOn_deriv_mul_cos γ).neg.div_const γ)
      (fun u _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply, Pi.neg_apply]; ring
  have h := integral_Ioi_mul_deriv_eq_deriv_mul (fun x _ => hf.hasDerivAt x) hv huv' hu'v hlim0 hlimtop
  rw [halfLineSine, h, halfLineCos]
  rw [show (fun x => deriv f x * (-Real.cos (γ * x) / γ)) =
    fun x => -(deriv f x * Real.cos (γ * x)) / γ by funext x; ring, integral_div, integral_neg]
  field_simp
  ring

/-- Second integration by parts: `∫₀^∞ f' cos(γu) = -(1/γ) ∫₀^∞ f'' sin(γu)`. -/
theorem halfLineCos_deriv_eq (hf : CausalSource f) {γ : ℝ} (hγ : γ ≠ 0) :
    halfLineCos (deriv f) γ = -halfLineSine (_root_.iteratedDeriv 2 f) γ / γ := by
  have hf1 := hf.iteratedDeriv 1
  rw [iteratedDeriv_one] at hf1
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun u => Real.sin (γ * u) / γ) (Real.cos (γ * x)) x := by
    intro x _
    have h := (((hasDerivAt_id x).const_mul γ).sin).div_const γ
    refine h.congr_deriv ?_
    simp only [id]; field_simp
  have hlim0 : Tendsto (deriv f * fun u => Real.sin (γ * u) / γ) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (deriv f * fun u => Real.sin (γ * u) / γ) :=
      hf.continuous_deriv.mul (by fun_prop)
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa [Pi.mul_apply] using this
  have hlimtop : Tendsto (deriv f * fun u => Real.sin (γ * u) / γ) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun u => ?_) ((hf.tendsto_deriv.norm.mul_const (1 / |γ|)).trans_eq
      (by simp))
    rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs (_ / _), abs_div]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (Real.abs_sin_le_one _)
      (abs_nonneg _)) (norm_nonneg _)
  have huv' : IntegrableOn (deriv f * fun u => Real.cos (γ * u)) (Ioi 0) :=
    hf.integrableOn_deriv_mul_cos γ
  have hf2 := hf.iteratedDeriv 2
  have hu'v : IntegrableOn (deriv (deriv f) * fun u => Real.sin (γ * u) / γ) (Ioi 0) := by
    have h2 : deriv (deriv f) = _root_.iteratedDeriv 2 f := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [h2]
    refine IntegrableOn.congr_fun ((hf2.integrableOn_mul_sin γ).div_const γ) (fun u _ => ?_)
      measurableSet_Ioi
    simp only [Pi.mul_apply]; ring
  have h := integral_Ioi_mul_deriv_eq_deriv_mul
    (fun x _ => ((hf1.hasDerivAt x))) hv huv' hu'v hlim0 hlimtop
  rw [halfLineCos, h, halfLineSine, sub_self, zero_sub,
    show (fun x => deriv (deriv f) x * (Real.sin (γ * x) / γ)) =
      fun x => _root_.iteratedDeriv 2 f x * Real.sin (γ * x) / γ by
        funext x; rw [iteratedDeriv_succ, iteratedDeriv_one]; ring,
    integral_div]
  ring

/-- **The jet recursion.** `c_f(γ) = f(0)/γ - c_{f''}(γ)/γ²`. -/
theorem halfLineSine_eq_sub (hf : CausalSource f) {γ : ℝ} (hγ : γ ≠ 0) :
    halfLineSine f γ = f 0 / γ - halfLineSine (_root_.iteratedDeriv 2 f) γ / γ ^ 2 := by
  rw [hf.halfLineSine_eq_cos hγ, hf.halfLineCos_deriv_eq hγ]
  field_simp
  ring

/-- `γ c_f(γ) → f(0)` as `γ → ∞` (Riemann–Lebesgue). -/
theorem tendsto_mul_halfLineSine (hf : CausalSource f) :
    Tendsto (fun γ => γ * halfLineSine f γ) atTop (𝓝 (f 0)) := by
  have hRL : Tendsto (fun γ : ℝ => ∫ u in Ioi (0 : ℝ), deriv f u * Real.cos (γ * u)) atTop (𝓝 0) := by
    refine (tendsto_integral_mul_cos (hf.integrableOn_deriv.integrable_indicator measurableSet_Ioi)).congr
      fun γ => ?_
    rw [← integral_indicator measurableSet_Ioi]
    congr 1; ext u
    by_cases hu : u ∈ Ioi (0 : ℝ) <;> simp [indicator, hu]
  have h := hRL.const_add (f 0)
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with γ hγ
  rw [hf.halfLineSine_eq_cos hγ.ne', halfLineCos]
  field_simp

theorem abs_halfLineSine_le (hf : CausalSource f) (γ : ℝ) :
    |halfLineSine f γ| ≤ ∫ u in Ioi (0 : ℝ), |f u| := by
  rw [halfLineSine, ← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans (setIntegral_mono_on
    (hf.integrableOn_mul_sin γ).norm hf.integrableOn_self.norm measurableSet_Ioi fun u _ => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)

/-- **Jet expansion.** `c_f(γ) = Σ_{j<m} (-1)^j f^{(2j)}(0)/γ^{2j+1} + (-1)^m c_{f^{(2m)}}(γ)/γ^{2m}`. -/
theorem halfLineSine_eq_jet (hf : CausalSource f) (m : ℕ) {γ : ℝ} (hγ : γ ≠ 0) :
    halfLineSine f γ = (∑ j ∈ Finset.range m,
        (-1) ^ j * _root_.iteratedDeriv (2 * j) f 0 / γ ^ (2 * j + 1)) +
      (-1) ^ m * halfLineSine (_root_.iteratedDeriv (2 * m) f) γ / γ ^ (2 * m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := (hf.iteratedDeriv (2 * m)).halfLineSine_eq_sub hγ
    rw [iteratedDeriv_iteratedDeriv, show 2 + 2 * m = 2 * (m + 1) by ring] at h
    rw [ih, Finset.sum_range_succ, h]
    field_simp
    ring

/-- If the even jets below `2m` vanish, `γ^{2m+1} c_f(γ) → (-1)^m f^{(2m)}(0)`. -/
theorem tendsto_pow_mul_halfLineSine (hf : CausalSource f) {m : ℕ}
    (hjets : ∀ j < m, _root_.iteratedDeriv (2 * j) f 0 = 0) :
    Tendsto (fun γ => γ ^ (2 * m + 1) * halfLineSine f γ) atTop
      (𝓝 ((-1) ^ m * _root_.iteratedDeriv (2 * m) f 0)) := by
  have h := ((hf.iteratedDeriv (2 * m)).tendsto_mul_halfLineSine).const_mul ((-1 : ℝ) ^ m)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with γ hγ
  rw [hf.halfLineSine_eq_jet m hγ.ne', Finset.sum_eq_zero fun j hj => by
    rw [hjets j (Finset.mem_range.mp hj)]; ring, zero_add]
  field_simp
  ring

/-- If the even jets below `2m` vanish, `|c_f(γ)| ≤ ‖f^{(2m)}‖₁/γ^{2m}`. -/
theorem abs_halfLineSine_le_of_jets (hf : CausalSource f) {m : ℕ}
    (hjets : ∀ j < m, _root_.iteratedDeriv (2 * j) f 0 = 0) {γ : ℝ} (hγ : 0 < γ) :
    |halfLineSine f γ| ≤ (∫ u in Ioi (0 : ℝ), |_root_.iteratedDeriv (2 * m) f u|) / γ ^ (2 * m) := by
  rw [hf.halfLineSine_eq_jet m hγ.ne', Finset.sum_eq_zero fun j hj => by
    rw [hjets j (Finset.mem_range.mp hj)]; ring, zero_add, abs_div, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow, one_mul, abs_of_pos (pow_pos hγ _)]
  exact div_le_div_of_nonneg_right ((hf.iteratedDeriv (2 * m)).abs_halfLineSine_le γ)
    (pow_pos hγ _).le

/-- **Fourier-scale classification (5a).** All even jets of `f` vanish at the cut iff its sine
transform decays faster than every power. -/
theorem even_jets_eq_zero_iff_rapid (hf : CausalSource f) :
    (∀ m, _root_.iteratedDeriv (2 * m) f 0 = 0) ↔
      ∀ N : ℕ, (halfLineSine f) =O[atTop] fun γ => (γ ^ N)⁻¹ := by
  constructor
  · intro h N
    refine Asymptotics.IsBigO.of_bound (∫ u in Ioi (0 : ℝ), |_root_.iteratedDeriv (2 * N) f u|) ?_
    filter_upwards [eventually_ge_atTop 1] with γ hγ
    have hγ0 : 0 < γ := by linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_pos (pow_pos hγ0 _)]
    refine (hf.abs_halfLineSine_le_of_jets (m := N) (fun j _ => h j) hγ0).trans ?_
    rw [div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left (inv_anti₀ (pow_pos hγ0 _) ?_) (integral_nonneg fun _ => abs_nonneg _)
    exact pow_le_pow_right₀ hγ (by omega)
  · intro h
    by_contra hne
    push Not at hne
    classical
    let m := Nat.find hne
    have hm : _root_.iteratedDeriv (2 * m) f 0 ≠ 0 := Nat.find_spec hne
    have hlow : ∀ j < m, _root_.iteratedDeriv (2 * j) f 0 = 0 := fun j hj => by
      by_contra hj'; exact Nat.find_min hne hj hj'
    have hlim := hf.tendsto_pow_mul_halfLineSine hlow
    -- `γ^{2m+1} c_f(γ) = O(1/γ)` tends to `0`
    have hzero : Tendsto (fun γ => γ ^ (2 * m + 1) * halfLineSine f γ) atTop (𝓝 0) := by
      have hO := (h (2 * m + 2)).const_mul_left 1
      have hO' : (fun γ => γ ^ (2 * m + 1) * halfLineSine f γ) =O[atTop] fun γ => γ⁻¹ := by
        have h1 := (Asymptotics.isBigO_refl (fun γ : ℝ => γ ^ (2 * m + 1)) atTop).mul (h (2 * m + 2))
        refine h1.trans (Asymptotics.IsBigO.of_bound 1 ?_)
        filter_upwards [eventually_gt_atTop 0] with γ hγ
        rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_pos hγ,
          abs_mul, abs_inv, abs_of_pos (pow_pos hγ _), abs_of_pos (pow_pos hγ _)]
        apply le_of_eq
        field_simp
        ring
      exact hO'.trans_tendsto tendsto_inv_atTop_zero
    have := tendsto_nhds_unique hlim hzero
    exact hm (by
      have h1 : ((-1 : ℝ) ^ m) ≠ 0 := pow_ne_zero _ (by norm_num)
      exact (mul_eq_zero.mp this).resolve_left h1)

/-- At the first nonzero even jet the sine transform has an eventual fixed sign. -/
theorem eventually_sign_halfLineSine (hf : CausalSource f) {m : ℕ}
    (hjets : ∀ j < m, _root_.iteratedDeriv (2 * j) f 0 = 0)
    (hm : _root_.iteratedDeriv (2 * m) f 0 ≠ 0) :
    ∀ᶠ γ in atTop, 0 < (-1) ^ m * _root_.iteratedDeriv (2 * m) f 0 * halfLineSine f γ := by
  set L := (-1) ^ m * _root_.iteratedDeriv (2 * m) f 0
  have hL : L ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) hm
  have h := (hf.tendsto_pow_mul_halfLineSine hjets).const_mul L
  have hpos : 0 < L * L := mul_self_pos.mpr hL
  filter_upwards [h.eventually (lt_mem_nhds hpos), eventually_gt_atTop 0] with γ hγ hγ0
  have hp : 0 < γ ^ (2 * m + 1) := pow_pos hγ0 _
  have : 0 < γ ^ (2 * m + 1) * (L * halfLineSine f γ) := by linarith [hγ]
  exact pos_of_mul_pos_right this hp.le

end CausalSource

/-- An analytic germ whose even jets all vanish is odd. -/
theorem eventually_neg_of_even_iteratedDeriv_eq_zero {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0)
    (heven : ∀ m, iteratedDeriv (2 * m) f 0 = 0) : ∀ᶠ u in 𝓝 0, f (-u) = -f u := by
  set g : ℝ → ℝ := fun u => f (-u) + f u
  have hneg : AnalyticAt ℝ (fun u => f (-u)) 0 := by
    have := hf.comp_of_eq ((analyticAt_id (𝕜 := ℝ) (z := (0 : ℝ))).neg) (by simp)
    simpa [Function.comp_def] using this
  have hg : AnalyticAt ℝ g 0 := hneg.add hf
  have hzero : ∀ n, iteratedDeriv n g 0 = 0 := by
    intro n
    have h1 := iteratedDeriv_comp_neg n f 0
    rw [show g = (fun u => f (-u)) + f from rfl, iteratedDeriv_add hneg.contDiffAt hf.contDiffAt,
      h1, neg_zero, smul_eq_mul]
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [show n = 2 * k by omega, heven k]; ring
    · rw [hk, pow_succ, pow_mul]; simp
  have htop : analyticOrderAt g 0 = ⊤ := by
    by_contra hfin
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
    have hle : ((m + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt g 0 := by
      rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hg]
      intro i _; exact hzero i
    rw [← hm] at hle
    have : (m + 1 : ℕ) ≤ m := by exact_mod_cast hle
    omega
  filter_upwards [analyticOrderAt_eq_top.mp htop] with u hu
  have : f (-u) + f u = 0 := hu
  linarith

end

end GaloisForLFunctions.HTGeometry
