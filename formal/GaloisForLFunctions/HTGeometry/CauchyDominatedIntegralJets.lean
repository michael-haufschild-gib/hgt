import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# All-order jets of dominated holomorphic integrals

Uniform strip bounds control every parameter derivative by Cauchy estimates.
Each derivative is the literal integral of the source jet. Exponential decay
on a strip also places the real restriction in Schwartz space.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped SchwartzMap
namespace GaloisForLFunctions.HTGeometry
noncomputable section

private theorem abs_im_le_add_radius {z w : ℂ} {r : ℝ} (h : ‖w - z‖ ≤ r) :
    |w.im| ≤ |z.im| + r := by
  have hi := (Complex.abs_im_le_norm (w - z)).trans h
  rw [Complex.sub_im] at hi
  calc
    |w.im| = |(w.im - z.im) + z.im| := by congr 1; ring
    _ ≤ |w.im - z.im| + |z.im| := abs_add_le _ _
    _ ≤ _ := by linarith only [hi]

/-- Cauchy estimates bound every jet uniformly on a smaller horizontal strip. -/
theorem norm_iteratedDeriv_le_of_strip_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {δ ε B : ℝ} (hε : ε < δ) (hb : ∀ z : ℂ, |z.im| ≤ δ → ‖f z‖ ≤ B)
    (n : ℕ) {z : ℂ} (hz : |z.im| ≤ ε) :
    ‖iteratedDeriv n f z‖ ≤ ((n.factorial : ℝ) / (δ - ε) ^ n) * B := by
  have hr : 0 < δ - ε := sub_pos.mpr hε
  have hc : ∀ w ∈ sphere z (δ - ε), ‖f w‖ ≤ B := by
    intro w hw
    have hn : ‖w - z‖ ≤ δ - ε := by
      simpa only [dist_eq_norm] using (mem_sphere.mp hw).le
    apply hb
    have hi := abs_im_le_add_radius hn
    linarith only [hi, hz]
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr
    (hf.differentiableOn.diffContOnCl_ball (subset_univ _)) hc
  convert h using 1; ring

/-- Measurability passes to every parameter jet of an entire family. -/
theorem aestronglyMeasurable_iteratedDeriv_entire_family
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {F : α → ℂ → ℂ}
    (hf : ∀ a, Differentiable ℂ (F a))
    (hm : ∀ z, AEStronglyMeasurable (fun a => F a z) μ) (n : ℕ) (z : ℂ) :
    AEStronglyMeasurable (fun a => iteratedDeriv n (F a) z) μ := by
  induction n generalizing z with
  | zero => exact hm z
  | succ n ih =>
    simp only [iteratedDeriv_succ]
    apply aestronglyMeasurable_deriv_param_complex (by norm_num : (0 : ℝ) < 1)
      (fun w _ => ih w)
    intro a
    exact ((hf a).contDiff.differentiable_iteratedDeriv' n) z

/-- Every jet of a dominated entire family is integrable inside its domination strip. -/
theorem integrable_iteratedDeriv_of_strip_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {F : α → ℂ → ℂ}
    (hf : ∀ a, Differentiable ℂ (F a))
    (hm : ∀ z, AEStronglyMeasurable (fun a => F a z) μ)
    {δ : ℝ} {B : α → ℝ} (hB : Integrable B μ)
    (hb : ∀ a z, |z.im| ≤ δ → ‖F a z‖ ≤ B a)
    (n : ℕ) {z : ℂ} (hz : |z.im| < δ) :
    Integrable (fun a => iteratedDeriv n (F a) z) μ := by
  refine (hB.const_mul ((n.factorial : ℝ) / (δ - |z.im|) ^ n)).mono'
    (aestronglyMeasurable_iteratedDeriv_entire_family hf hm n z) ?_
  filter_upwards with a
  exact norm_iteratedDeriv_le_of_strip_bound (hf a) hz (hb a) n le_rfl

/-- Uniform Cauchy bounds justify differentiating each jet integral. -/
theorem hasDerivAt_integral_iteratedDeriv_of_strip_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {F : α → ℂ → ℂ}
    (hf : ∀ a, Differentiable ℂ (F a))
    (hm : ∀ z, AEStronglyMeasurable (fun a => F a z) μ)
    {δ : ℝ} {B : α → ℝ} (hB : Integrable B μ)
    (hb : ∀ a z, |z.im| ≤ δ → ‖F a z‖ ≤ B a)
    (n : ℕ) {z : ℂ} (hz : |z.im| < δ) :
    HasDerivAt (fun w => ∫ a, iteratedDeriv n (F a) w ∂μ)
      (∫ a, iteratedDeriv (n + 1) (F a) z ∂μ) z := by
  let r := (δ - |z.im|) / 2
  let ε := |z.im| + r
  have hr : 0 < r := by dsimp [r]; linarith only [hz]
  have hε : ε < δ := by dsimp [ε, r]; linarith only [hz]
  have hlocal (w : ℂ) (hw : w ∈ ball z r) : |w.im| ≤ ε := by
    have hn : ‖w - z‖ ≤ r := by
      simpa only [dist_eq_norm] using (mem_ball.mp hw).le
    exact abs_im_le_add_radius hn
  have hi := integrable_iteratedDeriv_of_strip_bound hf hm hB hb n hz
  have hdm := aestronglyMeasurable_iteratedDeriv_entire_family hf hm (n + 1) z
  have hdom : ∀ᵐ a ∂μ, ∀ w ∈ ball z r,
      ‖iteratedDeriv (n + 1) (F a) w‖ ≤
        (((n + 1).factorial : ℝ) / (δ - ε) ^ (n + 1)) * B a := by
    filter_upwards with a
    intro w hw
    exact norm_iteratedDeriv_le_of_strip_bound (hf a) hε (hb a) (n + 1) (hlocal w hw)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w a => iteratedDeriv n (F a) w)
    (F' := fun w a => iteratedDeriv (n + 1) (F a) w)
    (bound := fun a => (((n + 1).factorial : ℝ) / (δ - ε) ^ (n + 1)) * B a)
    (ball_mem_nhds z hr)
    (Eventually.of_forall fun w => aestronglyMeasurable_iteratedDeriv_entire_family hf hm n w)
    hi hdm hdom (hB.const_mul _) ?_).2
  filter_upwards with a
  intro w hw
  simpa only [iteratedDeriv_succ] using
    ((hf a).contDiff.differentiable_iteratedDeriv' n w).hasDerivAt

/-- Every derivative of a dominated holomorphic integral is its literal integral jet. -/
theorem iteratedDeriv_integral_of_strip_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {F : α → ℂ → ℂ}
    (hf : ∀ a, Differentiable ℂ (F a))
    (hm : ∀ z, AEStronglyMeasurable (fun a => F a z) μ)
    {δ : ℝ} {B : α → ℝ} (hB : Integrable B μ)
    (hb : ∀ a z, |z.im| ≤ δ → ‖F a z‖ ≤ B a)
    (n : ℕ) {z : ℂ} (hz : |z.im| < δ) :
    iteratedDeriv n (fun w => ∫ a, F a w ∂μ) z =
      ∫ a, iteratedDeriv n (F a) z ∂μ := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hop : IsOpen {w : ℂ | |w.im| < δ} :=
      isOpen_lt Complex.continuous_im.abs continuous_const
    have he : iteratedDeriv n (fun w => ∫ a, F a w ∂μ) =ᶠ[𝓝 z]
        (fun w => ∫ a, iteratedDeriv n (F a) w ∂μ) := by
      filter_upwards [hop.mem_nhds hz] with w hw
      exact ih hw
    rw [he.deriv_eq]
    exact (hasDerivAt_integral_iteratedDeriv_of_strip_bound hf hm hB hb n hz).deriv

private theorem analyticAt_iteratedDeriv_on_strip {f : ℂ → ℂ} {δ : ℝ}
    (hf : ∀ z : ℂ, |z.im| < δ → DifferentiableAt ℂ f z)
    (n : ℕ) {z : ℂ} (hz : |z.im| < δ) : AnalyticAt ℂ (iteratedDeriv n f) z := by
  induction n with
  | zero =>
    have hd : DifferentiableOn ℂ f {w : ℂ | |w.im| < δ} :=
      fun w hw => (hf w hw).differentiableWithinAt
    exact hd.analyticOnNhd (isOpen_lt Complex.continuous_im.abs continuous_const) z hz
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv

/-- Real derivatives of a holomorphic strip restriction are its actual complex derivatives. -/
theorem iteratedDeriv_ofReal_on_strip {f : ℂ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hf : ∀ z : ℂ, |z.im| < δ → DifferentiableAt ℂ f z) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun t : ℝ => f (t : ℂ)) x = iteratedDeriv n f (x : ℂ) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, funext ih]
    have hx : |(x : ℂ).im| < δ := by simpa only [Complex.ofReal_im, abs_zero] using hδ
    have hd := (analyticAt_iteratedDeriv_on_strip hf n hx).differentiableAt.hasDerivAt
    simpa only [iteratedDeriv_succ] using hd.comp_ofReal.deriv

/-- A holomorphic function with strip exponential decay restricts to a Schwartz function. -/
def schwartzOfStripDecay (f : ℂ → ℂ) {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (hf : ∀ z : ℂ, |z.im| < 2 * δ → DifferentiableAt ℂ f z)
    (hb : ∀ z : ℂ, |z.im| ≤ δ → ‖f z‖ ≤ C * Real.exp (-|z.re|)) :
    SchwartzMap ℝ ℂ where
  toFun := fun x => f (x : ℂ)
  smooth' := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    have hx : |(x : ℂ).im| < 2 * δ := by simp only [Complex.ofReal_im, abs_zero]; positivity
    have ha := analyticAt_iteratedDeriv_on_strip hf 0 hx
    exact (ha.contDiffAt.restrict_scalars ℝ).comp x Complex.ofRealCLM.contDiff.contDiffAt
  decay' k n := by
    let D : ℝ := (n.factorial : ℝ) * (C * Real.exp δ) / δ ^ n
    have hD : 0 ≤ D := by dsimp [D]; positivity
    refine ⟨D * (k.factorial : ℝ), ?_⟩
    intro x
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      iteratedDeriv_ofReal_on_strip (by positivity : 0 < 2 * δ) hf,
      Real.norm_eq_abs]
    have hball : DifferentiableOn ℂ f (closedBall (x : ℂ) δ) := by
      intro z hz
      have hn : ‖z - (x : ℂ)‖ ≤ δ := by
        simpa only [dist_eq_norm] using mem_closedBall.mp hz
      have hi := abs_im_le_add_radius hn
      simp only [Complex.ofReal_im, abs_zero, zero_add] at hi
      exact (hf z (by linarith only [hi, hδ])).differentiableWithinAt
    have hs : ∀ z ∈ sphere (x : ℂ) δ,
        ‖f z‖ ≤ (C * Real.exp δ) * Real.exp (-|x|) := by
      intro z hz
      have hn : ‖z - (x : ℂ)‖ ≤ δ := by
        simpa only [dist_eq_norm] using (mem_sphere.mp hz).le
      have hi := abs_im_le_add_radius hn
      simp only [Complex.ofReal_im, abs_zero, zero_add] at hi
      have hr := (Complex.abs_re_le_norm (z - (x : ℂ))).trans hn
      simp only [Complex.sub_re, Complex.ofReal_re] at hr
      have hx : |x| ≤ |z.re| + δ := by
        calc
          |x| = |z.re + (x - z.re)| := by congr 1; ring
          _ ≤ |z.re| + |x - z.re| := abs_add_le _ _
          _ ≤ _ := by rw [abs_sub_comm]; linarith only [hr]
      have he : Real.exp (-|z.re|) ≤ Real.exp δ * Real.exp (-|x|) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith only [hx])
      calc
        ‖f z‖ ≤ C * Real.exp (-|z.re|) := hb z hi
        _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left he hC]
    have hj := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hδ
      (hball.diffContOnCl_ball (by exact subset_rfl)) hs
    have hj' : ‖iteratedDeriv n f (x : ℂ)‖ ≤ D * Real.exp (-|x|) := by
      convert hj using 1; dsimp only [D]; ring
    have hfact := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) k
    have hfacpos : (0 : ℝ) < k.factorial := by positivity
    rw [div_le_iff₀ hfacpos] at hfact
    have hpay : |x| ^ k * Real.exp (-|x|) ≤ k.factorial := by
      have hh := mul_le_mul_of_nonneg_right hfact (Real.exp_pos (-|x|)).le
      rw [mul_right_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at hh
      exact hh
    calc
      _ ≤ |x| ^ k * (D * Real.exp (-|x|)) :=
        mul_le_mul_of_nonneg_left hj' (pow_nonneg (abs_nonneg x) k)
      _ = D * (|x| ^ k * Real.exp (-|x|)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpay hD


end
end GaloisForLFunctions.HTGeometry
