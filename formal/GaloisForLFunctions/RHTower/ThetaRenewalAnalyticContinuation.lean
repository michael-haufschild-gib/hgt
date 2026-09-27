import GaloisForLFunctions.RHTower.ThetaRenewalLogKernel

/-!
# The real-analytic continuation of the renewal kernel

The increment continues holomorphically to the strip `|Im z| < π/2` as
`ν(z) = -e^{5z/4} Θ'(e^z)` (there `Re e^z > 0`).  The complex Volterra convolution
`(f ⋆ g)(z) = z ∫₀¹ f(z(1 - u)) g(zu) du` of functions holomorphic on a convex open set containing
`0` is holomorphic (differentiation under the integral), and on the real axis it is the oriented
real convolution.  On the closed boxes `|Re z| ≤ R`, `|Im z| ≤ π/4` the powers satisfy
`|ν^{⋆(m+1)}(z)| ≤ C^{m+1} |z|^m/m!`, so the series `Σ ν^{⋆m}/(m c^m)` converges uniformly and is
holomorphic on the open boxes.  Restricted to the real axis it is the kernel `Q` of the renewal
module, which is therefore real-analytic at every real point: the convolution series has a
real-analytic continuation along the whole real axis, namely the oriented series itself.
-/
open Complex Filter Topology Set MeasureTheory HurwitzZeta
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

local notation "Θ" => evenKernel (0 : UnitAddCircle)

/-! ## Complex Volterra convolution along segments -/

/-- The complex Volterra convolution `(f ⋆ g)(z) = z ∫₀¹ f(z(1 - u)) g(zu) du`. -/
def complexVolterraConv (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * ∫ u in (0 : ℝ)..1, f (z * (1 - u)) * g (z * u)

theorem mul_ofReal_mem_of_convex {U : Set ℂ} (hc : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {w : ℂ}
    (hw : w ∈ U) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : w * (s : ℂ) ∈ U := by
  have := hc h0 hw (a := 1 - s) (b := s) (by linarith [hs.2]) hs.1 (by ring)
  simpa [smul_eq_mul, Complex.real_smul, mul_comm] using this

/-- Holomorphy of the complex Volterra convolution on a convex open set containing `0`. -/
theorem differentiableOn_complexVolterraConv {U : Set ℂ} (hU : IsOpen U) (hc : Convex ℝ U)
    (h0 : (0 : ℂ) ∈ U) {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) :
    DifferentiableOn ℂ (complexVolterraConv f g) U := by
  intro z₀ hz₀
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  set r' := r / 2
  have hr' : 0 < r' := by positivity
  have hcb : Metric.closedBall z₀ r' ⊆ U :=
    (Metric.closedBall_subset_ball (by simp only [r']; linarith)).trans hball
  set K : Set ℂ := (fun p : ℂ × ℝ => p.1 * (p.2 : ℂ)) '' (Metric.closedBall z₀ r' ×ˢ Icc 0 1)
  have hK : IsCompact K := ((isCompact_closedBall z₀ r').prod isCompact_Icc).image (by fun_prop)
  have hKU : K ⊆ U := by
    rintro _ ⟨⟨w, s⟩, ⟨hw, hs⟩, rfl⟩
    exact mul_ofReal_mem_of_convex hc h0 (hcb hw) hs
  have hmem : ∀ z ∈ Metric.closedBall z₀ r', ∀ u ∈ Icc (0 : ℝ) 1,
      z * (1 - (u : ℂ)) ∈ K ∧ z * (u : ℂ) ∈ K := by
    intro z hz u hu
    refine ⟨⟨(z, 1 - u), ⟨hz, ⟨by linarith [hu.2], by linarith [hu.1]⟩⟩, by push_cast; ring⟩,
      ⟨(z, u), ⟨hz, hu⟩, rfl⟩⟩
  have hdf := hf.deriv hU
  have hdg := hg.deriv hU
  obtain ⟨M1, hM1⟩ := hK.exists_bound_of_continuousOn (hf.continuousOn.mono hKU)
  obtain ⟨M2, hM2⟩ := hK.exists_bound_of_continuousOn (hg.continuousOn.mono hKU)
  obtain ⟨M3, hM3⟩ := hK.exists_bound_of_continuousOn (hdf.continuousOn.mono hKU)
  obtain ⟨M4, hM4⟩ := hK.exists_bound_of_continuousOn (hdg.continuousOn.mono hKU)
  set μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  have hcontF : ∀ z ∈ Metric.closedBall z₀ r',
      ContinuousOn (fun u : ℝ => f (z * (1 - u)) * g (z * u)) (Icc 0 1) := by
    intro z hz
    refine ((hf.continuousOn.comp (by fun_prop) fun u hu => hKU (hmem z hz u hu).1).mul
      (hg.continuousOn.comp (by fun_prop) fun u hu => hKU (hmem z hz u hu).2))
  have hz₀c : z₀ ∈ Metric.closedBall z₀ r' := Metric.mem_closedBall_self hr'.le
  have hcontF' : ContinuousOn (fun u : ℝ => deriv f (z₀ * (1 - u)) * (1 - u) * g (z₀ * u) +
      f (z₀ * (1 - u)) * (deriv g (z₀ * u) * u)) (Icc 0 1) := by
    refine (((hdf.continuousOn.comp (by fun_prop) fun u hu => hKU (hmem z₀ hz₀c u hu).1).mul
      (by fun_prop)).mul (hg.continuousOn.comp (by fun_prop) fun u hu =>
        hKU (hmem z₀ hz₀c u hu).2)).add
      ((hf.continuousOn.comp (by fun_prop) fun u hu => hKU (hmem z₀ hz₀c u hu).1).mul
      ((hdg.continuousOn.comp (by fun_prop) fun u hu => hKU (hmem z₀ hz₀c u hu).2).mul
        (by fun_prop)))
  have hmeasF : ∀ z ∈ Metric.closedBall z₀ r',
      AEStronglyMeasurable (fun u : ℝ => f (z * (1 - u)) * g (z * u)) μ := fun z hz =>
    ((hcontF z hz).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hbound : ∀ᵐ (u : ℝ) ∂μ, ∀ z ∈ Metric.ball z₀ r',
      ‖deriv f (z * (1 - u)) * (1 - u) * g (z * u) + f (z * (1 - u)) * (deriv g (z * u) * u)‖ ≤
        M3 * M2 + M1 * M4 := by
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun u hu z hz => ?_)
    have hm := hmem z (Metric.ball_subset_closedBall hz) u ⟨hu.1.le, hu.2⟩
    have hu1 : ‖(1 : ℂ) - u‖ ≤ 1 := by
      rw [show (1 : ℂ) - u = ((1 - u : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_le]; constructor <;> linarith [hu.1, hu.2]
    have hu2 : ‖(u : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]; constructor <;> linarith [hu.1, hu.2]
    have hM3n : 0 ≤ M3 := (norm_nonneg _).trans (hM3 _ hm.1)
    have hM1n : 0 ≤ M1 := (norm_nonneg _).trans (hM1 _ hm.1)
    have hM4n : 0 ≤ M4 := (norm_nonneg _).trans (hM4 _ hm.2)
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, norm_mul]
      calc ‖deriv f (z * (1 - u))‖ * ‖1 - (u : ℂ)‖ * ‖g (z * u)‖ ≤ M3 * 1 * M2 :=
            mul_le_mul (mul_le_mul (hM3 _ hm.1) hu1 (norm_nonneg _) hM3n) (hM2 _ hm.2)
              (norm_nonneg _) (by positivity)
        _ = M3 * M2 := by ring
    · rw [norm_mul, norm_mul]
      calc ‖f (z * (1 - u))‖ * (‖deriv g (z * u)‖ * ‖(u : ℂ)‖) ≤ M1 * (M4 * 1) :=
            mul_le_mul (hM1 _ hm.1) (mul_le_mul (hM4 _ hm.2) hu2 (norm_nonneg _) hM4n)
              (by positivity) hM1n
        _ = M1 * M4 := by ring
  have hderiv : ∀ᵐ (u : ℝ) ∂μ, ∀ z ∈ Metric.ball z₀ r',
      HasDerivAt (fun z => f (z * (1 - u)) * g (z * u))
        (deriv f (z * (1 - u)) * (1 - u) * g (z * u) + f (z * (1 - u)) * (deriv g (z * u) * u)) z := by
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun u hu z hz => ?_)
    have hm := hmem z (Metric.ball_subset_closedBall hz) u ⟨hu.1.le, hu.2⟩
    have hd1 : HasDerivAt (fun z => f (z * (1 - u))) (deriv f (z * (1 - u)) * (1 - u)) z :=
      ((hf.differentiableAt (hU.mem_nhds (hKU hm.1))).hasDerivAt).comp z
        ((hasDerivAt_id z).mul_const (1 - (u : ℂ)) |>.congr_deriv (one_mul _))
    have hd2 : HasDerivAt (fun z => g (z * u)) (deriv g (z * u) * u) z :=
      ((hg.differentiableAt (hU.mem_nhds (hKU hm.2))).hasDerivAt).comp z
        ((hasDerivAt_id z).mul_const (u : ℂ) |>.congr_deriv (one_mul _))
    exact (hd1.mul hd2).congr_deriv (by ring)
  have hint0 : Integrable (fun u : ℝ => f (z₀ * (1 - u)) * g (z₀ * u)) μ := by
    refine (integrable_const (M1 * M2)).mono' (hmeasF z₀ hz₀c) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun u hu => ?_)
    have hm := hmem z₀ hz₀c u ⟨hu.1.le, hu.2⟩
    rw [norm_mul]
    exact mul_le_mul (hM1 _ hm.1) (hM2 _ hm.2) (norm_nonneg _) ((norm_nonneg _).trans (hM1 _ hm.1))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun z u => f (z * (1 - u)) * g (z * u))
    (F' := fun z u => deriv f (z * (1 - u)) * (1 - u) * g (z * u) +
      f (z * (1 - u)) * (deriv g (z * u) * u))
    (bound := fun _ => M3 * M2 + M1 * M4) (x₀ := z₀) (Metric.ball_mem_nhds z₀ hr')
    (Filter.eventually_of_mem (Metric.ball_mem_nhds z₀ hr') fun z hz =>
      hmeasF z (Metric.ball_subset_closedBall hz))
    hint0 (hcontF'.mono Ioc_subset_Icc_self |>.aestronglyMeasurable measurableSet_Ioc)
    hbound (integrable_const _) hderiv
  have hint : HasDerivAt (fun z => ∫ u in (0 : ℝ)..1, f (z * (1 - u)) * g (z * u))
      (∫ u, (deriv f (z₀ * (1 - u)) * (1 - u) * g (z₀ * u) +
        f (z₀ * (1 - u)) * (deriv g (z₀ * u) * u)) ∂μ) z₀ := by
    refine key.2.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
    simp only [μ]
    rw [intervalIntegral.integral_of_le zero_le_one]
  exact ((hasDerivAt_id z₀).mul hint).differentiableAt.differentiableWithinAt

/-- On the real axis the complex convolution is the oriented real one. -/
theorem complexVolterraConv_ofReal {f g : ℂ → ℂ} {f₀ g₀ : ℝ → ℝ}
    (hf : ∀ x : ℝ, f x = f₀ x) (hg : ∀ x : ℝ, g x = g₀ x) (t : ℝ) :
    complexVolterraConv f g t = (volterraConv f₀ g₀ t : ℂ) := by
  rw [complexVolterraConv, volterraConv]
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1)
    (fun s => ((f₀ (t - s) * g₀ s : ℝ) : ℂ)) ht
  simp only [mul_zero, mul_one] at h
  have hl : (∫ u in (0 : ℝ)..1, f (t * (1 - u)) * g (t * u)) =
      ∫ u in (0 : ℝ)..1, ((f₀ (t - t * u) * g₀ (t * u) : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [show (t : ℂ) * (1 - u) = ((t - t * u : ℝ) : ℂ) by push_cast; ring,
      show (t : ℂ) * u = ((t * u : ℝ) : ℂ) by push_cast; ring, hf, hg]
    push_cast; ring
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  rw [hl, h, intervalIntegral.integral_ofReal, Complex.real_smul]
  push_cast
  field_simp

/-! ## The complex increment on the strip `|Im z| < π/2` -/

/-- The strip `|Im z| < π/2`, where `Re e^z > 0`. -/
def thetaStrip : Set ℂ := {z | |z.im| < Real.pi / 2}

theorem isOpen_thetaStrip : IsOpen thetaStrip :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

theorem convex_thetaStrip : Convex ℝ thetaStrip := by
  intro x hx y hy a b ha hb hab
  simp only [thetaStrip, mem_setOf_eq] at hx hy ⊢
  simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
  calc |a * x.im + b * y.im| ≤ a * |x.im| + b * |y.im| := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ < Real.pi / 2 := by
        rcases eq_or_lt_of_le ha with rfl | ha'
        · simp at hab; subst hab; simpa using hy
        · have h1 := mul_lt_mul_of_pos_left hx ha'
          have h2 := mul_le_mul_of_nonneg_left hy.le hb
          have h3 : a * (Real.pi / 2) + b * (Real.pi / 2) = Real.pi / 2 := by
            rw [← add_mul, hab, one_mul]
          linarith

theorem zero_mem_thetaStrip : (0 : ℂ) ∈ thetaStrip := by
  simp [thetaStrip, Real.pi_pos]

theorem re_cexp_pos_of_mem_thetaStrip {z : ℂ} (hz : z ∈ thetaStrip) : 0 < (cexp z).re := by
  have hz' : |z.im| < Real.pi / 2 := hz
  rw [Complex.exp_re]
  refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩) <;>
    linarith [abs_lt.mp hz']

/-- The complex increment `ν(z) = -e^{5z/4} Θ'(e^z)`. -/
def thetaRenewalIncrementC (z : ℂ) : ℂ := -(cexp (5 / 4 * z) * jacobiThetaSumOne (cexp z))

theorem differentiableOn_thetaRenewalIncrementC : DifferentiableOn ℂ thetaRenewalIncrementC thetaStrip := by
  intro z hz
  have h := (hasDerivAt_jacobiThetaSumOne (re_cexp_pos_of_mem_thetaStrip hz)).comp z
    (Complex.hasDerivAt_exp z)
  exact ((((hasDerivAt_id z).const_mul (5 / 4 : ℂ)).cexp.mul h).neg).differentiableAt.differentiableWithinAt

theorem jacobiThetaSumOne_ofReal {y : ℝ} (hy : 0 < y) :
    jacobiThetaSumOne (y : ℂ) = ((-(2 * Real.pi * thetaMoment 1 y) : ℝ) : ℂ) := by
  have h1 : HasDerivAt (fun x : ℝ => jacobiThetaSum (x : ℂ)) (jacobiThetaSumOne y) y :=
    (hasDerivAt_jacobiThetaSum (by simpa using hy)).comp_ofReal
  have h2 : HasDerivAt (fun x : ℝ => ((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ))
      ((-(2 * Real.pi * thetaMoment 1 y) : ℝ) : ℂ) y :=
    (hasDerivAt_evenKernel_zero hy).ofReal_comp
  have heq : (fun x : ℝ => jacobiThetaSum (x : ℂ)) = fun x : ℝ => ((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ) :=
    funext jacobiThetaSum_ofReal_eq_evenKernel
  rw [heq] at h1
  exact h1.unique h2

theorem thetaRenewalIncrementC_ofReal (t : ℝ) :
    thetaRenewalIncrementC t = (thetaRenewalIncrement t : ℂ) := by
  rw [thetaRenewalIncrementC, ← Complex.ofReal_exp, jacobiThetaSumOne_ofReal (Real.exp_pos t),
    thetaRenewalIncrement]
  push_cast
  ring

/-! ## Holomorphic convolution powers and the holomorphic kernel -/

/-- The complex convolution powers of the increment. -/
def thetaRenewalPowerC : ℕ → ℂ → ℂ
  | 0 => thetaRenewalIncrementC
  | m + 1 => complexVolterraConv thetaRenewalIncrementC (thetaRenewalPowerC m)

theorem differentiableOn_thetaRenewalPowerC (m : ℕ) :
    DifferentiableOn ℂ (thetaRenewalPowerC m) thetaStrip := by
  induction m with
  | zero => exact differentiableOn_thetaRenewalIncrementC
  | succ m ih =>
    exact differentiableOn_complexVolterraConv isOpen_thetaStrip convex_thetaStrip
      zero_mem_thetaStrip differentiableOn_thetaRenewalIncrementC ih

theorem thetaRenewalPowerC_ofReal (m : ℕ) (t : ℝ) :
    thetaRenewalPowerC m t = (thetaRenewalPower m t : ℂ) := by
  induction m generalizing t with
  | zero => exact thetaRenewalIncrementC_ofReal t
  | succ m ih =>
    exact complexVolterraConv_ofReal thetaRenewalIncrementC_ofReal ih t

/-- The closed box `|Re z| ≤ R`, `|Im z| ≤ π/4`. -/
def thetaBox (R : ℝ) : Set ℂ := {z | |z.re| ≤ R ∧ |z.im| ≤ Real.pi / 4}

theorem isCompact_thetaBox (R : ℝ) : IsCompact (thetaBox R) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const).inter
      (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const)
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R + Real.pi / 4)).subset ?_
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (Complex.norm_le_abs_re_add_abs_im z).trans (add_le_add hz.1 hz.2)

theorem thetaBox_subset_thetaStrip (R : ℝ) : thetaBox R ⊆ thetaStrip := fun z hz => by
  show |z.im| < Real.pi / 2
  linarith [hz.2, Real.pi_pos]

theorem mul_ofReal_mem_thetaBox {R : ℝ} {z : ℂ} (hz : z ∈ thetaBox R) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : z * (s : ℂ) ∈ thetaBox R := by
  simp only [thetaBox, mem_setOf_eq, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, zero_add] at hz ⊢
  rw [abs_mul, abs_mul, abs_of_nonneg hs.1]
  constructor
  · nlinarith [hz.1, abs_nonneg z.re, hs.2]
  · nlinarith [hz.2, abs_nonneg z.im, hs.2]

theorem norm_le_of_mem_thetaBox {R : ℝ} {z : ℂ} (hz : z ∈ thetaBox R) : ‖z‖ ≤ R + 1 := by
  have := Complex.norm_le_abs_re_add_abs_im z
  have hpi : Real.pi / 4 < 1 := by linarith [Real.pi_lt_four]
  linarith [hz.1, hz.2]

/-- `|ν^{⋆(m+1)}(z)| ≤ C^{m+1} |z|^m/m!` on the box, where `|ν| ≤ C`. -/
theorem norm_thetaRenewalPowerC_le {R C : ℝ}
    (hC : ∀ w ∈ thetaBox R, ‖thetaRenewalIncrementC w‖ ≤ C) (m : ℕ) {z : ℂ} (hz : z ∈ thetaBox R) :
    ‖thetaRenewalPowerC m z‖ ≤ C ^ (m + 1) * ‖z‖ ^ m / m.factorial := by
  induction m generalizing z with
  | zero => simpa [thetaRenewalPowerC] using hC z hz
  | succ m ih =>
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC z hz)
    simp only [thetaRenewalPowerC, complexVolterraConv]
    rw [norm_mul]
    have hbound : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Ioc (0 : ℝ) 1 →
        ‖thetaRenewalIncrementC (z * (1 - u)) * thetaRenewalPowerC m (z * u)‖ ≤
          C * (C ^ (m + 1) * ‖z‖ ^ m * u ^ m / m.factorial) := by
      refine Eventually.of_forall fun u hu => ?_
      have h1 : z * (1 - (u : ℂ)) ∈ thetaBox R := by
        have := mul_ofReal_mem_thetaBox hz (s := 1 - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩
        simpa using this
      have h2 := mul_ofReal_mem_thetaBox hz (s := u) ⟨hu.1.le, hu.2⟩
      rw [norm_mul]
      have h3 := ih h2
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu.1, mul_pow] at h3
      exact mul_le_mul (hC _ h1) (h3.trans (le_of_eq (by ring))) (norm_nonneg _) hC0
    have hint := intervalIntegral.norm_integral_le_of_norm_le zero_le_one hbound
      ((by fun_prop : Continuous fun u : ℝ => C * (C ^ (m + 1) * ‖z‖ ^ m * u ^ m /
        m.factorial)).intervalIntegrable _ _)
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
      intervalIntegral.integral_const_mul, integral_pow] at hint
    calc ‖z‖ * ‖∫ u in (0 : ℝ)..1, thetaRenewalIncrementC (z * (1 - u)) *
          thetaRenewalPowerC m (z * u)‖
        ≤ ‖z‖ * (C * (C ^ (m + 1) * ‖z‖ ^ m * ((1 ^ (m + 1) - 0 ^ (m + 1)) / (m + 1)) /
          m.factorial)) := mul_le_mul_of_nonneg_left hint (norm_nonneg _)
      _ = C ^ (m + 1 + 1) * ‖z‖ ^ (m + 1) / (m + 1).factorial := by
          rw [Nat.factorial_succ]; push_cast; simp; field_simp; ring

/-- The holomorphic logarithmic kernel on the strip. -/
def thetaRenewalLogKernelC (z : ℂ) : ℂ :=
  ∑' m : ℕ, thetaRenewalPowerC m z / ((m + 1) * (Θ 1 : ℂ) ^ (m + 1))

theorem thetaRenewalLogKernelC_ofReal (t : ℝ) :
    thetaRenewalLogKernelC t = (thetaRenewalLogKernel t : ℂ) := by
  rw [thetaRenewalLogKernelC, thetaRenewalLogKernel, Complex.ofReal_tsum]
  refine tsum_congr fun m => ?_
  rw [thetaRenewalPowerC_ofReal]; push_cast; ring

/-- The open box `|Re z| < R`, `|Im z| < π/4`. -/
def thetaOpenBox (R : ℝ) : Set ℂ := {z | |z.re| < R ∧ |z.im| < Real.pi / 4}

theorem isOpen_thetaOpenBox (R : ℝ) : IsOpen (thetaOpenBox R) :=
  (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const).inter
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)

theorem differentiableOn_thetaRenewalLogKernelC (R : ℝ) :
    DifferentiableOn ℂ thetaRenewalLogKernelC (thetaOpenBox R) := by
  have hc := thetaSeam_pos
  obtain ⟨C, hC⟩ := (isCompact_thetaBox R).exists_bound_of_continuousOn
    (differentiableOn_thetaRenewalIncrementC.continuousOn.mono (thetaBox_subset_thetaStrip R))
  have hsub : thetaOpenBox R ⊆ thetaBox R := fun z hz => ⟨hz.1.le, hz.2.le⟩
  refine Complex.differentiableOn_tsum_of_summable_norm
    (u := fun m : ℕ => C / Θ 1 * ((C / Θ 1 * (R + 1)) ^ m / m.factorial))
    ((Real.summable_pow_div_factorial _).mul_left _)
    (fun m => ((differentiableOn_thetaRenewalPowerC m).mono
      ((hsub.trans (thetaBox_subset_thetaStrip R)))).div_const _)
    (isOpen_thetaOpenBox R) fun m z hz => ?_
  have hzb := hsub hz
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨by simp; linarith [abs_nonneg z.re, hzb.1],
    by simp; positivity⟩)
  have h1 := norm_thetaRenewalPowerC_le hC m hzb
  have h2 := norm_le_of_mem_thetaBox hzb
  rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc,
    show ‖((m : ℂ) + 1)‖ = (m : ℝ) + 1 by
      rw [show ((m : ℂ) + 1) = (((m : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]]
  rw [div_le_iff₀ (by positivity)]
  have hm : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hz' : ‖z‖ ^ m ≤ (R + 1) ^ m := pow_le_pow_left₀ (norm_nonneg _) h2 m
  calc ‖thetaRenewalPowerC m z‖ ≤ C ^ (m + 1) * ‖z‖ ^ m / m.factorial := h1
    _ ≤ C ^ (m + 1) * (R + 1) ^ m / m.factorial := by gcongr
    _ ≤ C / Θ 1 * ((C / Θ 1 * (R + 1)) ^ m / m.factorial) * (((m : ℝ) + 1) * Θ 1 ^ (m + 1)) := by
        have e : C / Θ 1 * ((C / Θ 1 * (R + 1)) ^ m / m.factorial) * (((m : ℝ) + 1) * Θ 1 ^ (m + 1)) =
            ((m : ℝ) + 1) * (C ^ (m + 1) * (R + 1) ^ m / m.factorial) := by
          rw [mul_pow, div_pow]; field_simp; ring
        rw [e]
        have : 0 ≤ C ^ (m + 1) * (R + 1) ^ m / m.factorial := by
          have hR : 0 ≤ R + 1 := le_trans (norm_nonneg _) h2
          positivity
        nlinarith

/-- **Real-analytic continuation.** The convolution series `Q`, continued to the whole real axis
by oriented convolutions, is real-analytic at every real point. -/
theorem analyticAt_thetaRenewalLogKernel (t : ℝ) : AnalyticAt ℝ thetaRenewalLogKernel t := by
  have hopen : thetaOpenBox (|t| + 1) ∈ 𝓝 (t : ℂ) := by
    refine (isOpen_thetaOpenBox _).mem_nhds ⟨?_, ?_⟩
    · simp only [Complex.ofReal_re]; linarith
    · simp only [Complex.ofReal_im, abs_zero]; positivity
  have hC : AnalyticAt ℂ thetaRenewalLogKernelC (t : ℂ) :=
    (differentiableOn_thetaRenewalLogKernelC _).analyticAt hopen
  have hR : AnalyticAt ℝ thetaRenewalLogKernelC (t : ℂ) := hC.restrictScalars
  have hcomp : AnalyticAt ℝ (fun x : ℝ => (thetaRenewalLogKernelC (x : ℂ)).re) t :=
    (Complex.reCLM.analyticAt _).comp (hR.comp (Complex.ofRealCLM.analyticAt t))
  refine hcomp.congr (Eventually.of_forall fun x => ?_)
  simp only [thetaRenewalLogKernelC_ofReal, Complex.ofReal_re]

end RHTower
