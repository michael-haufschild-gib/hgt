import GaloisForLFunctions.RHTower.WeightedScrewLandauEngine

/-!
# The weighted Widder–Landau engine with an exponential slack

The weighted Widder–Landau engine assumes that the weighted screw divisor `Φ_W` is nonnegative on the
source half-line and concludes that its Laplace transform is analytic on `Re s > 0`.  Here the
hypothesis is weakened to an exponential lower bound `Φ_W(t) ≥ −C₀ e^{εt}` with `0 ≤ ε < 1/2`: the
shifted divisor `Φ_W(t) + C₀ e^{εt}` is nonnegative, its Laplace transform is the weighted atom series
plus the single real pole `C₀/(s − ε)`, and the halving argument descends the abscissa of exponential
moments from `1/2` towards `ε` instead of `0`.  Conclusion: the Laplace transform of the shifted
divisor is analytic on `Re s > ε` and agrees there with `Σ'_q W_q/(s(s² + γ_q²)) + C₀/(s − ε)`
wherever the latter converges.
-/

open Complex MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

variable (W : XiZeroCopy → ℂ) (C₀ ε : ℝ)

/-! ## The shifted divisor -/

/-- `Φ_W(t) + C₀ e^{εt}`. -/
def thrDivisor (t : ℝ) : ℂ :=
  weightedXiScrewDivisor W t + ((C₀ * Real.exp (ε * t) : ℝ) : ℂ)

theorem thrDivisor_re (t : ℝ) :
    (thrDivisor W C₀ ε t).re = (weightedXiScrewDivisor W t).re + C₀ * Real.exp (ε * t) := by
  unfold thrDivisor
  rw [Complex.add_re, Complex.ofReal_re]

theorem thrDivisor_im (hreal : ∀ t : ℝ, (weightedXiScrewDivisor W t).im = 0) (t : ℝ) :
    (thrDivisor W C₀ ε t).im = 0 := by
  unfold thrDivisor
  rw [Complex.add_im, Complex.ofReal_im, hreal t, add_zero]

theorem measurable_thrDivisor : Measurable (thrDivisor W C₀ ε) := by
  unfold thrDivisor
  exact (measurable_weightedXiScrewDivisor W).add (by fun_prop)

/-- `e^{−rt} · Re(Φ_W(t) + C₀ e^{εt})`. -/
def thrDensity (r t : ℝ) : ℝ :=
  Real.exp (-r * t) * (thrDivisor W C₀ ε t).re

theorem measurable_thrDensity (r : ℝ) : Measurable (thrDensity W C₀ ε r) := by
  unfold thrDensity
  exact (by fun_prop : Measurable (fun t : ℝ => Real.exp (-r * t))).mul
    (measurable_thrDivisor W C₀ ε).re

theorem thrDensity_nonneg_ae
    (hlow : ∀ t : ℝ, 0 ≤ t → -(C₀ * Real.exp (ε * t)) ≤ (weightedXiScrewDivisor W t).re) (r : ℝ) :
    ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ thrDensity W C₀ ε r t := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  unfold thrDensity
  rw [thrDivisor_re]
  have := hlow t ht.le
  exact mul_nonneg (Real.exp_pos _).le (by linarith)

theorem thrDensity_eq (r t : ℝ) :
    thrDensity W C₀ ε r t
      = weightedScrewLandauDensity W r t + C₀ * Real.exp ((ε - r) * t) := by
  unfold thrDensity weightedScrewLandauDensity
  rw [thrDivisor_re, show (ε - r) * t = -r * t + ε * t by ring, Real.exp_add]
  ring

theorem integrableOn_thrDensity {C : ℝ} (hC : 0 ≤ C) (hW : ∀ q, ‖W q‖ ≤ C) (hε : ε < 1 / 2)
    {r : ℝ} (hr : 1 / 2 < r) :
    IntegrableOn (thrDensity W C₀ ε r) (Ioi 0) := by
  have h1 := integrableOn_weightedScrewLandauDensity W hC hW hr
  have h2 : IntegrableOn (fun t : ℝ => C₀ * Real.exp ((ε - r) * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul C₀
  refine (h1.add h2).congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply]
  rw [thrDensity_eq]

/-! ## The Landau measure and exponential moments -/

/-- The positive Landau measure of the shifted divisor. -/
def thrMeasure (r : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity
    (fun t => ENNReal.ofReal (thrDensity W C₀ ε r t))

/-- Exponential integrability above an abscissa. -/
def ThrMomentsAbove (b : ℝ) : Prop :=
  ∀ r : ℝ, b < r → IntegrableOn (thrDensity W C₀ ε r) (Ioi 0)

theorem thrMomentsAbove_one_half {C : ℝ} (hC : 0 ≤ C) (hW : ∀ q, ‖W q‖ ≤ C) (hε : ε < 1 / 2) :
    ThrMomentsAbove W C₀ ε (1 / 2) := by
  intro r hr
  exact integrableOn_thrDensity W C₀ ε hC hW hε hr

theorem integrable_exp_mul_id_thrMeasure_of_momentsAbove
    (hlow : ∀ t : ℝ, 0 ≤ t → -(C₀ * Real.exp (ε * t)) ≤ (weightedXiScrewDivisor W t).re)
    {b r rho : ℝ} (hMom : ThrMomentsAbove W C₀ ε b) (hr : b < r - rho) :
    Integrable (fun t : ℝ => Real.exp (rho * id t)) (thrMeasure W C₀ ε r) := by
  have hdens := hMom (r - rho) hr
  have hmeas : AEMeasurable
      (fun t => ENNReal.ofReal (thrDensity W C₀ ε r t))
      (volume.restrict (Ioi 0)) :=
    (measurable_thrDensity W C₀ ε r).ennreal_ofReal.aemeasurable.restrict
  have hnonneg := thrDensity_nonneg_ae W C₀ ε hlow r
  rw [thrMeasure,
    integrable_withDensity_iff_integrable_smul₀' hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply hdens.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hnonneg] with t ht hden
  rw [ENNReal.toReal_ofReal hden]
  simp only [id_eq, smul_eq_mul]
  unfold thrDensity
  rw [show -(r - rho) * t = -r * t + rho * t by ring, Real.exp_add]
  ring

theorem zero_mem_interior_integrableExpSet_thrMeasure
    (hlow : ∀ t : ℝ, 0 ≤ t → -(C₀ * Real.exp (ε * t)) ≤ (weightedXiScrewDivisor W t).re)
    {b r : ℝ} (hMom : ThrMomentsAbove W C₀ ε b) (hr : b < r) :
    0 ∈ interior (integrableExpSet id (thrMeasure W C₀ ε r)) := by
  let delta : ℝ := (r - b) / 2
  have hdelta : 0 < delta := by dsimp only [delta]; linarith
  rw [mem_interior_iff_mem_nhds]
  refine mem_of_superset
    (Ioo_mem_nhds (a := -delta) (b := delta) (by linarith) (by linarith)) ?_
  intro rho hrho
  exact integrable_exp_mul_id_thrMeasure_of_momentsAbove W C₀ ε hlow hMom (by
    dsimp only [delta] at hrho
    linarith [hrho.2])

/-! ## The Laplace transform and its continuation -/

/-- `∫₀^∞ e^{−st} (Φ_W(t) + C₀ e^{εt}) dt`. -/
def thrLaplace (s : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, Complex.exp (-s * (t : ℂ)) * thrDivisor W C₀ ε t

/-- The weighted atom series plus the real pole `C₀/(s − ε)`. -/
def thrContinuation (s : ℂ) : ℂ :=
  weightedScrewLaplaceContinuation W s + (C₀ : ℂ) / (s - (ε : ℂ))

theorem complexMGF_id_thrMeasure_eq_laplace
    (hlow : ∀ t : ℝ, 0 ≤ t → -(C₀ * Real.exp (ε * t)) ≤ (weightedXiScrewDivisor W t).re)
    (hreal : ∀ t : ℝ, (weightedXiScrewDivisor W t).im = 0) (r : ℝ) (z : ℂ) :
    complexMGF id (thrMeasure W C₀ ε r) z = thrLaplace W C₀ ε ((r : ℂ) - z) := by
  have hmeas : AEMeasurable
      (fun t => ENNReal.ofReal (thrDensity W C₀ ε r t))
      (volume.restrict (Ioi 0)) :=
    (measurable_thrDensity W C₀ ε r).ennreal_ofReal.aemeasurable.restrict
  have hnonneg := thrDensity_nonneg_ae W C₀ ε hlow r
  rw [complexMGF, thrMeasure,
    integral_withDensity_eq_integral_toReal_smul₀ hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  unfold thrLaplace
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hnonneg] with t _ hden
  rw [ENNReal.toReal_ofReal hden, Complex.real_smul]
  simp only [id_eq]
  unfold thrDensity
  have hcast : ((thrDivisor W C₀ ε t).re : ℂ) = thrDivisor W C₀ ε t := by
    apply Complex.ext
    · simp
    · simp [thrDivisor_im W C₀ ε hreal t]
  push_cast
  rw [hcast]
  rw [show Complex.exp (-(r : ℂ) * (t : ℂ)) * thrDivisor W C₀ ε t *
      Complex.exp (z * (t : ℂ)) =
      (Complex.exp (-(r : ℂ) * (t : ℂ)) * Complex.exp (z * (t : ℂ))) *
        thrDivisor W C₀ ε t by ring]
  rw [← Complex.exp_add]
  congr 1
  ring

theorem analyticOnNhd_thrLaplace_of_momentsAbove
    (hlow : ∀ t : ℝ, 0 ≤ t → -(C₀ * Real.exp (ε * t)) ≤ (weightedXiScrewDivisor W t).re)
    (hreal : ∀ t : ℝ, (weightedXiScrewDivisor W t).im = 0)
    {b : ℝ} (hMom : ThrMomentsAbove W C₀ ε b) :
    AnalyticOnNhd ℂ (thrLaplace W C₀ ε) {s : ℂ | b < s.re} := by
  intro s hs
  let r : ℝ := s.re
  let z : ℂ := (r : ℂ) - s
  have hzero := zero_mem_interior_integrableExpSet_thrMeasure W C₀ ε hlow hMom
    (show b < r from hs)
  have hzre : z.re = 0 := by dsimp only [z, r]; simp
  have hmgf : AnalyticAt ℂ (complexMGF id (thrMeasure W C₀ ε r)) z :=
    analyticAt_complexMGF (by simpa only [hzre] using hzero)
  have hmgf' : AnalyticAt ℂ (complexMGF id (thrMeasure W C₀ ε r)) ((r : ℂ) - s) := by
    simpa only [z] using hmgf
  have haffine : AnalyticAt ℂ (fun w : ℂ => (r : ℂ) - w) s := by fun_prop
  have hcomp := hmgf'.comp haffine
  have heq : (fun w : ℂ => complexMGF id (thrMeasure W C₀ ε r) ((r : ℂ) - w)) =
      thrLaplace W C₀ ε := by
    funext w
    exact complexMGF_id_thrMeasure_eq_laplace W C₀ ε hlow hreal r ((r : ℂ) - w) |>.trans
      (by congr 1; ring)
  rw [← heq]
  exact hcomp

/-! ## The Laplace transform of the exponential slack -/

theorem hasDerivAt_cexp_mul' (c : ℂ) (s : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (c * (y : ℂ))) (Complex.exp (c * (s : ℂ)) * c) s := by
  have hz : HasDerivAt (fun z : ℂ => c * z) c (s : ℂ) := by
    simpa using (hasDerivAt_id (s : ℂ)).const_mul c
  exact ((Complex.hasDerivAt_exp _).comp (s : ℂ) hz).comp_ofReal

theorem integrableOn_cexp_mul_Ioi {c : ℂ} (hc : c.re < 0) :
    IntegrableOn (fun t : ℝ => Complex.exp (c * (t : ℂ))) (Ioi 0) := by
  have hbound : IntegrableOn (fun t : ℝ => Real.exp (c.re * t)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi hc 0
  refine Integrable.mono' hbound ?_ ?_
  · exact (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
      |>.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t => ?_
    rw [Complex.norm_exp]
    apply le_of_eq
    congr 1
    simp [Complex.mul_re]

/-- `∫₀^∞ e^{−st} e^{εt} dt = 1/(s − ε)` for `Re s > ε`. -/
theorem integral_Ioi_cexp_neg_mul_exp {s : ℂ} (hs : ε < s.re) :
    ∫ t : ℝ in Ioi 0, Complex.exp (-s * (t : ℂ)) * ((Real.exp (ε * t) : ℝ) : ℂ)
      = 1 / (s - (ε : ℂ)) := by
  set c : ℂ := (ε : ℂ) - s with hcdef
  have hcre : c.re < 0 := by simp [hcdef]; linarith
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hcre
    exact lt_irrefl _ hcre
  have hfun : (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * ((Real.exp (ε * t) : ℝ) : ℂ))
      = fun t : ℝ => Complex.exp (c * (t : ℂ)) := by
    funext t
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hfun]
  have hderiv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun y : ℝ => Complex.exp (c * (y : ℂ)) / c) (Complex.exp (c * (t : ℂ))) t := by
    intro t _
    have := (hasDerivAt_cexp_mul' c t).div_const c
    rwa [mul_div_cancel_right₀ _ hc0] at this
  have hlim : Tendsto (fun y : ℝ => Complex.exp (c * (y : ℂ)) / c) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h1 : Tendsto (fun y : ℝ => c.re * y) atTop atBot :=
      Filter.tendsto_id.const_mul_atTop_of_neg hcre
    have h2 := Real.tendsto_exp_atBot.comp h1
    have h3 := h2.div_const ‖c‖
    simp only [Function.comp_def, zero_div] at h3
    refine h3.congr fun y => ?_
    rw [norm_div, Complex.norm_exp]
    congr 2
    simp [Complex.mul_re]
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (integrableOn_cexp_mul_Ioi hcre) hlim]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, zero_sub]
  rw [hcdef, show (ε : ℂ) - s = -(s - (ε : ℂ)) by ring, div_neg, neg_neg]

theorem integrableOn_cexp_mul_weightedXiScrewDivisor {C : ℝ} (hC : 0 ≤ C) (hW : ∀ q, ‖W q‖ ≤ C)
    {s : ℂ} (hsHalf : 1 / 2 < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * weightedXiScrewDivisor W t) (Ioi 0) := by
  let M : ℝ := C * xiInvSqMass
  let g : ℝ → ℝ := fun t =>
    (Real.exp ((-s.re + 1 / 2) * t) + Real.exp (-s.re * t)) * M
  have hdecay1 : -s.re + 1 / 2 < 0 := by linarith
  have hdecay2 : -s.re < 0 := by linarith
  have hg : IntegrableOn g (Ioi 0) :=
    ((integrableOn_exp_mul_Ioi hdecay1 0).add
      (integrableOn_exp_mul_Ioi hdecay2 0)).mul_const M
  refine Integrable.mono' hg ?_ ?_
  · exact ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).measurable
      |>.mul (measurable_weightedXiScrewDivisor W)).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := ht.le
    rw [norm_mul, Complex.norm_exp]
    have hre : (-s * (t : ℂ)).re = -s.re * t := by simp [Complex.mul_re]
    rw [hre]
    calc Real.exp (-s.re * t) * ‖weightedXiScrewDivisor W t‖
        ≤ Real.exp (-s.re * t) * (C * (Real.exp (|t| / 2) + 1) * xiInvSqMass) :=
          mul_le_mul_of_nonneg_left (norm_weightedXiScrewDivisor_le W hC hW t) (Real.exp_pos _).le
      _ = g t := by
          rw [abs_of_nonneg ht0]
          dsimp only [g, M]
          rw [show (-s.re + 1 / 2) * t = -s.re * t + t / 2 by ring, Real.exp_add]
          ring

theorem integrableOn_cexp_mul_exp_shift {s : ℂ} (hs : ε < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * ((C₀ * Real.exp (ε * t) : ℝ) : ℂ)) (Ioi 0) := by
  set c : ℂ := (ε : ℂ) - s with hcdef
  have hcre : c.re < 0 := by simp [hcdef]; linarith
  have hfun : (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * ((C₀ * Real.exp (ε * t) : ℝ) : ℂ))
      = fun t : ℝ => (C₀ : ℂ) * Complex.exp (c * (t : ℂ)) := by
    funext t
    push_cast
    have e : Complex.exp (c * (t : ℂ)) = Complex.exp (-s * (t : ℂ)) * Complex.exp ((ε : ℂ) * (t : ℂ)) := by
      rw [← Complex.exp_add, hcdef]
      congr 1
      ring
    rw [e]
    ring
  rw [hfun]
  exact (integrableOn_cexp_mul_Ioi hcre).const_mul _

/-- **Termwise Laplace transform** of the shifted divisor on `Re s > 1/2`. -/
theorem thrLaplace_eq_continuation {C : ℝ} (hC : 0 ≤ C) (hW : ∀ q, ‖W q‖ ≤ C) (hε : ε < 1 / 2)
    {s : ℂ} (hsHalf : 1 / 2 < s.re) :
    thrLaplace W C₀ ε s = thrContinuation W C₀ ε s := by
  unfold thrLaplace thrContinuation thrDivisor
  have hsε : ε < s.re := by linarith
  have hsplit : (fun t : ℝ => Complex.exp (-s * (t : ℂ))
      * (weightedXiScrewDivisor W t + ((C₀ * Real.exp (ε * t) : ℝ) : ℂ)))
      = fun t : ℝ => Complex.exp (-s * (t : ℂ)) * weightedXiScrewDivisor W t
        + Complex.exp (-s * (t : ℂ)) * ((C₀ * Real.exp (ε * t) : ℝ) : ℂ) := by
    funext t; ring
  rw [hsplit, integral_add (integrableOn_cexp_mul_weightedXiScrewDivisor W hC hW hsHalf)
    (integrableOn_cexp_mul_exp_shift C₀ ε hsε)]
  have h1 : (∫ t : ℝ in Ioi 0, Complex.exp (-s * (t : ℂ)) * weightedXiScrewDivisor W t)
      = weightedScrewLaplaceContinuation W s :=
    weightedScrewLaplace_eq_continuation W hC hW hsHalf
  have h2 : (∫ t : ℝ in Ioi 0, Complex.exp (-s * (t : ℂ)) * ((C₀ * Real.exp (ε * t) : ℝ) : ℂ))
      = (C₀ : ℂ) / (s - (ε : ℂ)) := by
    have hfun : (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * ((C₀ * Real.exp (ε * t) : ℝ) : ℂ))
        = fun t : ℝ => (C₀ : ℂ) * (Complex.exp (-s * (t : ℂ)) * ((Real.exp (ε * t) : ℝ) : ℂ)) := by
      funext t; push_cast; ring
    rw [hfun, integral_const_mul, integral_Ioi_cexp_neg_mul_exp ε hsε]
    ring
  rw [h1, h2]

/-! ## Analyticity of the continuation near real points above the threshold -/

/-- The radius of a pole-free ball around a real point `r > ε`. -/
def thrRadius (r : ℝ) : ℝ := min (r / 2) ((r - ε) / 2)

theorem thrRadius_pos {r : ℝ} (hr : ε < r) (hr0 : 0 < r) : 0 < thrRadius ε r :=
  lt_min (by linarith) (by linarith)

theorem thrRadius_le_half (r : ℝ) : thrRadius ε r ≤ r / 2 := min_le_left _ _

theorem thrRadius_le_gap (r : ℝ) : thrRadius ε r ≤ (r - ε) / 2 := min_le_right _ _

theorem differentiableOn_thrContinuation_ball {C : ℝ} (hW : ∀ q, ‖W q‖ ≤ C) {r : ℝ} (hr : ε < r)
    (hr0 : 0 < r) :
    DifferentiableOn ℂ (thrContinuation W C₀ ε) (Metric.ball (r : ℂ) (thrRadius ε r)) := by
  unfold thrContinuation
  refine DifferentiableOn.add ?_ ?_
  · exact (differentiableOn_weightedScrewLaplaceContinuation_ball W hW hr0).mono
      (Metric.ball_subset_ball (thrRadius_le_half ε r))
  · refine DifferentiableOn.div (differentiableOn_const _) (differentiableOn_id.sub (differentiableOn_const _))
      fun s hs => ?_
    intro h
    rw [sub_eq_zero] at h
    rw [Metric.mem_ball, h, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (by linarith)] at hs
    have := thrRadius_le_gap ε r
    linarith

/-- The strip `{b < Re s, |Im s| < (b − ε)/4}`. -/
def thrStrip (b : ℝ) : Set ℂ := {s : ℂ | b < s.re ∧ |s.im| < (b - ε) / 4}

theorem isPreconnected_thrStrip (b : ℝ) : IsPreconnected (thrStrip ε b) := by
  have hconv : Convex ℝ (thrStrip ε b) := by
    have h1 : thrStrip ε b = {s : ℂ | b < s.re} ∩ ({s : ℂ | s.im < (b - ε) / 4}
        ∩ {s : ℂ | -((b - ε) / 4) < s.im}) := by
      ext s
      simp only [thrStrip, mem_setOf_eq, mem_inter_iff, abs_lt]
      tauto
    rw [h1]
    exact (convex_halfSpace_re_gt b).inter ((convex_halfSpace_im_lt _).inter (convex_halfSpace_im_gt _))
  exact hconv.isPreconnected

theorem analyticOnNhd_thrContinuation_strip {C : ℝ} (hW : ∀ q, ‖W q‖ ≤ C) {b : ℝ} (hb : ε < b)
    (hε0 : 0 ≤ ε) :
    AnalyticOnNhd ℂ (thrContinuation W C₀ ε) (thrStrip ε b) := by
  intro s hs
  have hsre : ε < s.re := hb.trans hs.1
  have hsre0 : 0 < s.re := by linarith
  have hsball : s ∈ Metric.ball (s.re : ℂ) (thrRadius ε s.re) := by
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : s - (s.re : ℂ) = (s.im : ℂ) * I := by
      apply Complex.ext <;> simp [mul_re, mul_im]
    rw [heq, norm_mul, norm_real, Real.norm_eq_abs, norm_I, mul_one]
    have h2 := hs.2
    have h1 := hs.1
    refine lt_min ?_ ?_ <;> linarith
  exact (differentiableOn_thrContinuation_ball W C₀ ε hW hsre hsre0).analyticAt
    (Metric.isOpen_ball.mem_nhds hsball)

theorem thrLaplace_eq_continuation_of_momentsAbove {C : ℝ} (hC : 0 ≤ C) (hW : ∀ q, ‖W q‖ ≤ C)
    (hlow : ∀ t : ℝ, 0 ≤ t → -(C₀ * Real.exp (ε * t)) ≤ (weightedXiScrewDivisor W t).re)
    (hreal : ∀ t : ℝ, (weightedXiScrewDivisor W t).im = 0) (hε0 : 0 ≤ ε) (hε : ε < 1 / 2)
    {b : ℝ} (hb : ε < b) (hbHalf : b ≤ 1 / 2) (hMom : ThrMomentsAbove W C₀ ε b) :
    Set.EqOn (thrLaplace W C₀ ε) (thrContinuation W C₀ ε) (thrStrip ε b) := by
  have hleft := analyticOnNhd_thrLaplace_of_momentsAbove W C₀ ε hlow hreal hMom
  have hleftStrip : AnalyticOnNhd ℂ (thrLaplace W C₀ ε) (thrStrip ε b) :=
    fun s hs => hleft s hs.1
  have hright := analyticOnNhd_thrContinuation_strip W C₀ ε hW hb hε0
  have hone : (1 : ℂ) ∈ thrStrip ε b := by
    constructor
    · change b < 1
      linarith
    · simp
      linarith
  have hevent : thrLaplace W C₀ ε =ᶠ[𝓝 (1 : ℂ)] thrContinuation W C₀ ε := by
    have hopen : {s : ℂ | 1 / 2 < s.re} ∈ 𝓝 (1 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hopen] with s hs
    exact thrLaplace_eq_continuation W C₀ ε hC hW hε hs
  exact hleftStrip.eqOn_of_preconnected_of_eventuallyEq hright
    (isPreconnected_thrStrip ε b) hone hevent

/-- Translation of the continuation to a Landau MGF centre. -/
def thrLandauContinuation (r : ℝ) (z : ℂ) : ℂ :=
  thrContinuation W C₀ ε ((r : ℂ) - z)

theorem differentiableOn_thrLandauContinuation_closedBall {C : ℝ} (hW : ∀ q, ‖W q‖ ≤ C)
    {r : ℝ} (hr : ε < r) (hr0 : 0 < r) {R : NNReal} (hR : (R : ℝ) < thrRadius ε r) :
    DifferentiableOn ℂ (thrLandauContinuation W C₀ ε r) (Metric.closedBall 0 (R : ℝ)) := by
  intro z hz
  have hzNorm : ‖z‖ ≤ (R : ℝ) := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  have hsball : (r : ℂ) - z ∈ Metric.ball (r : ℂ) (thrRadius ε r) := by
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : (r : ℂ) - z - (r : ℂ) = -z := by ring
    rw [heq, norm_neg]
    exact lt_of_le_of_lt hzNorm hR
  have hbase := (differentiableOn_thrContinuation_ball W C₀ ε hW hr hr0
    ((r : ℂ) - z) hsball).differentiableAt (Metric.isOpen_ball.mem_nhds hsball)
  have haffine : DifferentiableAt ℂ (fun w : ℂ => (r : ℂ) - w) z := by fun_prop
  exact (hbase.comp z haffine).differentiableWithinAt

theorem thrLandauContinuation_eventuallyEq_complexMGF {C : ℝ} (hC : 0 ≤ C) (hW : ∀ q, ‖W q‖ ≤ C)
    (hlow : ∀ t : ℝ, 0 ≤ t → -(C₀ * Real.exp (ε * t)) ≤ (weightedXiScrewDivisor W t).re)
    (hreal : ∀ t : ℝ, (weightedXiScrewDivisor W t).im = 0) (hε0 : 0 ≤ ε) (hε : ε < 1 / 2)
    {b : ℝ} (hb : ε < b) (hbHalf : b ≤ 1 / 2) (hMom : ThrMomentsAbove W C₀ ε b)
    {r : ℝ} (hr : b < r) :
    thrLandauContinuation W C₀ ε r =ᶠ[𝓝 0] complexMGF id (thrMeasure W C₀ ε r) := by
  have heq := thrLaplace_eq_continuation_of_momentsAbove W C₀ ε hC hW hlow hreal hε0 hε hb hbHalf hMom
  have hopen : {z : ℂ | z.re < r - b ∧ |z.im| < (b - ε) / 4} ∈ 𝓝 (0 : ℂ) := by
    have hOpen : IsOpen {z : ℂ | z.re < r - b ∧ |z.im| < (b - ε) / 4} :=
      (isOpen_lt Complex.continuous_re continuous_const).inter
        (isOpen_lt Complex.continuous_im.abs continuous_const)
    exact hOpen.mem_nhds (by
      constructor
      · simpa using sub_pos.mpr hr
      · simp
        linarith)
  filter_upwards [hopen] with z hz
  have hsStrip : (r : ℂ) - z ∈ thrStrip ε b := by
    constructor
    · simp only [sub_re, ofReal_re]
      linarith [hz.1]
    · simp only [sub_im, ofReal_im, zero_sub, abs_neg]
      exact hz.2
  calc
    thrLandauContinuation W C₀ ε r z = thrContinuation W C₀ ε ((r : ℂ) - z) := rfl
    _ = thrLaplace W C₀ ε ((r : ℂ) - z) := (heq hsStrip).symm
    _ = complexMGF id (thrMeasure W C₀ ε r) z :=
      (complexMGF_id_thrMeasure_eq_laplace W C₀ ε hlow hreal r z).symm

theorem thr_landau_integrable_transfer {C : ℝ} (hC : 0 ≤ C) (hW : ∀ q, ‖W q‖ ≤ C)
    (hlow : ∀ t : ℝ, 0 ≤ t → -(C₀ * Real.exp (ε * t)) ≤ (weightedXiScrewDivisor W t).re)
    (hreal : ∀ t : ℝ, (weightedXiScrewDivisor W t).im = 0) (hε0 : 0 ≤ ε) (hε : ε < 1 / 2)
    {b : ℝ} (hb : ε < b) (hbHalf : b ≤ 1 / 2) (hMom : ThrMomentsAbove W C₀ ε b)
    {r : ℝ} (hr : b < r) {R : NNReal} (hR : (R : ℝ) < thrRadius ε r)
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrhoR : rho < (R : ℝ)) :
    Integrable (fun t : ℝ => Real.exp (rho * id t)) (thrMeasure W C₀ ε r) := by
  have hr0 : 0 < r := by linarith
  exact landau_complexMGF_integrable_transfer
    (by
      have hmeas : AEMeasurable
          (fun t => ENNReal.ofReal (thrDensity W C₀ ε r t))
          (volume.restrict (Ioi 0)) :=
        (measurable_thrDensity W C₀ ε r).ennreal_ofReal.aemeasurable.restrict
      rw [thrMeasure, ae_withDensity_iff' hmeas]
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      intro _hdens
      exact ht.le)
    (zero_mem_interior_integrableExpSet_thrMeasure W C₀ ε hlow hMom hr)
    (differentiableOn_thrLandauContinuation_closedBall W C₀ ε hW (hb.trans hr) hr0 hR)
    (thrLandauContinuation_eventuallyEq_complexMGF W C₀ ε hC hW hlow hreal hε0 hε hb hbHalf hMom hr)
    hrho0 hrhoR

theorem integrableOn_thrDensity_sub_of_transfer
    (hlow : ∀ t : ℝ, 0 ≤ t → -(C₀ * Real.exp (ε * t)) ≤ (weightedXiScrewDivisor W t).re)
    {r rho : ℝ}
    (htransfer : Integrable (fun t : ℝ => Real.exp (rho * id t)) (thrMeasure W C₀ ε r)) :
    IntegrableOn (thrDensity W C₀ ε (r - rho)) (Ioi 0) := by
  have hmeas : AEMeasurable
      (fun t => ENNReal.ofReal (thrDensity W C₀ ε r t))
      (volume.restrict (Ioi 0)) :=
    (measurable_thrDensity W C₀ ε r).ennreal_ofReal.aemeasurable.restrict
  have hnonneg := thrDensity_nonneg_ae W C₀ ε hlow r
  rw [thrMeasure,
    integrable_withDensity_iff_integrable_smul₀' hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at htransfer
  apply htransfer.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hnonneg] with t ht hden
  rw [ENNReal.toReal_ofReal hden]
  simp only [id_eq, smul_eq_mul]
  unfold thrDensity
  rw [show -(r - rho) * t = -r * t + rho * t by ring, Real.exp_add]
  ring

/-! ## Halving towards the threshold -/

/-- One Widder–Landau halving step towards `ε`. -/
theorem thrMomentsAbove_half {C : ℝ} (hC : 0 ≤ C) (hW : ∀ q, ‖W q‖ ≤ C)
    (hlow : ∀ t : ℝ, 0 ≤ t → -(C₀ * Real.exp (ε * t)) ≤ (weightedXiScrewDivisor W t).re)
    (hreal : ∀ t : ℝ, (weightedXiScrewDivisor W t).im = 0) (hε0 : 0 ≤ ε) (hε : ε < 1 / 2)
    {b : ℝ} (hb : ε < b) (hbHalf : b ≤ 1 / 2) (hMom : ThrMomentsAbove W C₀ ε b) :
    ThrMomentsAbove W C₀ ε ((b + ε) / 2) := by
  intro a ha
  let r : ℝ := a + (b - ε) / 2
  let rho : ℝ := (b - ε) / 2
  have hr : b < r := by dsimp only [r]; linarith
  have hr0 : 0 < r := by dsimp only [r]; linarith
  have hrho0 : 0 ≤ rho := by dsimp only [rho]; linarith
  have hgap : rho < thrRadius ε r := by
    refine lt_min ?_ ?_ <;> dsimp only [rho, r] <;> linarith
  let Rreal : ℝ := (rho + thrRadius ε r) / 2
  have hR0 : 0 ≤ Rreal := by
    dsimp only [Rreal]
    have := thrRadius_pos ε (hb.trans hr) hr0
    linarith
  let R : NNReal := ⟨Rreal, hR0⟩
  have hrhoR : rho < (R : ℝ) := by
    change rho < Rreal
    dsimp only [Rreal]
    linarith
  have hRlt : (R : ℝ) < thrRadius ε r := by
    change Rreal < thrRadius ε r
    dsimp only [Rreal]
    linarith
  have htransfer := thr_landau_integrable_transfer W C₀ ε hC hW hlow hreal hε0 hε hb hbHalf hMom hr
    hRlt hrho0 hrhoR
  have hsub := integrableOn_thrDensity_sub_of_transfer W C₀ ε hlow htransfer
  have hra : r - rho = a := by dsimp only [r, rho]; ring
  simpa only [hra] using hsub

/-- The thresholds `ε + (1/2 − ε)/2ⁿ`. -/
def thrThreshold (n : ℕ) : ℝ := ε + (1 / 2 - ε) / 2 ^ n

theorem thrThreshold_gt (hε : ε < 1 / 2) (n : ℕ) : ε < thrThreshold ε n := by
  unfold thrThreshold
  have : 0 < (1 / 2 - ε) / 2 ^ n := by
    have : 0 < 1 / 2 - ε := by linarith
    positivity
  linarith

theorem thrThreshold_le_half (hε : ε < 1 / 2) (n : ℕ) : thrThreshold ε n ≤ 1 / 2 := by
  unfold thrThreshold
  have h1 : (1 / 2 - ε) / 2 ^ n ≤ 1 / 2 - ε := by
    have h0 : 0 ≤ 1 / 2 - ε := by linarith
    have h2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

theorem thrThreshold_succ (n : ℕ) :
    thrThreshold ε (n + 1) = (thrThreshold ε n + ε) / 2 := by
  unfold thrThreshold
  rw [pow_succ]
  field_simp
  ring

theorem thrMomentsAbove_dyadic {C : ℝ} (hC : 0 ≤ C) (hW : ∀ q, ‖W q‖ ≤ C)
    (hlow : ∀ t : ℝ, 0 ≤ t → -(C₀ * Real.exp (ε * t)) ≤ (weightedXiScrewDivisor W t).re)
    (hreal : ∀ t : ℝ, (weightedXiScrewDivisor W t).im = 0) (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) :
    ∀ n : ℕ, ThrMomentsAbove W C₀ ε (thrThreshold ε n) := by
  intro n
  induction n with
  | zero =>
      have h : thrThreshold ε 0 = 1 / 2 := by unfold thrThreshold; simp
      rw [h]
      exact thrMomentsAbove_one_half W C₀ ε hC hW hε
  | succ n ih =>
      rw [thrThreshold_succ]
      exact thrMomentsAbove_half W C₀ ε hC hW hlow hreal hε0 hε (thrThreshold_gt ε hε n)
        (thrThreshold_le_half ε hε n) ih

/-- **All exponential moments above the threshold.** -/
theorem thrMomentsAbove_eps {C : ℝ} (hC : 0 ≤ C) (hW : ∀ q, ‖W q‖ ≤ C)
    (hlow : ∀ t : ℝ, 0 ≤ t → -(C₀ * Real.exp (ε * t)) ≤ (weightedXiScrewDivisor W t).re)
    (hreal : ∀ t : ℝ, (weightedXiScrewDivisor W t).im = 0) (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) :
    ThrMomentsAbove W C₀ ε ε := by
  intro a ha
  have hpos : 0 < a - ε := by linarith
  have hhalf : 0 < 1 / 2 - ε := by linarith
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < (a - ε) / (1 / 2 - ε) :=
    exists_pow_lt_of_lt_one (by positivity) (by norm_num)
  have hthreshold : thrThreshold ε n < a := by
    unfold thrThreshold
    rw [lt_div_iff₀ hhalf] at hn
    have : (1 / 2 - ε) / 2 ^ n = (1 / 2 - ε) * (1 / 2) ^ n := by
      rw [one_div_pow]; ring
    rw [this]
    linarith
  exact thrMomentsAbove_dyadic W C₀ ε hC hW hlow hreal hε0 hε n a hthreshold

/-- **The shifted Laplace transform is analytic on `Re s > ε`.** -/
theorem analyticOnNhd_thrLaplace_gt_eps {C : ℝ} (hC : 0 ≤ C) (hW : ∀ q, ‖W q‖ ≤ C)
    (hlow : ∀ t : ℝ, 0 ≤ t → -(C₀ * Real.exp (ε * t)) ≤ (weightedXiScrewDivisor W t).re)
    (hreal : ∀ t : ℝ, (weightedXiScrewDivisor W t).im = 0) (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) :
    AnalyticOnNhd ℂ (thrLaplace W C₀ ε) {s : ℂ | ε < s.re} :=
  analyticOnNhd_thrLaplace_of_momentsAbove W C₀ ε hlow hreal
    (thrMomentsAbove_eps W C₀ ε hC hW hlow hreal hε0 hε)

end

end RHTower
