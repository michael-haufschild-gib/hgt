import GaloisForLFunctions.EulerFETransportTheory.TheGaussianDefectDeterminesTheCausalTail
import GaloisForLFunctions.RHTower.ThetaGaussianBaseCommutator
import GaloisForLFunctions.HTGeometry.ReflectionIntegral

/-!
# The Gaussian defect of the complete outward translation operator

For `ψ(x) = exp(x/2 - π exp(2x))`, the coordinate `u = exp(2t) - 1`
identifies `∫₀∞ K(t)ψ(x+t)dt` with a damped Laplace transform. Applying
`∂x - (1/2 - 2π exp(2x))` measures its first rate moment.
-/

open MeasureTheory Set Filter Topology Complex

namespace GaloisForLFunctions.EulerFETransportTheory

noncomputable section

private theorem real_smul_complex (r : ℝ) (z : ℂ) : r • z = (r : ℂ) * z := by
  apply Complex.ext <;> simp

/-- Gaussian rate above the unmoved atom. -/
def gaussianCausalRate (t : ℝ) : ℝ := Real.exp (2 * t) - 1

@[fun_prop] theorem continuous_gaussianCausalRate : Continuous gaussianCausalRate := by
  unfold gaussianCausalRate
  fun_prop

/-- Causal density after changing to the rate coordinate and damping once. -/
def gaussianRateDensity (K : ℝ → ℂ) (u : ℝ) : ℂ :=
  ((Real.exp (-(3 / 4 : ℝ) * Real.log (1 + u) - u) / 2 : ℝ) : ℂ) *
    K (Real.log (1 + u) / 2)

/-- Full outward Gaussian response; no truncation of the causal tail. -/
def causalGaussianResponse (K : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), K t * (_root_.RHTower.thetaGaussBase (x + t) : ℂ)

theorem hasDerivAt_gaussianCausalRate (t : ℝ) :
    HasDerivAt gaussianCausalRate (2 * Real.exp (2 * t)) t :=
  (_root_.RHTower.hasDerivAt_exp_two_mul t).sub_const 1

theorem injective_gaussianCausalRate : Function.Injective gaussianCausalRate := by
  intro x y h
  have h1 : Real.exp (2 * x) = Real.exp (2 * y) := sub_left_injective h
  have h2 := Real.exp_injective h1
  linarith

theorem gaussianRateDensity_at_rate (K : ℝ → ℂ) (t : ℝ) :
    gaussianRateDensity K (gaussianCausalRate t) =
      ((Real.exp (-(3 * t / 2) - gaussianCausalRate t) / 2 : ℝ) : ℂ) * K t := by
  unfold gaussianRateDensity gaussianCausalRate
  rw [show 1 + (Real.exp (2 * t) - 1) = Real.exp (2 * t) by ring, Real.log_exp]
  rw [show (2 * t) / 2 = t by ring,
    show -(3 / 4 : ℝ) * (2 * t) = -(3 * t / 2) by ring]

theorem image_gaussianCausalRate : gaussianCausalRate '' Ioi 0 = Ioi 0 := by
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    change 0 < t at ht
    change 0 < Real.exp (2 * t) - 1
    have : 1 < Real.exp (2 * t) := Real.one_lt_exp_iff.2 (by linarith [ht])
    linarith
  · intro hu
    change 0 < u at hu
    refine ⟨Real.log (1 + u) / 2, ?_, ?_⟩
    · exact div_pos (Real.log_pos (by linarith [hu])) (by norm_num)
    · unfold gaussianCausalRate
      rw [show 2 * (Real.log (1 + u) / 2) = Real.log (1 + u) by ring,
        Real.exp_log (by linarith [hu] : 0 < 1 + u)]
      ring

/-- Exact change of variables on the whole positive ray. -/
theorem integral_gaussianCausalRate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) :
    (∫ u in Ioi (0 : ℝ), f u) =
      ∫ t in Ioi (0 : ℝ), (2 * Real.exp (2 * t)) • f (gaussianCausalRate t) := by
  have hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivWithinAt gaussianCausalRate
      (2 * Real.exp (2 * t)) (Ioi 0) t := fun t _ =>
    (hasDerivAt_gaussianCausalRate t).hasDerivWithinAt
  conv_lhs => rw [← image_gaussianCausalRate]
  rw [
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd
      injective_gaussianCausalRate.injOn]
  apply integral_congr_ae
  filter_upwards with t
  rw [abs_of_pos (by positivity : 0 < 2 * Real.exp (2 * t))]

theorem integrable_gaussianCausalRate_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) :
    IntegrableOn f (Ioi 0) ↔
      IntegrableOn (fun t => (2 * Real.exp (2 * t)) • f (gaussianCausalRate t)) (Ioi 0) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul (s := Ioi (0 : ℝ)) measurableSet_Ioi
    (fun t _ => (hasDerivAt_gaussianCausalRate t).hasDerivWithinAt)
    injective_gaussianCausalRate.injOn f
  have he : (fun t => |2 * Real.exp (2 * t)| • f (gaussianCausalRate t)) =
      fun t => (2 * Real.exp (2 * t)) • f (gaussianCausalRate t) := by
    funext t
    rw [abs_of_pos (by positivity : 0 < 2 * Real.exp (2 * t))]
  simpa only [image_gaussianCausalRate, he] using h

/-- Every measurable exponential-order kernel belongs to the damped rate domain. -/
theorem integrable_gaussianRateDensity_of_exponential_bound {K : ℝ → ℂ}
    (hKm : Measurable K) {C B : ℝ}
    (hK : ∀ t, 0 ≤ t → ‖K t‖ ≤ C * Real.exp (B * t)) :
    IntegrableOn (gaussianRateDensity K) (Ioi 0) := by
  apply (integrable_gaussianCausalRate_iff _).2
  have he : (fun t => (2 * Real.exp (2 * t)) • gaussianRateDensity K (gaussianCausalRate t)) =
      fun t => ((Real.exp (t / 2 - gaussianCausalRate t) : ℝ) : ℂ) * K t := by
    funext t
    rw [gaussianRateDensity_at_rate, real_smul_complex]
    have hh : Real.exp (2 * t) * Real.exp (-(3 * t / 2) - gaussianCausalRate t) =
        Real.exp (t / 2 - gaussianCausalRate t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hc := congrArg (fun r : ℝ => (r : ℂ)) hh
    simp only [Complex.ofReal_mul, Complex.ofReal_div] at hc ⊢
    rw [show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num]
    linear_combination (K t) * hc
  rw [he]
  have hb : IntegrableOn (fun t : ℝ => C * Real.exp 1 *
      Real.exp ((B + 1 / 2) * t - Real.exp (2 * t))) (Ioi 0) := by
    have hbase : IntegrableOn (fun t : ℝ => Real.exp ((B + 1 / 2) * t - Real.exp (2 * t)))
        (Ioi 0) := by
      simpa only [one_mul] using
        (_root_.RHTower.integrableOn_exp_sub_mul_exp_two (by norm_num : (0 : ℝ) < 1) (B + 1 / 2))
    exact hbase.const_mul (C * Real.exp 1)
  refine hb.mono' ((by fun_prop : Measurable fun t : ℝ =>
    ((Real.exp (t / 2 - gaussianCausalRate t) : ℝ) : ℂ) * K t).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc Real.exp (t / 2 - gaussianCausalRate t) * ‖K t‖
      ≤ Real.exp (t / 2 - gaussianCausalRate t) * (C * Real.exp (B * t)) :=
        mul_le_mul_of_nonneg_left (hK t ht.le) (Real.exp_pos _).le
    _ = C * Real.exp 1 * Real.exp ((B + 1 / 2) * t - Real.exp (2 * t)) := by
      have hh : Real.exp (t / 2 - gaussianCausalRate t) * Real.exp (B * t) =
          Real.exp 1 * Real.exp ((B + 1 / 2) * t - Real.exp (2 * t)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        unfold gaussianCausalRate
        ring
      linear_combination C * hh

private theorem gaussian_translation_weight (x t : ℝ) :
    (2 * Real.exp (2 * t)) *
      (Real.exp (-(3 * t / 2) - gaussianCausalRate t) / 2 *
        Real.exp (-(Real.pi * Real.exp (2 * x) - 1) * gaussianCausalRate t)) *
        _root_.RHTower.thetaGaussBase x = _root_.RHTower.thetaGaussBase (x + t) := by
  rw [_root_.RHTower.thetaGaussBase_add]
  have he : Real.exp (2 * t) * Real.exp (-(3 * t / 2) - gaussianCausalRate t) *
      Real.exp (-(Real.pi * Real.exp (2 * x) - 1) * gaussianCausalRate t) =
      Real.exp (t / 2 - Real.pi * Real.exp (2 * x) * (Real.exp (2 * t) - 1)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    unfold gaussianCausalRate
    ring
  calc _ = (Real.exp (2 * t) * Real.exp (-(3 * t / 2) - gaussianCausalRate t) *
      Real.exp (-(Real.pi * Real.exp (2 * x) - 1) * gaussianCausalRate t)) *
      _root_.RHTower.thetaGaussBase x := by ring
    _ = _ := by rw [he]

private theorem gaussianCausalRate_integrand (K : ℝ → ℂ) (x t : ℝ) :
    (2 * Real.exp (2 * t)) • ((_root_.RHTower.thetaGaussBase x : ℂ) *
      (gaussianRateDensity K (gaussianCausalRate t) *
        Complex.exp (-((Real.pi * Real.exp (2 * x) - 1 : ℝ) : ℂ) * gaussianCausalRate t))) =
      K t * (_root_.RHTower.thetaGaussBase (x + t) : ℂ) := by
  rw [gaussianRateDensity_at_rate, real_smul_complex]
  have he : Complex.exp (-((Real.pi * Real.exp (2 * x) - 1 : ℝ) : ℂ) * gaussianCausalRate t) =
      (Real.exp (-(Real.pi * Real.exp (2 * x) - 1) * gaussianCausalRate t) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [he]
  have hw := congrArg (fun r : ℝ => (r : ℂ)) (gaussian_translation_weight x t)
  simp only [Complex.ofReal_mul, Complex.ofReal_div] at hw ⊢
  linear_combination (K t) * hw

/-- The actual outward translation integral is a Laplace transform in Gaussian rate. -/
theorem causalGaussianResponse_eq_laplace (K : ℝ → ℂ) (x : ℝ) :
    causalGaussianResponse K x = (_root_.RHTower.thetaGaussBase x : ℂ) *
      gaussianRateLaplace (gaussianRateDensity K) ((Real.pi * Real.exp (2 * x) - 1 : ℝ) : ℂ) := by
  rw [gaussianRateLaplace, ← integral_const_mul, integral_gaussianCausalRate]
  apply integral_congr_ae
  filter_upwards with t
  simpa only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_one] using
    (gaussianCausalRate_integrand K x t).symm

theorem integrable_causalGaussianResponse {K : ℝ → ℂ}
    (hK : IntegrableOn (gaussianRateDensity K) (Ioi 0)) {x : ℝ}
    (hx : 1 < Real.pi * Real.exp (2 * x)) :
    IntegrableOn (fun t => K t * (_root_.RHTower.thetaGaussBase (x + t) : ℂ)) (Ioi 0) := by
  have hi := (integrable_gaussianRateLaplace hK
    (z := ((Real.pi * Real.exp (2 * x) - 1 : ℝ) : ℂ))
    (by simp only [Complex.ofReal_re]; linarith)).const_mul
      (_root_.RHTower.thetaGaussBase x : ℂ)
  exact ((integrable_gaussianCausalRate_iff _).1 hi).congr
    (Eventually.of_forall fun t => gaussianCausalRate_integrand K x t)

/-- Differentiation of the complete causal response on its Gaussian half-line. -/
theorem hasDerivAt_causalGaussianResponse {K : ℝ → ℂ}
    (hK : IntegrableOn (gaussianRateDensity K) (Ioi 0)) {x : ℝ}
    (hx : 1 < Real.pi * Real.exp (2 * x)) :
    HasDerivAt (causalGaussianResponse K)
      (((_root_.RHTower.gaussBaseCoeff x * _root_.RHTower.thetaGaussBase x : ℝ) : ℂ) *
        gaussianRateLaplace (gaussianRateDensity K) ((Real.pi * Real.exp (2 * x) - 1 : ℝ) : ℂ) -
      ((2 * Real.pi * Real.exp (2 * x) : ℝ) : ℂ) *
        (_root_.RHTower.thetaGaussBase x : ℂ) *
        gaussianRateMoment (gaussianRateDensity K) ((Real.pi * Real.exp (2 * x) - 1 : ℝ) : ℂ)) x := by
  have hr : HasDerivAt (fun y : ℝ => Real.pi * Real.exp (2 * y) - 1)
      (2 * Real.pi * Real.exp (2 * x)) x :=
    (((_root_.RHTower.hasDerivAt_exp_two_mul x).const_mul Real.pi).sub_const 1).congr_deriv (by ring)
  have hz : 0 < (((Real.pi * Real.exp (2 * x) - 1 : ℝ) : ℂ)).re := sub_pos.2 hx
  have hl := (hasDerivAt_gaussianRateLaplace hK
    (z := ((Real.pi * Real.exp (2 * x) - 1 : ℝ) : ℂ))
    hz).comp_ofReal.scomp x hr
  have hp := ((_root_.RHTower.hasDerivAt_thetaGaussBase x).ofReal_comp).mul hl
  have he : causalGaussianResponse K = fun y => (_root_.RHTower.thetaGaussBase y : ℂ) *
      gaussianRateLaplace (gaussianRateDensity K) ((Real.pi * Real.exp (2 * y) - 1 : ℝ) : ℂ) :=
    funext (causalGaussianResponse_eq_laplace K)
  rw [he]
  exact hp.congr_deriv (by
    simp only [Function.comp_apply, real_smul_complex, Complex.ofReal_mul]
    ring)

/-- The first-order Gaussian equation records the complete first rate moment. -/
theorem gaussBaseOperator_causalGaussianResponse {K : ℝ → ℂ}
    (hK : IntegrableOn (gaussianRateDensity K) (Ioi 0)) {x : ℝ}
    (hx : 1 < Real.pi * Real.exp (2 * x)) :
    _root_.RHTower.gaussBaseOperator (causalGaussianResponse K) x =
      -((2 * Real.pi * Real.exp (2 * x) : ℝ) : ℂ) *
        (_root_.RHTower.thetaGaussBase x : ℂ) *
        gaussianRateMoment (gaussianRateDensity K) ((Real.pi * Real.exp (2 * x) - 1 : ℝ) : ℂ) := by
  rw [_root_.RHTower.gaussBaseOperator, (hasDerivAt_causalGaussianResponse hK hx).deriv,
    causalGaussianResponse_eq_laplace]
  push_cast
  ring

/-- A scalar identity term is invisible to the Gaussian defect. -/
theorem gaussBaseOperator_add_scalar_gaussian (c : ℂ) {K : ℝ → ℂ}
    (hK : IntegrableOn (gaussianRateDensity K) (Ioi 0)) {x : ℝ}
    (hx : 1 < Real.pi * Real.exp (2 * x)) :
    _root_.RHTower.gaussBaseOperator
      (fun y => c * (_root_.RHTower.thetaGaussBase y : ℂ) + causalGaussianResponse K y) x =
      _root_.RHTower.gaussBaseOperator (causalGaussianResponse K) x := by
  have hc := ((_root_.RHTower.hasDerivAt_thetaGaussBase x).ofReal_comp).const_mul c
  have hk := hasDerivAt_causalGaussianResponse hK hx
  have hs := hc.add hk
  change HasDerivAt (fun y => c * (_root_.RHTower.thetaGaussBase y : ℂ) + causalGaussianResponse K y)
    _ x at hs
  unfold _root_.RHTower.gaussBaseOperator
  rw [hs.deriv, hk.deriv]
  simp only [Complex.ofReal_mul]
  ring

/-- One open interval of the Gaussian differential defect identifies the full rate density. -/
theorem ae_eq_rateDensity_of_gaussian_defect_local {K H : ℝ → ℂ}
    (hK : IntegrableOn (gaussianRateDensity K) (Ioi 0))
    (hH : IntegrableOn (gaussianRateDensity H) (Ioi 0))
    {a b : ℝ} (ha : 1 < Real.pi * Real.exp (2 * a)) (hab : a < b)
    (heq : ∀ x ∈ Ioo a b,
      _root_.RHTower.gaussBaseOperator (causalGaussianResponse K) x =
        _root_.RHTower.gaussBaseOperator (causalGaussianResponse H) x) :
    gaussianRateDensity K =ᵐ[volume.restrict (Ioi 0)] gaussianRateDensity H := by
  have hpq : Real.pi * Real.exp (2 * a) - 1 < Real.pi * Real.exp (2 * b) - 1 := by
    have := mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 (by linarith : 2 * a < 2 * b)) Real.pi_pos
    linarith
  apply ae_eq_of_gaussianRateMoment_local hK hH (by linarith : 0 < Real.pi * Real.exp (2 * a) - 1)
    hpq
  intro r hr
  let x := Real.log ((r + 1) / Real.pi) / 2
  have hr0 : 0 < r := (by linarith : 0 < Real.pi * Real.exp (2 * a) - 1).trans hr.1
  have hxe : Real.pi * Real.exp (2 * x) - 1 = r := by
    dsimp [x]
    rw [show 2 * (Real.log ((r + 1) / Real.pi) / 2) = Real.log ((r + 1) / Real.pi) by ring,
      Real.exp_log (div_pos (by linarith) Real.pi_pos)]
    field_simp
    ring
  have hxa : a < x := by
    have h1 : Real.exp (2 * a) < Real.exp (2 * x) :=
      (mul_lt_mul_iff_right₀ Real.pi_pos).1 (by linarith [hr.1])
    linarith [Real.exp_lt_exp.1 h1]
  have hxb : x < b := by
    have h1 : Real.exp (2 * x) < Real.exp (2 * b) :=
      (mul_lt_mul_iff_right₀ Real.pi_pos).1 (by linarith [hr.2])
    linarith [Real.exp_lt_exp.1 h1]
  have hx : 1 < Real.pi * Real.exp (2 * x) := by linarith
  have h := heq x ⟨hxa, hxb⟩
  rw [gaussBaseOperator_causalGaussianResponse hK hx,
    gaussBaseOperator_causalGaussianResponse hH hx] at h
  have hc : -((2 * Real.pi * Real.exp (2 * x) : ℝ) : ℂ) *
      (_root_.RHTower.thetaGaussBase x : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · exact neg_ne_zero.2 (by exact_mod_cast (by positivity : (2 * Real.pi * Real.exp (2 * x)) ≠ 0))
    · exact_mod_cast (_root_.RHTower.thetaGaussBase_pos x).ne'
  have h' := mul_left_cancel₀ hc h
  have hcast : ((Real.pi * Real.exp (2 * x) - 1 : ℝ) : ℂ) = (r : ℂ) := congrArg Complex.ofReal hxe
  simpa only [hcast] using h'

/-- The rate chart loses no almost-everywhere information about a causal kernel. -/
theorem ae_eq_of_gaussianRateDensity_eq {K H : ℝ → ℂ}
    (hK : IntegrableOn (gaussianRateDensity K) (Ioi 0))
    (hH : IntegrableOn (gaussianRateDensity H) (Ioi 0))
    (heq : gaussianRateDensity K =ᵐ[volume.restrict (Ioi 0)] gaussianRateDensity H) :
    K =ᵐ[volume.restrict (Ioi 0)] H := by
  let q := gaussianRateDensity K - gaussianRateDensity H
  let V : ℝ → ℂ := fun t => (2 * Real.exp (2 * t)) • q (gaussianCausalRate t)
  have hq : IntegrableOn q (Ioi 0) := hK.sub hH
  have hV : IntegrableOn V (Ioi 0) := (integrable_gaussianCausalRate_iff q).1 hq
  have hq0 : q =ᵐ[volume.restrict (Ioi 0)] 0 := by
    filter_upwards [heq] with u hu
    exact sub_eq_zero.2 hu
  have hI : (∫ u in Ioi (0 : ℝ), ‖q u‖) = 0 := by
    calc _ = ∫ _u in Ioi (0 : ℝ), (0 : ℝ) := integral_congr_ae (hq0.mono fun u hu => by rw [hu]; simp)
      _ = 0 := by simp
  rw [integral_gaussianCausalRate] at hI
  have hIV : (∫ t in Ioi (0 : ℝ), ‖V t‖) = 0 := by
    calc _ = ∫ t in Ioi (0 : ℝ), (2 * Real.exp (2 * t)) • ‖q (gaussianCausalRate t)‖ := by
          apply integral_congr_ae
          filter_upwards with t
          change ‖(2 * Real.exp (2 * t)) • q (gaussianCausalRate t)‖ =
            (2 * Real.exp (2 * t)) * ‖q (gaussianCausalRate t)‖
          rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.exp (2 * t))]
      _ = 0 := hI
  have hV0 : V =ᵐ[volume.restrict (Ioi 0)] 0 := by
    have hn := (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun t => norm_nonneg (V t))
      hV.norm).1 hIV
    filter_upwards [hn] with t ht
    exact norm_eq_zero.1 ht
  filter_upwards [hV0] with t ht
  have hs : (2 * Real.exp (2 * t) : ℝ) ≠ 0 := by positivity
  have hdiff : q (gaussianCausalRate t) = 0 := (smul_eq_zero.1 ht).resolve_left hs
  change gaussianRateDensity K (gaussianCausalRate t) - gaussianRateDensity H (gaussianCausalRate t) = 0 at hdiff
  rw [sub_eq_zero, gaussianRateDensity_at_rate, gaussianRateDensity_at_rate] at hdiff
  exact mul_left_cancel₀ (by exact_mod_cast
    (div_ne_zero (Real.exp_ne_zero _) (by norm_num : (2 : ℝ) ≠ 0))) hdiff

/-- A local Gaussian differential measurement identifies the entire causal kernel. -/
theorem ae_eq_of_causalGaussian_defect_local {K H : ℝ → ℂ}
    (hK : IntegrableOn (gaussianRateDensity K) (Ioi 0))
    (hH : IntegrableOn (gaussianRateDensity H) (Ioi 0))
    {a b : ℝ} (ha : 1 < Real.pi * Real.exp (2 * a)) (hab : a < b)
    (heq : ∀ x ∈ Ioo a b,
      _root_.RHTower.gaussBaseOperator (causalGaussianResponse K) x =
        _root_.RHTower.gaussBaseOperator (causalGaussianResponse H) x) :
    K =ᵐ[volume.restrict (Ioi 0)] H :=
  ae_eq_of_gaussianRateDensity_eq hK hH
    (ae_eq_rateDensity_of_gaussian_defect_local hK hH ha hab heq)

/-- The local defect's kernel consists exactly of the scalar identity terms. -/
theorem causalGaussian_defect_local_iff (c d : ℂ) {K H : ℝ → ℂ}
    (hK : IntegrableOn (gaussianRateDensity K) (Ioi 0))
    (hH : IntegrableOn (gaussianRateDensity H) (Ioi 0))
    {a b : ℝ} (ha : 1 < Real.pi * Real.exp (2 * a)) (hab : a < b) :
    (∀ x ∈ Ioo a b,
      _root_.RHTower.gaussBaseOperator
        (fun y => c * (_root_.RHTower.thetaGaussBase y : ℂ) + causalGaussianResponse K y) x =
      _root_.RHTower.gaussBaseOperator
        (fun y => d * (_root_.RHTower.thetaGaussBase y : ℂ) + causalGaussianResponse H y) x) ↔
      K =ᵐ[volume.restrict (Ioi 0)] H := by
  have hx1 : ∀ x ∈ Ioo a b, 1 < Real.pi * Real.exp (2 * x) := by
    intro x hx
    exact ha.trans (mul_lt_mul_of_pos_left (Real.exp_lt_exp.2
      (by linarith [hx.1] : 2 * a < 2 * x)) Real.pi_pos)
  constructor
  · intro heq
    apply ae_eq_of_causalGaussian_defect_local hK hH ha hab
    intro x hx
    have h := heq x hx
    rwa [gaussBaseOperator_add_scalar_gaussian c hK (hx1 x hx),
      gaussBaseOperator_add_scalar_gaussian d hH (hx1 x hx)] at h
  · intro heq
    have hresp : causalGaussianResponse K = causalGaussianResponse H := by
      funext x
      apply integral_congr_ae
      filter_upwards [heq] with t ht
      rw [ht]
    intro x hx
    rw [gaussBaseOperator_add_scalar_gaussian c hK (hx1 x hx),
      gaussBaseOperator_add_scalar_gaussian d hH (hx1 x hx), hresp]

#print axioms integrable_gaussianRateDensity_of_exponential_bound
#print axioms gaussBaseOperator_causalGaussianResponse
#print axioms ae_eq_of_causalGaussian_defect_local
#print axioms causalGaussian_defect_local_iff

end

end GaloisForLFunctions.EulerFETransportTheory
