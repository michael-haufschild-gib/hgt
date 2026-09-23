import Mathlib

/-!
# Gaussian-mollified block weights

A smooth weight that dominates the indicator of a height block `[a, v]` while keeping its Fourier
transform explicit: the convolution of the indicator of `[p, q]` with the centred Gaussian density
of standard deviation `η`.  Its Fourier transform is the Gaussian factor `e^{-η²ξ²/2}` times the
transform of the indicator, so it is bounded by `2 e^{-η²ξ²/2}/|ξ|` — super-polynomial decay in
`η|ξ|` without any integration by parts.  The weight lies in `[0, 1]`, is at least
`1 − 2 e^{-K²/2}/(K√(2π))` on `[p + Kη, q − Kη]`, has total mass `q − p`, and decays like the
Gaussian outside `[p, q]`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Complex Set

/-! ## The Gaussian kernel -/

/-- The centred Gaussian density with standard deviation `η`. -/
def gaussKernelBlockWeight (η x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2) / (2 * η ^ 2)) / (Real.sqrt (2 * Real.pi) * η)

theorem gaussKernelBlockWeight_nonneg {η : ℝ} (hη : 0 < η) (x : ℝ) : 0 ≤ gaussKernelBlockWeight η x := by
  unfold gaussKernelBlockWeight
  positivity

theorem gaussKernelBlockWeight_pos {η : ℝ} (hη : 0 < η) (x : ℝ) : 0 < gaussKernelBlockWeight η x := by
  unfold gaussKernelBlockWeight
  positivity

theorem gaussKernelBlockWeight_neg (η x : ℝ) : gaussKernelBlockWeight η (-x) = gaussKernelBlockWeight η x := by
  simp [gaussKernelBlockWeight]

theorem continuous_gaussKernelBlockWeight (η : ℝ) : Continuous (gaussKernelBlockWeight η) := by
  unfold gaussKernelBlockWeight
  fun_prop

theorem gaussKernelBlockWeight_eq_exp_neg_mul_sq {η : ℝ} (hη : 0 < η) (x : ℝ) :
    gaussKernelBlockWeight η x = (Real.sqrt (2 * Real.pi) * η)⁻¹ * Real.exp (-(1 / (2 * η ^ 2)) * x ^ 2) := by
  unfold gaussKernelBlockWeight
  rw [div_eq_inv_mul]
  congr 2
  field_simp

theorem integrable_gaussKernelBlockWeight {η : ℝ} (hη : 0 < η) : Integrable (gaussKernelBlockWeight η) := by
  have h := (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 1 / (2 * η ^ 2))).const_mul
    (Real.sqrt (2 * Real.pi) * η)⁻¹
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  rw [gaussKernelBlockWeight_eq_exp_neg_mul_sq hη]

theorem integral_gaussKernelBlockWeight {η : ℝ} (hη : 0 < η) : ∫ x : ℝ, gaussKernelBlockWeight η x = 1 := by
  have hfun : (fun x : ℝ => gaussKernelBlockWeight η x)
      = fun x => (Real.sqrt (2 * Real.pi) * η)⁻¹ * Real.exp (-(1 / (2 * η ^ 2)) * x ^ 2) := by
    funext x
    exact gaussKernelBlockWeight_eq_exp_neg_mul_sq hη x
  rw [hfun, integral_const_mul, integral_gaussian,
    show Real.pi / (1 / (2 * η ^ 2)) = 2 * Real.pi * η ^ 2 by field_simp,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi) (η ^ 2), Real.sqrt_sq hη.le]
  have : Real.sqrt (2 * Real.pi) * η ≠ 0 := by positivity
  field_simp

/-- **Fourier transform of the Gaussian kernel.** -/
theorem integral_gaussKernelBlockWeight_mul_cexp {η : ℝ} (hη : 0 < η) (ξ : ℝ) :
    ∫ s : ℝ, (gaussKernelBlockWeight η s : ℂ) * Complex.exp (-(I * ξ * s))
      = Complex.exp (((-(η ^ 2 * ξ ^ 2 / 2)) : ℝ) : ℂ) := by
  have hη' : (η : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  have hb : ((-(1 / (2 * η ^ 2)) : ℂ)).re < 0 := by
    rw [show ((-(1 / (2 * η ^ 2)) : ℂ)) = ((-(1 / (2 * η ^ 2)) : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
    exact neg_neg_of_pos (by positivity)
  have h := integral_cexp_quadratic hb (-(Complex.I * ξ)) 0
  have hfun : (fun s : ℝ => (gaussKernelBlockWeight η s : ℂ) * Complex.exp (-(I * ξ * s)))
      = fun s : ℝ => ((Real.sqrt (2 * Real.pi) * η : ℝ) : ℂ)⁻¹ *
          Complex.exp ((-(1 / (2 * η ^ 2)) : ℂ) * (s : ℂ) ^ 2 + (-(Complex.I * ξ)) * s + 0) := by
    funext s
    unfold gaussKernelBlockWeight
    push_cast
    rw [div_eq_inv_mul, mul_assoc, ← Complex.exp_add]
    congr 2
    field_simp
    ring
  rw [hfun, integral_const_mul, h]
  have hbase : ((Real.pi : ℂ) / -(-(1 / (2 * η ^ 2)) : ℂ)) = ((2 * Real.pi * η ^ 2 : ℝ) : ℂ) := by
    push_cast
    field_simp
  have hpow : ((2 * Real.pi * η ^ 2 : ℝ) : ℂ) ^ ((1 : ℂ) / 2)
      = ((Real.sqrt (2 * Real.pi) * η : ℝ) : ℂ) := by
    rw [show ((1 : ℂ) / 2) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by positivity)]
    congr 1
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity), Real.sqrt_sq hη.le]
  have hexp : (0 : ℂ) - (-(Complex.I * ξ)) ^ 2 / (4 * (-(1 / (2 * η ^ 2)) : ℂ))
      = ((-(η ^ 2 * ξ ^ 2 / 2) : ℝ) : ℂ) := by
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hbase, hpow, hexp]
  have hne : ((Real.sqrt (2 * Real.pi) * η : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : Real.sqrt (2 * Real.pi) * η ≠ 0)
  field_simp

/-- Gaussian tail bound: `∫_{x}^∞ g ≤ η e^{-x²/(2η²)} / (x √(2π))` for `x > 0`. -/
theorem integral_gaussKernelBlockWeight_Ioi_le {η x : ℝ} (hη : 0 < η) (hx : 0 < x) :
    ∫ s in Ioi x, gaussKernelBlockWeight η s ≤ η * Real.exp (-(x ^ 2) / (2 * η ^ 2)) / (x * Real.sqrt (2 * Real.pi)) := by
  -- antiderivative of `s ↦ s g(s)` is `−η² g(s)`
  have hderiv : ∀ s : ℝ, HasDerivAt (fun s => -(η ^ 2) * gaussKernelBlockWeight η s) (s * gaussKernelBlockWeight η s) s := by
    intro s
    unfold gaussKernelBlockWeight
    have h1 : HasDerivAt (fun s : ℝ => -(s ^ 2) / (2 * η ^ 2)) (-(2 * s) / (2 * η ^ 2)) s := by
      have := ((hasDerivAt_pow 2 s).neg).div_const (2 * η ^ 2)
      simpa using this
    have h2 := (h1.exp).div_const (Real.sqrt (2 * Real.pi) * η)
    have h3 := h2.const_mul (-(η ^ 2))
    have hη' : η ≠ 0 := hη.ne'
    have hs : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
    refine h3.congr_deriv ?_
    field_simp
  have hlim : Filter.Tendsto (fun s => -(η ^ 2) * gaussKernelBlockWeight η s) Filter.atTop (nhds 0) := by
    have hg : Filter.Tendsto (gaussKernelBlockWeight η) Filter.atTop (nhds 0) := by
      unfold gaussKernelBlockWeight
      have hexp : Filter.Tendsto (fun s : ℝ => Real.exp (-(s ^ 2) / (2 * η ^ 2))) Filter.atTop (nhds 0) := by
        have h2 : Filter.Tendsto (fun s : ℝ => s ^ 2 / (2 * η ^ 2)) Filter.atTop Filter.atTop :=
          (Filter.tendsto_pow_atTop two_ne_zero).atTop_div_const (by positivity)
        have h3 := Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp h2)
        refine h3.congr fun s => ?_
        simp only [Function.comp, neg_div]
      simpa using hexp.div_const (Real.sqrt (2 * Real.pi) * η)
    simpa using hg.const_mul (-(η ^ 2))
  have hnn : ∀ s ∈ Ioi x, 0 ≤ s * gaussKernelBlockWeight η s := fun s hs =>
    mul_nonneg (le_trans hx.le (le_of_lt hs)) (gaussKernelBlockWeight_nonneg hη s)
  have hcont : ContinuousWithinAt (fun s => -(η ^ 2) * gaussKernelBlockWeight η s) (Ici x) x :=
    (continuous_const.mul (continuous_gaussKernelBlockWeight η)).continuousWithinAt
  have hint := integral_Ioi_of_hasDerivAt_of_nonneg hcont (fun s _ => hderiv s) hnn hlim
  have hintOn : IntegrableOn (fun s => s * gaussKernelBlockWeight η s) (Ioi x) :=
    integrableOn_Ioi_deriv_of_nonneg hcont (fun s _ => hderiv s) hnn hlim
  have hmono : ∫ s in Ioi x, gaussKernelBlockWeight η s ≤ ∫ s in Ioi x, (1 / x) * (s * gaussKernelBlockWeight η s) := by
    refine setIntegral_mono_on ((integrable_gaussKernelBlockWeight hη).integrableOn) (hintOn.const_mul _)
      measurableSet_Ioi fun s hs => ?_
    have hs' : x ≤ s := le_of_lt hs
    have hg := gaussKernelBlockWeight_nonneg hη s
    rw [show (1 / x) * (s * gaussKernelBlockWeight η s) = (s / x) * gaussKernelBlockWeight η s by ring]
    have : 1 ≤ s / x := by rw [le_div_iff₀ hx]; linarith
    nlinarith
  rw [integral_const_mul, hint] at hmono
  refine hmono.trans (le_of_eq ?_)
  unfold gaussKernelBlockWeight
  field_simp
  ring

/-! ## The mollified block indicator -/

/-- The Gaussian-mollified indicator of `[p, q]` with standard deviation `η`. -/
def blockWeight (p q η t : ℝ) : ℝ :=
  ∫ u in p..q, gaussKernelBlockWeight η (t - u)

theorem blockWeight_eq_interval (p q η t : ℝ) :
    blockWeight p q η t = ∫ s in (t - q)..(t - p), gaussKernelBlockWeight η s := by
  unfold blockWeight
  exact intervalIntegral.integral_comp_sub_left (gaussKernelBlockWeight η) t

theorem intervalIntegrable_gaussKernelBlockWeight {η : ℝ} (hη : 0 < η) (a b : ℝ) :
    IntervalIntegrable (gaussKernelBlockWeight η) volume a b :=
  (integrable_gaussKernelBlockWeight hη).intervalIntegrable

theorem blockWeight_nonneg {η : ℝ} (hη : 0 < η) {p q : ℝ} (hpq : p ≤ q) (t : ℝ) :
    0 ≤ blockWeight p q η t := by
  rw [blockWeight_eq_interval]
  exact intervalIntegral.integral_nonneg (by linarith) fun s _ => gaussKernelBlockWeight_nonneg hη s

theorem blockWeight_le_one {η : ℝ} (hη : 0 < η) {p q : ℝ} (hpq : p ≤ q) (t : ℝ) :
    blockWeight p q η t ≤ 1 := by
  rw [blockWeight_eq_interval, intervalIntegral.integral_of_le (by linarith),
    ← integral_gaussKernelBlockWeight hη]
  exact setIntegral_le_integral (integrable_gaussKernelBlockWeight hη)
    (Filter.Eventually.of_forall fun s => gaussKernelBlockWeight_nonneg hη s)

theorem continuous_blockWeight {η : ℝ} (hη : 0 < η) (p q : ℝ) : Continuous (blockWeight p q η) := by
  have hF : Continuous fun b : ℝ => ∫ s in (0 : ℝ)..b, gaussKernelBlockWeight η s :=
    intervalIntegral.continuous_primitive (fun a b => intervalIntegrable_gaussKernelBlockWeight hη a b) 0
  have hfun : blockWeight p q η = fun t =>
      (∫ s in (0 : ℝ)..(t - p), gaussKernelBlockWeight η s) - ∫ s in (0 : ℝ)..(t - q), gaussKernelBlockWeight η s := by
    funext t
    rw [blockWeight_eq_interval,
      intervalIntegral.integral_interval_sub_left (intervalIntegrable_gaussKernelBlockWeight hη _ _)
        (intervalIntegrable_gaussKernelBlockWeight hη _ _)]
  rw [hfun]
  exact (hF.comp (continuous_id.sub continuous_const)).sub
    (hF.comp (continuous_id.sub continuous_const))

/-- Symmetric central mass: `∫_{-x}^{x} g = 1 − 2 ∫_{x}^∞ g`. -/
theorem integral_gaussKernelBlockWeight_symm {η x : ℝ} (hη : 0 < η) (_hx : 0 ≤ x) :
    ∫ s in (-x)..x, gaussKernelBlockWeight η s = 1 - 2 * ∫ s in Ioi x, gaussKernelBlockWeight η s := by
  have hint := integrable_gaussKernelBlockWeight hη
  have h1 : ∫ s in Iic (-x), gaussKernelBlockWeight η s = ∫ s in Ioi x, gaussKernelBlockWeight η s := by
    rw [← integral_comp_neg_Ioi]
    simp only [gaussKernelBlockWeight_neg]
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (f := gaussKernelBlockWeight η) (b := x) (μ := volume)
    hint.integrableOn hint.integrableOn
  rw [integral_gaussKernelBlockWeight hη] at hsplit
  rw [← intervalIntegral.integral_Iic_sub_Iic hint.integrableOn hint.integrableOn, h1]
  linarith

/-- **Lower bound inside the block**: on `[p + Kη, q − Kη]` the weight is at least
`1 − 2 e^{-K²/2}/(K √(2π))`. -/
theorem blockWeight_ge_of_mem {η K : ℝ} (hη : 0 < η) (hK : 0 < K) {p q t : ℝ}
    (ht₁ : p + K * η ≤ t) (ht₂ : t ≤ q - K * η) :
    1 - 2 * (Real.exp (-(K ^ 2) / 2) / (K * Real.sqrt (2 * Real.pi))) ≤ blockWeight p q η t := by
  have hKη : 0 < K * η := mul_pos hK hη
  rw [blockWeight_eq_interval]
  have hmono : ∫ s in (-(K * η))..(K * η), gaussKernelBlockWeight η s
      ≤ ∫ s in (t - q)..(t - p), gaussKernelBlockWeight η s := by
    refine intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (Filter.Eventually.of_forall fun s => gaussKernelBlockWeight_nonneg hη s)
      (intervalIntegrable_gaussKernelBlockWeight hη _ _)
  refine le_trans ?_ hmono
  rw [integral_gaussKernelBlockWeight_symm hη hKη.le]
  have htail := integral_gaussKernelBlockWeight_Ioi_le hη hKη
  have hsimp : η * Real.exp (-(K * η) ^ 2 / (2 * η ^ 2)) / (K * η * Real.sqrt (2 * Real.pi))
      = Real.exp (-(K ^ 2) / 2) / (K * Real.sqrt (2 * Real.pi)) := by
    have hη' : η ≠ 0 := hη.ne'
    rw [show -(K * η) ^ 2 / (2 * η ^ 2) = -(K ^ 2) / 2 by field_simp]
    field_simp
  rw [hsimp] at htail
  linarith

/-- Gaussian antitonicity on the right half-line. -/
theorem gaussKernelBlockWeight_le_of_le {η s s' : ℝ} (hη : 0 < η) (hs' : 0 ≤ s') (hss : s' ≤ s) :
    gaussKernelBlockWeight η s ≤ gaussKernelBlockWeight η s' := by
  unfold gaussKernelBlockWeight
  have hden : 0 < Real.sqrt (2 * Real.pi) * η := by positivity
  refine div_le_div_of_nonneg_right ?_ hden.le
  refine Real.exp_le_exp.mpr ?_
  have : s' ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hs' hss 2
  have hpos : 0 < 2 * η ^ 2 := by positivity
  rw [div_le_div_iff_of_pos_right hpos]
  linarith

/-- **Decay to the right of the block**: for `t ≥ q`, `w(t) ≤ (q − p) g(t − q)`. -/
theorem blockWeight_le_of_ge {η : ℝ} (hη : 0 < η) {p q t : ℝ} (hpq : p ≤ q) (ht : q ≤ t) :
    blockWeight p q η t ≤ (q - p) * gaussKernelBlockWeight η (t - q) := by
  rw [blockWeight_eq_interval]
  have hle : ∫ s in (t - q)..(t - p), gaussKernelBlockWeight η s
      ≤ ∫ s in (t - q)..(t - p), gaussKernelBlockWeight η (t - q) := by
    refine intervalIntegral.integral_mono_on (by linarith) (intervalIntegrable_gaussKernelBlockWeight hη _ _)
      intervalIntegrable_const fun s hs => ?_
    exact gaussKernelBlockWeight_le_of_le hη (by linarith) hs.1
  refine hle.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- **Decay to the left of the block**: for `t ≤ p`, `w(t) ≤ (q − p) g(p − t)`. -/
theorem blockWeight_le_of_le {η : ℝ} (hη : 0 < η) {p q t : ℝ} (hpq : p ≤ q) (ht : t ≤ p) :
    blockWeight p q η t ≤ (q - p) * gaussKernelBlockWeight η (p - t) := by
  rw [blockWeight_eq_interval]
  have hle : ∫ s in (t - q)..(t - p), gaussKernelBlockWeight η s
      ≤ ∫ s in (t - q)..(t - p), gaussKernelBlockWeight η (t - p) := by
    refine intervalIntegral.integral_mono_on (by linarith) (intervalIntegrable_gaussKernelBlockWeight hη _ _)
      intervalIntegrable_const fun s hs => ?_
    rw [← gaussKernelBlockWeight_neg, ← gaussKernelBlockWeight_neg η (t - p)]
    exact gaussKernelBlockWeight_le_of_le hη (by linarith) (by linarith [hs.2])
  refine hle.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const, smul_eq_mul, ← gaussKernelBlockWeight_neg, show -(t - p) = p - t by ring]
  ring

/-! ## Mass and Fourier transform via Fubini -/

/-- The unimodular twist. -/
theorem norm_cexp_neg_I_mul (ξ t : ℝ) : ‖Complex.exp (-(I * ξ * t))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- The two-variable integrand of the block weight's Fourier transform. -/
def blockFourierIntegrand (p q η ξ : ℝ) (t u : ℝ) : ℂ :=
  Set.indicator (Ioc p q) (fun _ => (1 : ℂ)) u *
    ((gaussKernelBlockWeight η (t - u) : ℂ) * Complex.exp (-(I * ξ * t)))

theorem blockFourierIntegrand_eq_indicator (p q η ξ : ℝ) :
    Function.uncurry (blockFourierIntegrand p q η ξ) =
      Set.indicator (univ ×ˢ Ioc p q)
        (fun z : ℝ × ℝ => (gaussKernelBlockWeight η (z.1 - z.2) : ℂ) * Complex.exp (-(I * ξ * z.1))) := by
  funext z
  simp only [Function.uncurry, blockFourierIntegrand, Set.indicator, Set.mem_prod, Set.mem_univ,
    true_and]
  split_ifs <;> simp

theorem aestronglyMeasurable_blockFourierIntegrand (p q η ξ : ℝ) :
    AEStronglyMeasurable (Function.uncurry (blockFourierIntegrand p q η ξ))
      (volume.prod volume) := by
  rw [blockFourierIntegrand_eq_indicator]
  refine AEStronglyMeasurable.indicator ?_ (MeasurableSet.univ.prod measurableSet_Ioc)
  refine Continuous.aestronglyMeasurable ?_
  have hg := continuous_gaussKernelBlockWeight η
  fun_prop

theorem norm_blockFourierIntegrand (p q η ξ t u : ℝ) (hη : 0 < η) :
    ‖blockFourierIntegrand p q η ξ t u‖ =
      Set.indicator (Ioc p q) (fun _ => (1 : ℝ)) u * gaussKernelBlockWeight η (t - u) := by
  unfold blockFourierIntegrand
  rw [norm_mul, norm_mul, norm_cexp_neg_I_mul, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (gaussKernelBlockWeight_nonneg hη _)]
  congr 1
  simp only [Set.indicator]
  split_ifs <;> simp

theorem integrable_blockFourierIntegrand_left {η : ℝ} (hη : 0 < η) (p q ξ u : ℝ) :
    Integrable (fun t : ℝ => blockFourierIntegrand p q η ξ t u) := by
  unfold blockFourierIntegrand
  by_cases hu : u ∈ Ioc p q
  · have hg : Integrable (fun t : ℝ => ((gaussKernelBlockWeight η (t - u) : ℝ) : ℂ)) :=
      ((integrable_gaussKernelBlockWeight hη).comp_sub_right u).ofReal
    have hmul : Integrable (fun t : ℝ => Complex.exp (-(I * ξ * t)) * ((gaussKernelBlockWeight η (t - u) : ℝ) : ℂ)) :=
      hg.bdd_mul (by fun_prop : Continuous fun t : ℝ => Complex.exp (-(I * ξ * t))).aestronglyMeasurable
        (Filter.Eventually.of_forall fun t => (norm_cexp_neg_I_mul ξ t).le)
    refine (hmul.const_mul (Set.indicator (Ioc p q) (fun _ => (1 : ℂ)) u)).congr
      (Filter.Eventually.of_forall fun t => ?_)
    ring
  · simp [Set.indicator_of_notMem hu]

theorem integral_norm_blockFourierIntegrand {η : ℝ} (hη : 0 < η) (p q ξ u : ℝ) :
    ∫ t : ℝ, ‖blockFourierIntegrand p q η ξ t u‖ =
      Set.indicator (Ioc p q) (fun _ => (1 : ℝ)) u := by
  simp_rw [norm_blockFourierIntegrand p q η ξ _ u hη]
  rw [integral_const_mul]
  have : ∫ t : ℝ, gaussKernelBlockWeight η (t - u) = 1 := by
    rw [integral_sub_right_eq_self (gaussKernelBlockWeight η) u]
    exact integral_gaussKernelBlockWeight hη
  rw [this, mul_one]

theorem integrable_blockFourierIntegrand {η : ℝ} (hη : 0 < η) (p q ξ : ℝ) :
    Integrable (Function.uncurry (blockFourierIntegrand p q η ξ)) (volume.prod volume) := by
  refine (integrable_prod_iff' (aestronglyMeasurable_blockFourierIntegrand p q η ξ)).mpr ⟨?_, ?_⟩
  · exact Filter.Eventually.of_forall fun u => integrable_blockFourierIntegrand_left hη p q ξ u
  · have h : (fun u : ℝ => ∫ t : ℝ, ‖Function.uncurry (blockFourierIntegrand p q η ξ) (t, u)‖)
        = Set.indicator (Ioc p q) (fun _ => (1 : ℝ)) := by
      funext u
      exact integral_norm_blockFourierIntegrand hη p q ξ u
    rw [h]
    exact (integrableOn_const (μ := volume) (s := Ioc p q) (C := (1 : ℝ))
      measure_Ioc_lt_top.ne).integrable_indicator measurableSet_Ioc

theorem integral_blockFourierIntegrand_right {p q : ℝ} (hpq : p ≤ q) (η ξ t : ℝ) :
    ∫ u : ℝ, blockFourierIntegrand p q η ξ t u =
      (blockWeight p q η t : ℂ) * Complex.exp (-(I * ξ * t)) := by
  unfold blockFourierIntegrand
  have : (fun u : ℝ => Set.indicator (Ioc p q) (fun _ => (1 : ℂ)) u *
      ((gaussKernelBlockWeight η (t - u) : ℂ) * Complex.exp (-(I * ξ * t))))
      = Set.indicator (Ioc p q) (fun u => ((gaussKernelBlockWeight η (t - u) : ℂ) * Complex.exp (-(I * ξ * t)))) := by
    funext u
    simp only [Set.indicator]
    split_ifs <;> simp
  rw [this, integral_indicator measurableSet_Ioc, integral_mul_const, blockWeight,
    intervalIntegral.integral_of_le hpq, integral_complex_ofReal]

theorem integral_blockFourierIntegrand_left {η : ℝ} (hη : 0 < η) (p q ξ u : ℝ) :
    ∫ t : ℝ, blockFourierIntegrand p q η ξ t u =
      Set.indicator (Ioc p q) (fun _ => (1 : ℂ)) u *
        (Complex.exp (-(I * ξ * u)) * Complex.exp (((-(η ^ 2 * ξ ^ 2 / 2)) : ℝ) : ℂ)) := by
  unfold blockFourierIntegrand
  rw [integral_const_mul]
  congr 1
  have hshift : (fun t : ℝ => (gaussKernelBlockWeight η (t - u) : ℂ) * Complex.exp (-(I * ξ * t)))
      = fun t : ℝ => (fun s : ℝ => Complex.exp (-(I * ξ * u)) *
          ((gaussKernelBlockWeight η s : ℂ) * Complex.exp (-(I * ξ * s)))) (t - u) := by
    funext t
    simp only
    have hsplit : Complex.exp (-(I * ξ * t))
        = Complex.exp (-(I * ξ * u)) * Complex.exp (-(I * ξ * ((t - u : ℝ) : ℂ))) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hsplit]
    ring
  rw [hshift, integral_sub_right_eq_self
    (fun s : ℝ => Complex.exp (-(I * ξ * u)) * ((gaussKernelBlockWeight η s : ℂ) * Complex.exp (-(I * ξ * s)))) u,
    integral_const_mul, integral_gaussKernelBlockWeight_mul_cexp hη]

/-- **Fourier transform of the block weight.** -/
theorem integral_blockWeight_mul_cexp {η : ℝ} (hη : 0 < η) {p q : ℝ} (hpq : p ≤ q) (ξ : ℝ) :
    ∫ t : ℝ, (blockWeight p q η t : ℂ) * Complex.exp (-(I * ξ * t))
      = Complex.exp (((-(η ^ 2 * ξ ^ 2 / 2)) : ℝ) : ℂ) *
          ∫ u in p..q, Complex.exp (-(I * ξ * u)) := by
  have hswap := integral_integral_swap (integrable_blockFourierIntegrand hη p q ξ)
  simp_rw [integral_blockFourierIntegrand_right hpq η ξ,
    integral_blockFourierIntegrand_left hη p q ξ] at hswap
  rw [hswap]
  have hind : (fun u : ℝ => Set.indicator (Ioc p q) (fun _ => (1 : ℂ)) u *
      (Complex.exp (-(I * ξ * u)) * Complex.exp (((-(η ^ 2 * ξ ^ 2 / 2)) : ℝ) : ℂ)))
      = Set.indicator (Ioc p q) (fun u => Complex.exp (-(I * ξ * u)) *
          Complex.exp (((-(η ^ 2 * ξ ^ 2 / 2)) : ℝ) : ℂ)) := by
    funext u
    simp only [Set.indicator]
    split_ifs <;> simp
  rw [hind, integral_indicator measurableSet_Ioc, integral_mul_const,
    intervalIntegral.integral_of_le hpq]
  ring

/-- **Total mass of the block weight** is the length `q − p`. -/
theorem integral_blockWeight {η : ℝ} (hη : 0 < η) {p q : ℝ} (hpq : p ≤ q) :
    ∫ t : ℝ, blockWeight p q η t = q - p := by
  have h := integral_blockWeight_mul_cexp hη hpq 0
  simp at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

/-- The block weight is integrable. -/
theorem integrable_blockWeight {η : ℝ} (hη : 0 < η) {p q : ℝ} (hpq : p ≤ q) :
    Integrable (blockWeight p q η) := by
  have h := (integrable_blockFourierIntegrand hη p q 0).integral_prod_left
  simp_rw [Function.uncurry_apply_pair, integral_blockFourierIntegrand_right hpq η 0,
    Complex.ofReal_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one] at h
  simpa using h.re

/-- **Gaussian decay of the Fourier transform**: `‖ŵ(ξ)‖ ≤ 2 e^{-η²ξ²/2}/|ξ|`. -/
theorem norm_integral_blockWeight_mul_cexp_le {η : ℝ} (hη : 0 < η) {p q : ℝ} (hpq : p ≤ q)
    {ξ : ℝ} (hξ : ξ ≠ 0) :
    ‖∫ t : ℝ, (blockWeight p q η t : ℂ) * Complex.exp (-(I * ξ * t))‖
      ≤ 2 * Real.exp (-(η ^ 2 * ξ ^ 2 / 2)) / |ξ| := by
  rw [integral_blockWeight_mul_cexp hη hpq ξ, norm_mul, Complex.norm_exp_ofReal]
  have hc : (-(I * ξ) : ℂ) ≠ 0 := by
    intro h
    apply hξ
    have := congrArg Complex.im h
    simp at this
    exact this
  have hfun : (fun u : ℝ => Complex.exp (-(I * ξ * u))) = fun u : ℝ => Complex.exp ((-(I * ξ)) * u) := by
    funext u
    ring_nf
  rw [hfun, integral_exp_mul_complex hc, norm_div]
  have hnum : ‖Complex.exp (-(I * ξ) * q) - Complex.exp (-(I * ξ) * p)‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖Complex.exp (-(I * ξ) * q)‖ = 1 := by
      rw [Complex.norm_exp]; simp
    have h2 : ‖Complex.exp (-(I * ξ) * p)‖ = 1 := by
      rw [Complex.norm_exp]; simp
    rw [h1, h2]; norm_num
  have hden : ‖(-(I * ξ) : ℂ)‖ = |ξ| := by
    rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [hden]
  have hξpos : 0 < |ξ| := abs_pos.mpr hξ
  calc Real.exp (-(η ^ 2 * ξ ^ 2 / 2)) * (‖Complex.exp (-(I * ξ) * q) - Complex.exp (-(I * ξ) * p)‖ / |ξ|)
      ≤ Real.exp (-(η ^ 2 * ξ ^ 2 / 2)) * (2 / |ξ|) := by
        gcongr
    _ = 2 * Real.exp (-(η ^ 2 * ξ ^ 2 / 2)) / |ξ| := by ring

end GaloisForLFunctions.HTGeometry

end
