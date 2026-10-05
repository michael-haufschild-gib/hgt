import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinTwoKBesselMellinProduct

/-!
# The Macdonald function `K₀` and its moments

For `r > 0` and `j ∈ ℕ` put

`K_j(r) = ∫₀^∞ cosh(t)^j e^{−r cosh t} dt`  (`kMoment j r`),

so that `K₀` is the Macdonald function and `K₀^{(j)} = (−1)^j K_j`.

* `hasDerivAt_kMoment`: `K_j' = −K_{j+1}`.
* `kMoment_le_exp_mul`: `K_j(r) ≤ e^{−(r − r₁)} K_j(r₁)` for `0 < r₁ ≤ r`, since `cosh ≥ 1`.
* `kMoment_ode`: `r (K₂(r) − K₀(r)) = K₁(r)`, i.e. Bessel's equation `K₀'' + K₀'/r − K₀ = 0`.  It is
  the integral of `d/dt [sinh t · e^{−r cosh t}] = cosh t · e^{−r cosh t} − r sinh² t · e^{−r cosh t}`.
* `mellin_kZero`: `∫₀^∞ r^{s−1} K₀(r) dr = 2^{s−2} Γ(s/2)²` for `Re s > 0`.  Write
  `K₀(r) = ½ ∫_ℝ e^{−r cosh t} dt`, integrate in `r` first (Euler's integral gives
  `Γ(s) cosh(t)^{−s}`), then use the hyperbolic Beta integral `∫_ℝ cosh(t)^{−s} dt = 2^{s−1} Γ(s/2)²/Γ(s)`.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower.BesselKZero

/-- The moment `K_j(r) = ∫₀^∞ cosh(t)^j e^{−r cosh t} dt`. -/
def kMoment (j : ℕ) (r : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), Real.cosh t ^ j * Real.exp (-(r * Real.cosh t))

/-- The integrand of `K_j`. -/
def kIntegrand (j : ℕ) (r t : ℝ) : ℝ := Real.cosh t ^ j * Real.exp (-(r * Real.cosh t))

theorem kIntegrand_nonneg (j : ℕ) (r t : ℝ) : 0 ≤ kIntegrand j r t := by
  unfold kIntegrand
  have := Real.cosh_pos t
  positivity

theorem continuous_kIntegrand (j : ℕ) (r : ℝ) : Continuous (kIntegrand j r) := by
  unfold kIntegrand
  fun_prop

theorem cosh_le_exp_of_nonneg {t : ℝ} (ht : 0 ≤ t) : Real.cosh t ≤ Real.exp t := by
  rw [Real.cosh_eq]
  have : Real.exp (-t) ≤ Real.exp t := Real.exp_le_exp.mpr (by linarith)
  linarith

/-- Gaussian majorant: `cosh(t)^j e^{−r cosh t} ≤ e^{2j²/r} e^{−(r/8) t²}` for `t ≥ 0`. -/
theorem kIntegrand_le {j : ℕ} {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    kIntegrand j r t ≤ Real.exp (2 * (j : ℝ) ^ 2 / r) * Real.exp (-(r / 8) * t ^ 2) := by
  unfold kIntegrand
  have h1 : Real.cosh t ^ j ≤ Real.exp ((j : ℝ) * t) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.cosh_pos t).le (cosh_le_exp_of_nonneg ht) j
  have h2 := GaloisForLFunctions.HTGeometry.bessel_exponent_bound r (j : ℝ) hr ht
  calc Real.cosh t ^ j * Real.exp (-(r * Real.cosh t))
      ≤ Real.exp ((j : ℝ) * t) * Real.exp (-(r * Real.cosh t)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
    _ = Real.exp (-r * Real.cosh t + (j : ℝ) * t) := by
        rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (2 * (j : ℝ) ^ (2 : ℕ) / r - r / 8 * t ^ (2 : ℕ)) := Real.exp_le_exp.mpr h2
    _ = Real.exp (2 * (j : ℝ) ^ 2 / r) * Real.exp (-(r / 8) * t ^ 2) := by
        rw [← Real.exp_add]; ring_nf

theorem integrable_gaussianMajorant (c : ℝ) {b : ℝ} (hb : 0 < b) :
    Integrable fun t : ℝ => c * Real.exp (-b * t ^ 2) :=
  (integrable_exp_neg_mul_sq hb).const_mul c

theorem integrableOn_kIntegrand (j : ℕ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (kIntegrand j r) (Ioi 0) := by
  refine (integrable_gaussianMajorant (Real.exp (2 * (j : ℝ) ^ 2 / r))
    (show 0 < r / 8 by positivity)).integrableOn.mono' (continuous_kIntegrand j r).aestronglyMeasurable
    ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (kIntegrand_nonneg j r t)]
  have := kIntegrand_le (j := j) hr (le_of_lt ht)
  simpa [neg_mul] using this

theorem kMoment_eq (j : ℕ) (r : ℝ) : kMoment j r = ∫ t in Ioi (0 : ℝ), kIntegrand j r t := rfl

theorem kMoment_nonneg (j : ℕ) (r : ℝ) : 0 ≤ kMoment j r :=
  setIntegral_nonneg measurableSet_Ioi fun t _ => kIntegrand_nonneg j r t

/-- `K_j(r) ≤ e^{−(r − r₁)} K_j(r₁)` for `0 < r₁ ≤ r`. -/
theorem kMoment_le_exp_mul (j : ℕ) {r₁ r : ℝ} (hr₁ : 0 < r₁) (h : r₁ ≤ r) :
    kMoment j r ≤ Real.exp (-(r - r₁)) * kMoment j r₁ := by
  rw [kMoment_eq, kMoment_eq, ← integral_const_mul]
  refine setIntegral_mono_on (integrableOn_kIntegrand j (lt_of_lt_of_le hr₁ h))
    ((integrableOn_kIntegrand j hr₁).const_mul _) measurableSet_Ioi fun t _ => ?_
  unfold kIntegrand
  have hc : 1 ≤ Real.cosh t := Real.one_le_cosh t
  have hsplit : Real.exp (-(r * Real.cosh t)) =
      Real.exp (-((r - r₁) * Real.cosh t)) * Real.exp (-(r₁ * Real.cosh t)) := by
    rw [← Real.exp_add]; ring_nf
  have hle : Real.exp (-((r - r₁) * Real.cosh t)) ≤ Real.exp (-(r - r₁)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  rw [hsplit]
  have h0 : 0 ≤ Real.cosh t ^ j * Real.exp (-(r₁ * Real.cosh t)) := by
    have := Real.cosh_pos t; positivity
  calc Real.cosh t ^ j * (Real.exp (-((r - r₁) * Real.cosh t)) * Real.exp (-(r₁ * Real.cosh t)))
      = Real.exp (-((r - r₁) * Real.cosh t)) * (Real.cosh t ^ j * Real.exp (-(r₁ * Real.cosh t))) := by
        ring
    _ ≤ Real.exp (-(r - r₁)) * (Real.cosh t ^ j * Real.exp (-(r₁ * Real.cosh t))) :=
        mul_le_mul_of_nonneg_right hle h0

/-- **`K_j' = −K_{j+1}`.** -/
theorem hasDerivAt_kMoment (j : ℕ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (kMoment j) (-kMoment (j + 1) r) r := by
  have hr2 : 0 < r / 2 := by positivity
  set bound : ℝ → ℝ := fun t =>
    Real.exp (2 * ((j + 1 : ℕ) : ℝ) ^ 2 / (r / 2)) * Real.exp (-((r / 2) / 8) * t ^ 2) with hbound
  have hball : Metric.ball r (r / 2) ∈ 𝓝 r := Metric.ball_mem_nhds r hr2
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun x t => kIntegrand j x t) (F' := fun x t => -kIntegrand (j + 1) x t)
    (bound := bound) (x₀ := r) hball
    (Eventually.of_forall fun x => (continuous_kIntegrand j x).aestronglyMeasurable)
    (integrableOn_kIntegrand j hr)
    ((continuous_kIntegrand (j + 1) r).neg.aestronglyMeasurable)
    ?_ ((integrable_gaussianMajorant _ (show 0 < r / 2 / 8 by positivity)).integrableOn) ?_
  · have h := key.2
    rw [integral_neg] at h
    exact h
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht x hx
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (kIntegrand_nonneg _ _ _)]
    have hx' : r / 2 < x := by
      have := (Metric.mem_ball.mp hx)
      rw [Real.dist_eq] at this
      linarith [abs_lt.mp this]
    have hmono : kIntegrand (j + 1) x t ≤ kIntegrand (j + 1) (r / 2) t := by
      unfold kIntegrand
      have hc : 0 < Real.cosh t := Real.cosh_pos t
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith))
        (by positivity)
    exact hmono.trans (by simpa [hbound, neg_mul] using kIntegrand_le (j := j + 1) hr2 (le_of_lt ht))
  · refine Eventually.of_forall fun t x _ => ?_
    have h1 : HasDerivAt (fun y : ℝ => -(y * Real.cosh t)) (-(1 * Real.cosh t)) x :=
      ((hasDerivAt_id' x).mul_const (Real.cosh t)).neg
    have h2 := (h1.exp).const_mul (Real.cosh t ^ j)
    exact h2.congr_deriv (by unfold kIntegrand; ring)

theorem differentiableAt_kMoment (j : ℕ) {r : ℝ} (hr : 0 < r) : DifferentiableAt ℝ (kMoment j) r :=
  (hasDerivAt_kMoment j hr).differentiableAt

theorem deriv_kMoment (j : ℕ) {r : ℝ} (hr : 0 < r) : deriv (kMoment j) r = -kMoment (j + 1) r :=
  (hasDerivAt_kMoment j hr).deriv

theorem continuousOn_kMoment (j : ℕ) : ContinuousOn (kMoment j) (Ioi 0) :=
  fun _ hr => (differentiableAt_kMoment j hr).continuousAt.continuousWithinAt

/-- **Bessel's equation** in moment form: `r (K₂(r) − K₀(r)) = K₁(r)`. -/
theorem kMoment_ode {r : ℝ} (hr : 0 < r) :
    r * (kMoment 2 r - kMoment 0 r) = kMoment 1 r := by
  -- `d/dt [sinh t e^{−r cosh t}] = cosh t e^{−r cosh t} − r sinh² t e^{−r cosh t}`
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t => Real.sinh t * Real.exp (-(r * Real.cosh t)))
      (kIntegrand 1 r t - r * (kIntegrand 2 r t - kIntegrand 0 r t)) t := by
    intro t _
    have h1 := Real.hasDerivAt_sinh t
    have h2 := (((Real.hasDerivAt_cosh t).const_mul r).neg).exp
    refine (h1.mul h2).congr_deriv ?_
    simp only [kIntegrand, pow_one, pow_zero, one_mul]
    linear_combination (r * Real.exp (-(r * Real.cosh t))) * Real.cosh_sq t
  have hint : IntegrableOn (fun t => kIntegrand 1 r t - r * (kIntegrand 2 r t - kIntegrand 0 r t))
      (Ioi 0) :=
    (integrableOn_kIntegrand 1 hr).sub
      (((integrableOn_kIntegrand 2 hr).sub (integrableOn_kIntegrand 0 hr)).const_mul r)
  have hlim : Tendsto (fun t => Real.sinh t * Real.exp (-(r * Real.cosh t))) atTop (𝓝 0) := by
    -- `0 ≤ sinh t e^{−r cosh t} ≤ cosh t e^{−r cosh t} ≤ e^{2/r} e^{−(r/8) t²}` for `t ≥ 0`
    have hg : Tendsto (fun t : ℝ => Real.exp (2 * ((1 : ℕ) : ℝ) ^ 2 / r) *
        Real.exp (-(r / 8) * t ^ 2)) atTop (𝓝 0) := by
      have : Tendsto (fun t : ℝ => -(r / 8) * t ^ 2) atTop atBot :=
        (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).const_mul_atTop_of_neg
          (by linarith : -(r / 8) < 0)
      have h2 := (Real.tendsto_exp_atBot.comp this).const_mul (Real.exp (2 * ((1 : ℕ) : ℝ) ^ 2 / r))
      rw [mul_zero] at h2
      exact h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg ?_ ?_
    · filter_upwards [eventually_ge_atTop 0] with t ht
      exact mul_nonneg (Real.sinh_nonneg_iff.mpr ht) (Real.exp_nonneg _)
    · filter_upwards [eventually_ge_atTop 0] with t ht
      have hle : Real.sinh t ≤ Real.cosh t := by
        rw [Real.sinh_eq, Real.cosh_eq]; linarith [Real.exp_pos (-t)]
      have h := kIntegrand_le (j := 1) hr ht
      unfold kIntegrand at h
      calc Real.sinh t * Real.exp (-(r * Real.cosh t))
          ≤ Real.cosh t ^ 1 * Real.exp (-(r * Real.cosh t)) := by
            rw [pow_one]; exact mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _)
        _ ≤ _ := h
  have hcont : ContinuousWithinAt (fun t => Real.sinh t * Real.exp (-(r * Real.cosh t))) (Ici 0) 0 := by
    fun_prop
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  simp only [Real.sinh_zero, zero_mul, sub_zero] at hftc
  have h20 : IntegrableOn (fun x => kIntegrand 2 r x - kIntegrand 0 r x) (Ioi 0) :=
    (integrableOn_kIntegrand 2 hr).sub (integrableOn_kIntegrand 0 hr)
  have h23 : IntegrableOn (fun x => r * (kIntegrand 2 r x - kIntegrand 0 r x)) (Ioi 0) :=
    h20.const_mul r
  have e1 : ∫ x in Ioi (0 : ℝ), (kIntegrand 1 r x - r * (kIntegrand 2 r x - kIntegrand 0 r x)) =
      kMoment 1 r - r * (kMoment 2 r - kMoment 0 r) := by
    rw [integral_sub (integrableOn_kIntegrand 1 hr) h23, integral_const_mul,
      integral_sub (integrableOn_kIntegrand 2 hr) (integrableOn_kIntegrand 0 hr)]
    rfl
  rw [e1] at hftc
  linarith

/-! ## The Mellin transform of `K₀` -/

/-- `∫_ℝ e^{−r cosh t} dt = 2 K₀(r)`. -/
theorem integral_exp_neg_mul_cosh (r : ℝ) :
    ∫ t : ℝ, Real.exp (-(r * Real.cosh t)) = 2 * kMoment 0 r := by
  by_cases hr : 0 < r
  · have hInt : Integrable fun t : ℝ => Real.exp (-(r * Real.cosh t)) := by
      have hO := integrableOn_kIntegrand 0 hr
      have hO' : IntegrableOn (fun t : ℝ => Real.exp (-(r * Real.cosh t))) (Ioi 0) := by
        refine hO.congr_fun (fun t _ => ?_) measurableSet_Ioi
        simp [kIntegrand]
      have hI : IntegrableOn (fun t : ℝ => Real.exp (-(r * Real.cosh t))) (Iic 0) := by
        have := (hO'.comp_neg)
        rw [integrableOn_Iic_iff_integrableOn_Iio]
        simpa [Real.cosh_neg] using this
      rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
      exact hI.union hO'
    rw [← setIntegral_univ, ← Iic_union_Ioi (a := (0 : ℝ)),
      setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hInt.integrableOn
        hInt.integrableOn]
    have hneg : ∫ t in Iic (0 : ℝ), Real.exp (-(r * Real.cosh t)) =
        ∫ t in Ioi (0 : ℝ), Real.exp (-(r * Real.cosh t)) := by
      have h := integral_comp_neg_Ioi (0 : ℝ) (fun t : ℝ => Real.exp (-(r * Real.cosh t)))
      simp only [neg_zero, Real.cosh_neg] at h
      exact h.symm
    rw [hneg, kMoment]
    simp only [pow_zero, one_mul]
    ring
  · -- for `r ≤ 0` both sides vanish (no integrability)
    have hnot : ¬ Integrable fun t : ℝ => Real.exp (-(r * Real.cosh t)) := by
      intro h
      have hlow : ∀ t : ℝ, 1 ≤ Real.exp (-(r * Real.cosh t)) := fun t =>
        Real.one_le_exp (by nlinarith [Real.one_le_cosh t])
      have : Integrable (fun _ : ℝ => (1 : ℝ)) :=
        h.mono' (by fun_prop) (Eventually.of_forall fun t => by
          rw [Real.norm_eq_abs, abs_one]; exact hlow t)
      have hvol := (integrable_const_iff (μ := (volume : Measure ℝ)) (c := (1 : ℝ))).mp this
      simp only [one_ne_zero, false_or] at hvol
      have := hvol.measure_univ_lt_top
      rw [Real.volume_univ] at this
      exact lt_irrefl _ this
    have hnotO : ¬ IntegrableOn (fun t : ℝ => Real.cosh t ^ 0 * Real.exp (-(r * Real.cosh t)))
        (Ioi 0) := by
      intro h
      have hlow : ∀ t : ℝ, 1 ≤ Real.cosh t ^ 0 * Real.exp (-(r * Real.cosh t)) := fun t => by
        rw [pow_zero, one_mul]; exact Real.one_le_exp (by nlinarith [Real.one_le_cosh t])
      have : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi 0) :=
        h.mono' (by fun_prop) ((ae_restrict_iff' measurableSet_Ioi).mpr
          (Eventually.of_forall fun t _ => by rw [Real.norm_eq_abs, abs_one]; exact hlow t))
      rw [integrableOn_const_iff] at this
      simp at this
    rw [integral_undef hnot, kMoment, integral_undef hnotO, mul_zero]

/-- **The Mellin transform of `K₀`**: `∫₀^∞ r^{s−1} K₀(r) dr = 2^{s−2} Γ(s/2)²` for `Re s > 0`,
the integral converging absolutely. -/
theorem hasMellin_kZero {s : ℂ} (hs : 0 < s.re) :
    HasMellin (fun r : ℝ => (kMoment 0 r : ℂ)) s ((2 : ℂ) ^ (s - 2) * Complex.Gamma (s / 2) ^ 2) := by
  set F : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) ^ (s - 1) * ((Real.exp (-(p.1 * Real.cosh p.2)) : ℝ) : ℂ)
    with hF
  -- the inner `r`-integral
  have hinner : ∀ t : ℝ, ∫ r in Ioi (0 : ℝ), F (r, t) =
      Complex.Gamma s * ((Real.cosh t : ℝ) : ℂ) ^ (-s) := by
    intro t
    have hc : 0 < Real.cosh t := Real.cosh_pos t
    have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi (a := s) (r := Real.cosh t) hs hc
    simp only [hF]
    have hcongr : ∀ r : ℝ, (r : ℂ) ^ (s - 1) * ((Real.exp (-(r * Real.cosh t)) : ℝ) : ℂ) =
        (r : ℂ) ^ (s - 1) * Complex.exp (-((Real.cosh t : ℂ) * (r : ℂ))) := by
      intro r; rw [Complex.ofReal_exp]; push_cast; ring_nf
    simp_rw [hcongr]
    rw [h, mul_comm]
    congr 1
    rw [one_div, Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg hc.le]; exact Real.pi_ne_zero.symm), ← Complex.cpow_neg]
  -- integrability of `F` on `(0,∞) × ℝ`
  have hnormInner : ∀ t : ℝ, ∫ r in Ioi (0 : ℝ), ‖F (r, t)‖ =
      Real.Gamma s.re * (Real.cosh t) ^ (-s.re) := by
    intro t
    have hc : 0 < Real.cosh t := Real.cosh_pos t
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := s.re) (r := Real.cosh t) hs hc
    have hnorm : ∀ r ∈ Ioi (0 : ℝ), ‖F (r, t)‖ = r ^ (s.re - 1) * Real.exp (-(Real.cosh t * r)) := by
      intro r hr
      have hr0 : (0 : ℝ) < r := hr
      simp only [hF, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hr0, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Complex.sub_re, Complex.one_re]
      ring_nf
    rw [setIntegral_congr_fun measurableSet_Ioi hnorm, h, one_div, Real.inv_rpow hc.le,
      Real.rpow_neg hc.le]
    ring
  have hmeasF : AEStronglyMeasurable F ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    have hcont : ContinuousOn F (Ioi (0 : ℝ) ×ˢ univ) := by
      intro p hp
      have hp1 : (0 : ℝ) < p.1 := hp.1
      refine ContinuousAt.continuousWithinAt ?_
      simp only [hF]
      refine ContinuousAt.mul ?_ (by fun_prop)
      exact (Complex.continuousAt_ofReal_cpow_const p.1 (s - 1) (Or.inr hp1.ne')).comp
        continuous_fst.continuousAt
    have hμ : (volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure ℝ) =
        ((volume : Measure ℝ).prod volume).restrict (Ioi (0 : ℝ) ×ˢ univ) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [hμ]
    exact hcont.aestronglyMeasurable (measurableSet_Ioi.prod MeasurableSet.univ)
  have hGammaCosh : Integrable fun t : ℝ => Real.Gamma s.re * (Real.cosh t) ^ (-s.re) := by
    have h := GaloisForLFunctions.RHTower.integrable_complex_cosh_cpow_neg_mul_exp
      (s := (s.re : ℂ)) (a := 0) (by simpa using hs)
    have h' : Integrable fun t : ℝ => (Real.cosh t) ^ (-s.re) := by
      refine (h.norm).congr (Eventually.of_forall fun t => ?_)
      simp only [zero_mul, Complex.exp_zero, mul_one]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (Real.cosh_pos t)]
      simp
    exact h'.const_mul _
  have hFint : Integrable F ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    rw [integrable_prod_iff' hmeasF]
    refine ⟨Eventually.of_forall fun t => ?_, ?_⟩
    · -- each `r`-slice is integrable
      by_contra hni
      have h0 : ∫ r in Ioi (0 : ℝ), ‖F (r, t)‖ = 0 := by
        apply integral_undef
        intro hn
        have hsl : ContinuousOn (fun r : ℝ => F (r, t)) (Ioi 0) := by
          intro r hr
          refine ContinuousAt.continuousWithinAt ?_
          simp only [hF]
          exact (Complex.continuousAt_ofReal_cpow_const r (s - 1) (Or.inr (ne_of_gt hr))).mul
            (by fun_prop)
        exact hni ((integrable_norm_iff (hsl.aestronglyMeasurable measurableSet_Ioi)).mp hn)
      rw [hnormInner t] at h0
      have hG : 0 < Real.Gamma s.re := Real.Gamma_pos_of_pos hs
      have hc : 0 < (Real.cosh t) ^ (-s.re) := Real.rpow_pos_of_pos (Real.cosh_pos t) _
      exact absurd h0 (mul_pos hG hc).ne'
    · exact hGammaCosh.congr (Eventually.of_forall fun t => (hnormInner t).symm)
  -- assemble
  have hK : ∀ r : ℝ, (kMoment 0 r : ℂ) = (1 / 2 : ℂ) * ∫ t : ℝ, ((Real.exp (-(r * Real.cosh t)) : ℝ) : ℂ) := by
    intro r
    rw [integral_complex_ofReal, integral_exp_neg_mul_cosh]
    push_cast; ring
  have hconv : MellinConvergent (fun r : ℝ => (kMoment 0 r : ℂ)) s := by
    have h := hFint.integral_prod_left
    unfold MellinConvergent
    refine (h.const_mul (1 / 2 : ℂ)).congr (Eventually.of_forall fun r => ?_)
    simp only [hF, smul_eq_mul]
    rw [integral_const_mul, hK r]
    ring
  refine ⟨hconv, ?_⟩
  show ∫ r in Ioi (0 : ℝ), (r : ℂ) ^ (s - 1) • (kMoment 0 r : ℂ) = _
  simp only [smul_eq_mul]
  calc ∫ r in Ioi (0 : ℝ), (r : ℂ) ^ (s - 1) * (kMoment 0 r : ℂ)
      = (1 / 2 : ℂ) * ∫ r in Ioi (0 : ℝ), ∫ t : ℝ, F (r, t) := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
        simp only [hF]
        rw [hK, integral_const_mul]
        ring
    _ = (1 / 2 : ℂ) * ∫ t : ℝ, ∫ r in Ioi (0 : ℝ), F (r, t) := by
        rw [integral_integral_swap hFint]
    _ = (1 / 2 : ℂ) * (Complex.Gamma s * ∫ t : ℝ, ((Real.cosh t : ℝ) : ℂ) ^ (-s)) := by
        simp_rw [hinner]
        rw [integral_const_mul]
    _ = (2 : ℂ) ^ (s - 2) * Complex.Gamma (s / 2) ^ 2 := by
        have hB := GaloisForLFunctions.RHTower.integral_complex_cosh_cpow_neg_mul_exp
          (s := s) (a := 0) (by simpa using half_pos hs) (by simpa using half_pos hs)
        simp only [zero_mul, Complex.exp_zero, mul_one, add_zero, sub_zero] at hB
        rw [hB]
        have hG : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
        have h2 : (2 : ℂ) ^ (s - 1) = 2 * (2 : ℂ) ^ (s - 2) := by
          rw [show s - 1 = (s - 2) + 1 by ring, Complex.cpow_add _ _ (by norm_num),
            Complex.cpow_one]
          ring
        rw [h2]
        field_simp

theorem mellin_kZero {s : ℂ} (hs : 0 < s.re) :
    ∫ r in Ioi (0 : ℝ), (r : ℂ) ^ (s - 1) * (kMoment 0 r : ℂ) =
      (2 : ℂ) ^ (s - 2) * Complex.Gamma (s / 2) ^ 2 :=
  (hasMellin_kZero hs).2

theorem mellinConvergent_kZero {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun r : ℝ => (kMoment 0 r : ℂ)) s :=
  (hasMellin_kZero hs).1

end RHTower.BesselKZero
