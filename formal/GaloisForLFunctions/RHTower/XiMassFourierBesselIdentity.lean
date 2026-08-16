import GaloisForLFunctions.RHTower.XiMassFourierBesselRealTime
import GaloisForLFunctions.HTGeometry.PrincipalSquareRootDeriv

/-!
# The Fourier–Bessel identity at complex vertical time

The real-time identity `F_0(h) = 2aσ/q·K₁(aq)` extends to every complex vertical time by analytic
continuation.  Both sides are holomorphic in `τ` on the convex strip

`V_h = {τ : 0 < Re τ, |Im τ| < h}`,

because on it the propagation argument `τ² + h²` has positive real part, so its principal square
root is holomorphic and stays in the right half plane where the Schläfli integral is holomorphic.
The two sides agree on the positive real axis, which meets `V_h` in a set clustering at `1`, so
the identity theorem propagates the identity to all of `V_h`.

The strip covers every spacelike cone `h ≥ κ u` with `κ > 1`, which is exactly the region where
the exterior Bessel analysis lives.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## The mass profile as a function of complex vertical time -/

/-- The hyperbolic mass kernel at general complex vertical time. -/
def xiMassHyperbolicKernelC (a : ℝ) (τ : ℂ) (h t : ℝ) : ℂ :=
  ((a * Real.cosh t : ℝ) : ℂ) * Complex.exp (-τ * ((a * Real.cosh t : ℝ) : ℂ))
    * Complex.exp (-(I * (h : ℂ) * ((a * Real.sinh t : ℝ) : ℂ)))

theorem xiMassHyperbolicKernelC_eq (a sigma u h t : ℝ) :
    xiMassHyperbolicKernelC a ((sigma : ℂ) + (u : ℂ) * I) h t
      = xiMassHyperbolicFourierKernel a sigma u h t := rfl

theorem norm_xiMassHyperbolicKernelC {a : ℝ} (ha : 0 < a) (τ : ℂ) (h t : ℝ) :
    ‖xiMassHyperbolicKernelC a τ h t‖
      = a * Real.cosh t * Real.exp (-(τ.re * (a * Real.cosh t))) := by
  rw [xiMassHyperbolicKernelC, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos ha (Real.cosh_pos t)), Complex.norm_exp, Complex.norm_exp]
  have hfirst : (-τ * ((a * Real.cosh t : ℝ) : ℂ)).re = -(τ.re * (a * Real.cosh t)) := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have hphase : (-(I * (h : ℂ) * ((a * Real.sinh t : ℝ) : ℂ))).re = 0 := by
    simp [Complex.mul_re]
  rw [hfirst, hphase, Real.exp_zero, mul_one]

theorem integrable_xiMassHyperbolicKernelC {a h : ℝ} {τ : ℂ} (ha : 0 < a) (hτ : 0 < τ.re) :
    Integrable (xiMassHyperbolicKernelC a τ h) := by
  have hτeq : ((τ.re : ℝ) : ℂ) + ((τ.im : ℝ) : ℂ) * I = τ := Complex.re_add_im τ
  have := integrable_xiMassHyperbolicFourierKernel (a := a) (sigma := τ.re) (u := τ.im) (h := h)
    ha hτ
  refine this.congr (ae_of_all _ fun t => ?_)
  rw [← xiMassHyperbolicKernelC_eq a τ.re τ.im h t, hτeq]

/-- The mass Fourier profile as a function of complex vertical time. -/
def xiMassProfileC (a h : ℝ) (τ : ℂ) : ℂ := ∫ t : ℝ, xiMassHyperbolicKernelC a τ h t

theorem xiMassProfileC_eq_stripFourier {a h : ℝ} {τ : ℂ} (ha : 0 < a) (hτ : 0 < τ.re) :
    xiMassProfileC a h τ = stripFourier (xiMassAnalyticTest a τ) (h : ℂ) := by
  have hτeq : ((τ.re : ℝ) : ℂ) + ((τ.im : ℝ) : ℂ) * I = τ := Complex.re_add_im τ
  have hrep := stripFourier_xiMass_eq_integral_hyperbolicFourier
    (a := a) (sigma := τ.re) (u := τ.im) (h := h) ha hτ
  rw [hτeq] at hrep
  rw [xiMassProfileC, hrep]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  rw [← xiMassHyperbolicKernelC_eq a τ.re τ.im h t, hτeq]

/-- **The mass profile is holomorphic in the vertical time.** -/
theorem hasDerivAt_xiMassProfileC {a h : ℝ} {τ : ℂ} (ha : 0 < a) (hτ : 0 < τ.re) :
    HasDerivAt (xiMassProfileC a h)
      (∫ t : ℝ, -((a * Real.cosh t : ℝ) : ℂ) * xiMassHyperbolicKernelC a τ h t) τ := by
  have hX2 : (0 : ℝ) < τ.re / 2 := by linarith
  have hY : (0 : ℝ) < τ.re / 2 * a := by positivity
  set F : ℂ → ℝ → ℂ := fun v t => xiMassHyperbolicKernelC a v h t with hF
  set F' : ℂ → ℝ → ℂ := fun v t =>
    -((a * Real.cosh t : ℝ) : ℂ) * xiMassHyperbolicKernelC a v h t with hF'
  set bound : ℝ → ℝ := fun t =>
    a ^ 2 * (Real.cosh t ^ 2 * Real.exp (-(τ.re / 2 * a * Real.cosh t))) with hbound
  have hcont : ∀ v : ℂ, Continuous (fun t : ℝ => xiMassHyperbolicKernelC a v h t) := by
    intro v
    unfold xiMassHyperbolicKernelC
    fun_prop
  have hs : Metric.ball τ (τ.re / 2) ∈ nhds τ := Metric.ball_mem_nhds τ hX2
  have hre : ∀ v : ℂ, v ∈ Metric.ball τ (τ.re / 2) → τ.re / 2 < v.re := by
    intro v hv
    have hdist : ‖v - τ‖ < τ.re / 2 := by
      rw [← Complex.dist_eq]
      exact hv
    have hle : |v.re - τ.re| ≤ ‖v - τ‖ := by
      have := Complex.abs_re_le_norm (v - τ)
      simpa [Complex.sub_re] using this
    have := (abs_lt.1 (lt_of_le_of_lt hle hdist)).1
    linarith
  have hmeas : ∀ᶠ v : ℂ in nhds τ, AEStronglyMeasurable (F v) volume := by
    filter_upwards with v
    exact (hcont v).aestronglyMeasurable
  have hint : Integrable (F τ) volume := integrable_xiMassHyperbolicKernelC ha hτ
  have hmeas' : AEStronglyMeasurable (F' τ) volume :=
    (((by fun_prop : Continuous fun t : ℝ => -((a * Real.cosh t : ℝ) : ℂ))).mul
      (hcont τ)).aestronglyMeasurable
  have hbnd : ∀ᵐ t ∂(volume : Measure ℝ),
      ∀ v ∈ Metric.ball τ (τ.re / 2), ‖F' v t‖ ≤ bound t := by
    filter_upwards with t
    intro v hv
    have hvre := hre v hv
    rw [hF', hbound]
    simp only
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos ha (Real.cosh_pos t)), norm_xiMassHyperbolicKernelC ha]
    have hexp : Real.exp (-(v.re * (a * Real.cosh t)))
        ≤ Real.exp (-(τ.re / 2 * a * Real.cosh t)) := by
      refine Real.exp_le_exp.2 ?_
      have hac : (0 : ℝ) < a * Real.cosh t := mul_pos ha (Real.cosh_pos t)
      have := mul_le_mul_of_nonneg_right hvre.le hac.le
      nlinarith [this]
    have hnn : (0 : ℝ) ≤ a * Real.cosh t * (a * Real.cosh t) := by positivity
    calc a * Real.cosh t * (a * Real.cosh t * Real.exp (-(v.re * (a * Real.cosh t))))
        = (a * Real.cosh t * (a * Real.cosh t)) * Real.exp (-(v.re * (a * Real.cosh t))) := by
          ring
      _ ≤ (a * Real.cosh t * (a * Real.cosh t)) * Real.exp (-(τ.re / 2 * a * Real.cosh t)) :=
          mul_le_mul_of_nonneg_left hexp hnn
      _ = a ^ 2 * (Real.cosh t ^ 2 * Real.exp (-(τ.re / 2 * a * Real.cosh t))) := by ring
  have hboundint : Integrable bound volume := by
    rw [hbound]
    refine Integrable.const_mul ?_ _
    have := HTGeometry.integrable_cosh_sq_mul_exp_neg_mul_cosh hY
    exact this.congr (ae_of_all _ fun t => by ring_nf)
  have hderiv : ∀ᵐ t ∂(volume : Measure ℝ), ∀ v ∈ Metric.ball τ (τ.re / 2),
      HasDerivAt (fun z => F z t) (F' v t) v := by
    filter_upwards with t
    intro v _
    have hbase : HasDerivAt (fun z : ℂ => -z * ((a * Real.cosh t : ℝ) : ℂ))
        (-((a * Real.cosh t : ℝ) : ℂ)) v := by
      simpa using ((hasDerivAt_id v).neg.mul_const (((a * Real.cosh t : ℝ) : ℂ)))
    have hexp := hbase.cexp
    have hmul := (hexp.const_mul (((a * Real.cosh t : ℝ) : ℂ))).mul_const
      (Complex.exp (-(I * (h : ℂ) * ((a * Real.sinh t : ℝ) : ℂ))))
    rw [hF, hF']
    simp only [xiMassHyperbolicKernelC]
    have heq : ((a * Real.cosh t : ℝ) : ℂ)
          * (Complex.exp (-v * ((a * Real.cosh t : ℝ) : ℂ)) * -((a * Real.cosh t : ℝ) : ℂ))
          * Complex.exp (-(I * (h : ℂ) * ((a * Real.sinh t : ℝ) : ℂ)))
        = -((a * Real.cosh t : ℝ) : ℂ)
          * (((a * Real.cosh t : ℝ) : ℂ) * Complex.exp (-v * ((a * Real.cosh t : ℝ) : ℂ))
            * Complex.exp (-(I * (h : ℂ) * ((a * Real.sinh t : ℝ) : ℂ)))) := by ring
    rw [← heq]
    exact hmul
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℝ)) (x₀ := τ) (F := F) (F' := F') (bound := bound)
    (s := Metric.ball τ (τ.re / 2)) hs hmeas hint hmeas' hbnd hboundint hderiv
  exact hmain.2

/-! ## The holomorphic strip -/

/-- The convex strip on which the identity is continued. -/
def xiMassBesselStrip (h : ℝ) : Set ℂ := {τ : ℂ | 0 < τ.re ∧ |τ.im| < h}

theorem convex_xiMassBesselStrip (h : ℝ) : Convex ℝ (xiMassBesselStrip h) := by
  have h1 : Convex ℝ {τ : ℂ | 0 < τ.re} :=
    convex_halfSpace_re_gt 0
  have h2 : Convex ℝ {τ : ℂ | τ.im < h} := convex_halfSpace_im_lt h
  have h3 : Convex ℝ {τ : ℂ | -h < τ.im} := convex_halfSpace_im_gt (-h)
  have hset : xiMassBesselStrip h
      = {τ : ℂ | 0 < τ.re} ∩ ({τ : ℂ | τ.im < h} ∩ {τ : ℂ | -h < τ.im}) := by
    ext τ
    simp only [xiMassBesselStrip, Set.mem_setOf_eq, Set.mem_inter_iff, abs_lt]
    tauto
  rw [hset]
  exact h1.inter (h2.inter h3)

theorem isOpen_xiMassBesselStrip (h : ℝ) : IsOpen (xiMassBesselStrip h) := by
  have hset : xiMassBesselStrip h
      = {τ : ℂ | 0 < τ.re} ∩ ({τ : ℂ | τ.im < h} ∩ {τ : ℂ | -h < τ.im}) := by
    ext τ
    simp only [xiMassBesselStrip, Set.mem_setOf_eq, Set.mem_inter_iff, abs_lt]
    tauto
  rw [hset]
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_im continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im))

theorem xiMassPropagation_re_pos {h : ℝ} {τ : ℂ} (hτ : τ ∈ xiMassBesselStrip h) :
    0 < (τ ^ 2 + (h : ℂ) ^ 2).re := by
  obtain ⟨hre, him⟩ := hτ
  have hval : (τ ^ 2 + (h : ℂ) ^ 2).re = τ.re ^ 2 - τ.im ^ 2 + h ^ 2 := by
    simp [Complex.add_re, Complex.mul_re, pow_two]
  rw [hval]
  have : τ.im ^ 2 < h ^ 2 := by
    have := abs_lt.1 him
    nlinarith [abs_nonneg τ.im, sq_abs τ.im]
  nlinarith [sq_nonneg τ.re]


/-! ## The identity by analytic continuation -/

/-- The Bessel side of the identity. -/
def xiMassBesselSide (a h : ℝ) (τ : ℂ) : ℂ :=
  2 * (a : ℂ) * τ / HTGeometry.csqrt (τ ^ 2 + (h : ℂ) ^ 2)
    * HTGeometry.besselK1C ((a : ℂ) * HTGeometry.csqrt (τ ^ 2 + (h : ℂ) ^ 2))

theorem re_mul_csqrt_pos {a h : ℝ} {τ : ℂ} (ha : 0 < a) (hτ : τ ∈ xiMassBesselStrip h) :
    0 < ((a : ℂ) * HTGeometry.csqrt (τ ^ 2 + (h : ℂ) ^ 2)).re := by
  have hgre : 0 < (τ ^ 2 + (h : ℂ) ^ 2).re := xiMassPropagation_re_pos hτ
  have hcs : 0 < HTGeometry.csqrtRe (τ ^ 2 + (h : ℂ) ^ 2) := HTGeometry.csqrtRe_pos hgre
  have hval : ((a : ℂ) * HTGeometry.csqrt (τ ^ 2 + (h : ℂ) ^ 2)).re
      = a * HTGeometry.csqrtRe (τ ^ 2 + (h : ℂ) ^ 2) := by
    rw [Complex.mul_re, HTGeometry.csqrt_re]
    simp
  rw [hval]
  exact mul_pos ha hcs

theorem differentiableAt_xiMassBesselSide {a h : ℝ} {τ : ℂ} (ha : 0 < a)
    (hτ : τ ∈ xiMassBesselStrip h) : DifferentiableAt ℂ (xiMassBesselSide a h) τ := by
  have hgre : 0 < (τ ^ 2 + (h : ℂ) ^ 2).re := xiMassPropagation_re_pos hτ
  have hg : DifferentiableAt ℂ (fun z : ℂ => z ^ 2 + (h : ℂ) ^ 2) τ := by fun_prop
  have hcs : DifferentiableAt ℂ (fun z : ℂ => HTGeometry.csqrt (z ^ 2 + (h : ℂ) ^ 2)) τ := by
    have h1 : DifferentiableAt ℂ (HTGeometry.csqrt ∘ fun z : ℂ => z ^ 2 + (h : ℂ) ^ 2) τ :=
      (HTGeometry.differentiableAt_csqrt hgre).comp τ hg
    exact h1
  have hne : HTGeometry.csqrt (τ ^ 2 + (h : ℂ) ^ 2) ≠ 0 := HTGeometry.csqrt_ne_zero hgre
  have hnum : DifferentiableAt ℂ (fun z : ℂ => 2 * (a : ℂ) * z) τ := by fun_prop
  have hinner : DifferentiableAt ℂ
      (fun z : ℂ => (a : ℂ) * HTGeometry.csqrt (z ^ 2 + (h : ℂ) ^ 2)) τ := hcs.const_mul _
  have hbes : DifferentiableAt ℂ
      (fun z : ℂ => HTGeometry.besselK1C ((a : ℂ) * HTGeometry.csqrt (z ^ 2 + (h : ℂ) ^ 2))) τ := by
    have h1 : DifferentiableAt ℂ
        (HTGeometry.besselK1C ∘ fun z : ℂ => (a : ℂ) * HTGeometry.csqrt (z ^ 2 + (h : ℂ) ^ 2)) τ :=
      (HTGeometry.differentiableAt_besselK1C (re_mul_csqrt_pos ha hτ)).comp τ hinner
    exact h1
  exact (hnum.div hcs hne).mul hbes

theorem differentiableAt_xiMassProfileC {a h : ℝ} {τ : ℂ} (ha : 0 < a)
    (hτ : τ ∈ xiMassBesselStrip h) : DifferentiableAt ℂ (xiMassProfileC a h) τ :=
  (hasDerivAt_xiMassProfileC ha hτ.1).differentiableAt

/-- On the positive real axis the two sides agree. -/
theorem xiMassProfileC_eq_besselSide_real {a h : ℝ} (ha : 0 < a) (hh : 0 ≤ h) {sigma : ℝ}
    (hsigma : 0 < sigma) :
    xiMassProfileC a h ((sigma : ℝ) : ℂ) = xiMassBesselSide a h ((sigma : ℝ) : ℂ) := by
  have hre : (0 : ℝ) < (((sigma : ℝ) : ℂ)).re := by simpa using hsigma
  have hleft : xiMassProfileC a h ((sigma : ℝ) : ℂ)
      = stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + ((0 : ℝ) : ℂ) * I)) (h : ℂ) := by
    rw [xiMassProfileC_eq_stripFourier ha hre]
    norm_num
  have hbase := stripFourier_xiMass_realTime_eq_bessel (a := a) (sigma := sigma) (h := h)
    ha hsigma hh
  have hprop : ((sigma : ℝ) : ℂ) ^ 2 + (h : ℂ) ^ 2 = ((sigma ^ 2 + h ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have hpos : (0 : ℝ) < sigma ^ 2 + h ^ 2 := by positivity
  rw [hleft, hbase, xiMassBesselSide, hprop, HTGeometry.csqrt_ofReal_of_pos hpos]
  congr 2
  push_cast
  ring

/-- **(17.1) The Fourier–Bessel identity.**  On the spacelike strip the mass Fourier profile is the
order-one Bessel carrier of its own propagation radius. -/
theorem xiMassProfileC_eq_besselSide {a h : ℝ} (ha : 0 < a) (hh : 0 < h) :
    Set.EqOn (xiMassProfileC a h) (xiMassBesselSide a h) (xiMassBesselStrip h) := by
  have hopen : IsOpen (xiMassBesselStrip h) := isOpen_xiMassBesselStrip h
  have hconn : IsPreconnected (xiMassBesselStrip h) :=
    (convex_xiMassBesselStrip h).isPreconnected
  have hone : (1 : ℂ) ∈ xiMassBesselStrip h := by
    refine ⟨by norm_num, ?_⟩
    simpa using hh
  have hL : DifferentiableOn ℂ (xiMassProfileC a h) (xiMassBesselStrip h) := by
    intro z hz
    exact (differentiableAt_xiMassProfileC ha hz).differentiableWithinAt
  have hR : DifferentiableOn ℂ (xiMassBesselSide a h) (xiMassBesselStrip h) := by
    intro z hz
    exact (differentiableAt_xiMassBesselSide ha hz).differentiableWithinAt
  have hLa : AnalyticOnNhd ℂ (xiMassProfileC a h) (xiMassBesselStrip h) :=
    DifferentiableOn.analyticOnNhd hL hopen
  have hRa : AnalyticOnNhd ℂ (xiMassBesselSide a h) (xiMassBesselStrip h) :=
    DifferentiableOn.analyticOnNhd hR hopen
  have htendR : Filter.Tendsto (fun n : ℕ => (1 + 1 / ((n : ℝ) + 1) : ℝ)) Filter.atTop (nhds 1) := by
    have h0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 := Filter.Tendsto.const_add (1 : ℝ) h0
    simpa using h1
  have htend : Filter.Tendsto (fun n : ℕ => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ))
      Filter.atTop (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hcont : Filter.Tendsto (fun x : ℝ => (x : ℂ)) (nhds (1 : ℝ)) (nhds ((1 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.continuousAt
      have h2 := hcont.comp htendR
      simp only [Function.comp_def, Complex.ofReal_one] at h2
      exact h2
    · filter_upwards with n
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hcontra
      have hreal : (1 + 1 / ((n : ℝ) + 1) : ℝ) = 1 := by
        exact_mod_cast congrArg Complex.re hcontra
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hfreqAt : ∀ n : ℕ,
      xiMassProfileC a h ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)
        = xiMassBesselSide a h ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) := by
    intro n
    refine xiMassProfileC_eq_besselSide_real ha hh.le ?_
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hfreq : ∃ᶠ z in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ,
      xiMassProfileC a h z = xiMassBesselSide a h z :=
    htend.frequently ((Filter.Eventually.of_forall hfreqAt).frequently)
  exact hLa.eqOn_of_preconnected_of_frequently_eq hRa hconn hone hfreq

/-- **(17.1)** in terms of the strip Fourier transform. -/
theorem stripFourier_xiMass_eq_bessel {a h : ℝ} {τ : ℂ} (ha : 0 < a) (hh : 0 < h)
    (hτ : τ ∈ xiMassBesselStrip h) :
    stripFourier (xiMassAnalyticTest a τ) (h : ℂ)
      = 2 * (a : ℂ) * τ / HTGeometry.csqrt (τ ^ 2 + (h : ℂ) ^ 2)
        * HTGeometry.besselK1C ((a : ℂ) * HTGeometry.csqrt (τ ^ 2 + (h : ℂ) ^ 2)) := by
  rw [← xiMassProfileC_eq_stripFourier ha hτ.1]
  exact xiMassProfileC_eq_besselSide ha hh hτ

end

end RHTower
