import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.WeilsFormOnStepPacketsIsDeterminedByItsValuesOnWindows

/-!
# Under the Riemann hypothesis Weil's form of a step packet is nonnegative

Weil's form `𝔚_Q` of a packet in the coordinate of its autocorrelation is defined for bounded
packets that are not smooth. Under the Riemann hypothesis it is nonnegative on every bounded
measurable packet `g` of bounded support with an integrable jump integrand
(`packetForm_nonneg_of_riemannHypothesis`), in particular on step packets
(`packetForm_step_nonneg_of_riemannHypothesis`).

**Proof.** Smooth `g` by bumps of integral one shrinking to the origin, `g_i = φ_i ⋆ g`.

* `g_i` is a packet of class `C²`, so `𝔚_Q(g_i)` is the sum over the zeros, nonnegative under
  the Riemann hypothesis.
* **Smoothing does not increase the jump integral** (`packetAutocorr_mollify_sub_le`). By
  Jensen, `(g_i(u + x) − g_i(u))² ≤ ∫ φ_i(t) (g(u − t + x) − g(u − t))² dt`; integrated over `u`
  this is `h_{g_i}(0) − h_{g_i}(x) ≤ h_g(0) − h_g(x)` at every displacement `x`.
* The other terms converge: `g_i → g` almost everywhere, boundedly and on a fixed compact, so
  the degrees and the autocorrelation at each point converge.

Hence `𝔚_Q(g) ≥ limsup 𝔚_Q(g_i) ≥ 0`.
-/

open Finset Filter Topology MeasureTheory
open Zeta23
open scoped ArithmeticFunction.vonMangoldt Convolution

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### Bounded packets -/

/-- A bounded measurable function supported in `[l, r]` is integrable. -/
theorem integrable_of_bounded_of_support {f : ℝ → ℝ} (hm : Measurable f) {C l r : ℝ}
    (hb : ∀ u, |f u| ≤ C) (hs : ∀ u, f u ≠ 0 → l ≤ u ∧ u ≤ r) : Integrable f := by
  have hsub : Function.support f ⊆ Set.Icc l r := fun u hu => hs u hu
  rw [← integrableOn_iff_integrable_of_support_subset hsub]
  exact Measure.integrableOn_of_bounded (measure_Icc_lt_top (μ := volume)).ne
    hm.aestronglyMeasurable
    (Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hb u)

/-- The autocorrelation vanishes at displacements beyond the length of the support. -/
theorem packetAutocorr_eq_zero_of_support {f : ℝ → ℝ} {a b x : ℝ}
    (hs : ∀ u, f u ≠ 0 → a < u ∧ u < b) (hx : b - a ≤ x) : packetAutocorr f x = 0 := by
  rw [packetAutocorr]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun u => ?_)
  by_cases hu : f u = 0
  · simp [hu]
  · have h1 := (hs u hu).1
    have h2 : f (u + x) = 0 := by
      by_contra h
      have := (hs _ h).2
      linarith
    simp [h2]

/-- `2(h(0) − h(x)) = ∫ (f(u + x) − f(u))² du`. -/
theorem two_mul_packetAutocorr_zero_sub {f : ℝ → ℝ} (hf2 : Integrable fun u => f u ^ 2)
    {x : ℝ} (hfx : Integrable fun u => f u * f (u + x)) :
    2 * (packetAutocorr f 0 - packetAutocorr f x) = ∫ u, (f (u + x) - f u) ^ 2 := by
  have h0 : packetAutocorr f 0 = ∫ u, f u ^ 2 := by
    simp only [packetAutocorr, add_zero]
    exact integral_congr_ae (Eventually.of_forall fun u => (sq (f u)).symm)
  have hshift : Integrable fun u => f (u + x) ^ 2 := hf2.comp_add_right x
  have hs : ∫ u, f (u + x) ^ 2 = ∫ u, f u ^ 2 :=
    integral_add_right_eq_self (fun u => f u ^ 2) x
  have e : (fun u => (f (u + x) - f u) ^ 2) =
      fun u => f (u + x) ^ 2 - 2 * (f u * f (u + x)) + f u ^ 2 := by
    funext u
    ring
  have i1 : Integrable fun u => 2 * (f u * f (u + x)) := hfx.const_mul 2
  have i12 : Integrable fun u => f (u + x) ^ 2 - 2 * (f u * f (u + x)) := hshift.sub i1
  rw [e, integral_add i12 hf2, integral_sub hshift i1, integral_const_mul, hs, h0, packetAutocorr]
  ring

/-- **Jensen with a weight of integral one.** -/
theorem sq_integral_mul_le {φ w : ℝ → ℝ} (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ)
    (hφ1 : ∫ t, φ t = 1) (h1 : Integrable fun t => φ t * w t)
    (h2 : Integrable fun t => φ t * w t ^ 2) :
    (∫ t, φ t * w t) ^ 2 ≤ ∫ t, φ t * w t ^ 2 := by
  have hnn : 0 ≤ ∫ t, φ t * (w t - ∫ t, φ t * w t) ^ 2 :=
    integral_nonneg fun t => mul_nonneg (hφ0 t) (sq_nonneg _)
  have e : (fun t => φ t * (w t - ∫ t, φ t * w t) ^ 2) =
      fun t => φ t * w t ^ 2 - 2 * (∫ t, φ t * w t) * (φ t * w t) +
        (∫ t, φ t * w t) ^ 2 * φ t := by
    funext t
    ring
  have i1 : Integrable fun t => 2 * (∫ t, φ t * w t) * (φ t * w t) := h1.const_mul _
  have i12 : Integrable fun t => φ t * w t ^ 2 - 2 * (∫ t, φ t * w t) * (φ t * w t) := h2.sub i1
  have i3 : Integrable fun t => (∫ t, φ t * w t) ^ 2 * φ t := hφi.const_mul _
  rw [e, integral_add i12 i3, integral_sub h2 i1, integral_const_mul, integral_const_mul,
    hφ1] at hnn
  nlinarith

/-! ### Smoothing a bounded packet -/

/-- Bumps of radius `1/(i + 1)`. -/
def shrinkingBump (i : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := 1 / (2 * ((i : ℝ) + 1))
  rOut := 1 / ((i : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := one_div_lt_one_div_of_lt (by positivity)
    (by linarith [show (0 : ℝ) ≤ i from Nat.cast_nonneg i])

theorem shrinkingBump_rOut (i : ℕ) : (shrinkingBump i).rOut = 1 / ((i : ℝ) + 1) := rfl

theorem shrinkingBump_rOut_le_one (i : ℕ) : (shrinkingBump i).rOut ≤ 1 := by
  rw [shrinkingBump_rOut, div_le_one (by positivity)]
  linarith [show (0 : ℝ) ≤ i from Nat.cast_nonneg i]

/-- The packet smoothed by the bump of integral one. -/
def mollify (φ : ContDiffBump (0 : ℝ)) (g : ℝ → ℝ) : ℝ → ℝ :=
  (φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g

section Mollify

variable {g : ℝ → ℝ} {M l r : ℝ} (φ : ContDiffBump (0 : ℝ))

theorem mollify_apply (g : ℝ → ℝ) (u : ℝ) :
    mollify φ g u = ∫ t, φ.normed volume t * g (u - t) := by
  rw [mollify, convolution_def]
  rfl

theorem normed_eq_zero_of_le {t : ℝ} (ht : φ.rOut ≤ |t|) : φ.normed volume t = 0 := by
  have h : t ∉ Function.support (φ.normed volume) := by
    rw [φ.support_normed_eq, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    exact not_lt.mpr ht
  exact Function.notMem_support.mp h

/-- A bounded measurable function against the bump is integrable. -/
theorem integrable_normed_mul {b : ℝ → ℝ} (hbm : Measurable b) {C : ℝ} (hb : ∀ t, |b t| ≤ C) :
    Integrable fun t => φ.normed volume t * b t := by
  refine ((φ.integrable_normed (μ := volume)).norm.mul_const C).mono'
    ((φ.continuous_normed (μ := volume)).measurable.mul hbm).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hb t) (norm_nonneg _)

variable (hgm : Measurable g) (hgb : ∀ u, |g u| ≤ M) (hsupp : ∀ u, g u ≠ 0 → l ≤ u ∧ u ≤ r)

include hgm hgb in
theorem abs_mollify_le (u : ℝ) : |mollify φ g u| ≤ M := by
  rw [mollify_apply, ← Real.norm_eq_abs]
  have hb : Integrable fun t => φ.normed volume t * M := (φ.integrable_normed).mul_const M
  refine (norm_integral_le_of_norm_le hb (Eventually.of_forall fun t => ?_)).trans (le_of_eq ?_)
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed t)]
    exact mul_le_mul_of_nonneg_left (hgb _) (φ.nonneg_normed t)
  · rw [integral_mul_const, φ.integral_normed, one_mul]

include hsupp in
/-- The smoothed packet is supported within the radius of the bump of the support. -/
theorem mollify_ne_zero (u : ℝ) (hu : mollify φ g u ≠ 0) :
    l - φ.rOut < u ∧ u < r + φ.rOut := by
  by_contra hcon
  apply hu
  rw [mollify_apply]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
  show φ.normed volume t * g (u - t) = 0
  by_cases ht : φ.rOut ≤ |t|
  · rw [normed_eq_zero_of_le φ ht, zero_mul]
  · have ht' : |t| < φ.rOut := lt_of_not_ge ht
    have hg0 : g (u - t) = 0 := by
      by_contra hne
      obtain ⟨h1, h2⟩ := hsupp _ hne
      apply hcon
      constructor <;> linarith [abs_lt.mp ht']
    rw [hg0, mul_zero]

include hgm hgb hsupp in
theorem locallyIntegrable_packet : LocallyIntegrable g :=
  (integrable_of_bounded_of_support hgm hgb hsupp).locallyIntegrable

include hgm hgb hsupp in
theorem contDiff_mollify : ContDiff ℝ 2 (mollify φ g) := by
  have h := HasCompactSupport.contDiff_convolution_left (n := 2) (ContinuousLinearMap.lsmul ℝ ℝ)
    (φ.hasCompactSupport_normed (μ := volume)) (φ.contDiff_normed (μ := volume))
    (locallyIntegrable_packet hgm hgb hsupp)
  exact h

include hsupp in
theorem hasCompactSupport_mollify : HasCompactSupport (mollify φ g) :=
  HasCompactSupport.intro (isCompact_Icc (a := l - φ.rOut) (b := r + φ.rOut)) fun u hu => by
    by_contra hne
    obtain ⟨h1, h2⟩ := mollify_ne_zero φ hsupp u hne
    exact hu ⟨h1.le, h2.le⟩

include hgm hgb hsupp in
/-- **Smoothing does not increase `h(0) − h(x)`.** -/
theorem packetAutocorr_mollify_sub_le (x : ℝ) :
    packetAutocorr (mollify φ g) 0 - packetAutocorr (mollify φ g) x ≤
      packetAutocorr g 0 - packetAutocorr g x := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hgb 0)
  have hGc : Continuous (mollify φ g) := (contDiff_mollify φ hgm hgb hsupp).continuous
  have hGm : Measurable (mollify φ g) := hGc.measurable
  have hGs : ∀ u, mollify φ g u ≠ 0 → l - φ.rOut ≤ u ∧ u ≤ r + φ.rOut := fun u hu =>
    ⟨(mollify_ne_zero φ hsupp u hu).1.le, (mollify_ne_zero φ hsupp u hu).2.le⟩
  have hGb := abs_mollify_le φ hgm hgb
  -- integrability of the squares and of the products
  have hsq : ∀ {f : ℝ → ℝ} {a b : ℝ}, Measurable f → (∀ u, |f u| ≤ M) →
      (∀ u, f u ≠ 0 → a ≤ u ∧ u ≤ b) → Integrable fun u => f u ^ 2 := fun {f a b} hf hfb hfs =>
    integrable_of_bounded_of_support (hf.pow_const 2)
      (fun u => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hfb u) 2)
      (fun u hu => hfs u fun h0 => hu (by rw [h0]; ring))
  have hpr : ∀ {f : ℝ → ℝ} {a b : ℝ}, Measurable f → (∀ u, |f u| ≤ M) →
      (∀ u, f u ≠ 0 → a ≤ u ∧ u ≤ b) → Integrable fun u => f u * f (u + x) :=
    fun {f a b} hf hfb hfs =>
      integrable_of_bounded_of_support (hf.mul (hf.comp (measurable_id.add_const x)))
        (C := M * M)
        (fun u => by
          rw [abs_mul]
          exact mul_le_mul (hfb u) (hfb _) (abs_nonneg _) hM0)
        (fun u hu => hfs u fun h0 => hu (by rw [h0, zero_mul]))
  have hG := two_mul_packetAutocorr_zero_sub (hsq hGm hGb hGs) (hpr hGm hGb hGs)
  have hg := two_mul_packetAutocorr_zero_sub (hsq hgm hgb hsupp) (hpr hgm hgb hsupp)
  -- the square of the difference of `g` at the displacement `x`
  set w : ℝ → ℝ := fun v => (g (v + x) - g v) ^ 2 with hw
  have hwm : Measurable w := ((hgm.comp (measurable_id.add_const x)).sub hgm).pow_const 2
  have hwi : Integrable w := by
    have hi1 : Integrable fun u => g (u + x) ^ 2 := (hsq hgm hgb hsupp).comp_add_right x
    have hi2 : Integrable fun u => 2 * (g u * g (u + x)) := (hpr hgm hgb hsupp).const_mul 2
    have hi12 : Integrable fun u => g (u + x) ^ 2 - 2 * (g u * g (u + x)) := hi1.sub hi2
    have e : w = fun u => g (u + x) ^ 2 - 2 * (g u * g (u + x)) + g u ^ 2 := by
      funext u
      simp only [hw]
      ring
    rw [e]
    exact hi12.add (hsq hgm hgb hsupp)
  -- Jensen at each point
  have hpt : ∀ u, (mollify φ g (u + x) - mollify φ g u) ^ 2 ≤
      ((φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) u := by
    intro u
    have hmeas : ∀ c : ℝ, Measurable fun t => g (c - t) := fun c =>
      hgm.comp (measurable_const.sub measurable_id)
    have i1 : Integrable fun t => φ.normed volume t * g (u + x - t) :=
      integrable_normed_mul φ (hmeas _) fun t => hgb _
    have i2 : Integrable fun t => φ.normed volume t * g (u - t) :=
      integrable_normed_mul φ (hmeas _) fun t => hgb _
    have hdiff : mollify φ g (u + x) - mollify φ g u =
        ∫ t, φ.normed volume t * (g (u - t + x) - g (u - t)) := by
      rw [mollify_apply, mollify_apply, ← integral_sub i1 i2]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      show φ.normed volume t * g (u + x - t) - φ.normed volume t * g (u - t) =
        φ.normed volume t * (g (u - t + x) - g (u - t))
      rw [show u + x - t = u - t + x by ring]
      ring
    have hconv : ((φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) u =
        ∫ t, φ.normed volume t * (g (u - t + x) - g (u - t)) ^ 2 := by
      rw [convolution_def]
      rfl
    have hdm : Measurable fun t => g (u - t + x) - g (u - t) :=
      (hgm.comp ((measurable_const.sub measurable_id).add_const x)).sub (hmeas u)
    have hdb : ∀ t, |g (u - t + x) - g (u - t)| ≤ M + M := fun t =>
      (abs_sub _ _).trans (add_le_add (hgb _) (hgb _))
    rw [hdiff, hconv]
    exact sq_integral_mul_le φ.nonneg_normed φ.integrable_normed φ.integral_normed
      (integrable_normed_mul φ hdm hdb)
      (integrable_normed_mul φ (hdm.pow_const 2) fun t => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hdb t) 2)
  -- integrate over `u`
  have hLi : Integrable fun u => (mollify φ g (u + x) - mollify φ g u) ^ 2 := by
    have hi1 : Integrable fun u => mollify φ g (u + x) ^ 2 :=
      (hsq hGm hGb hGs).comp_add_right x
    have hi2 : Integrable fun u => 2 * (mollify φ g u * mollify φ g (u + x)) :=
      (hpr hGm hGb hGs).const_mul 2
    have hi12 : Integrable fun u =>
        mollify φ g (u + x) ^ 2 - 2 * (mollify φ g u * mollify φ g (u + x)) := hi1.sub hi2
    have e : (fun u => (mollify φ g (u + x) - mollify φ g u) ^ 2) = fun u =>
        mollify φ g (u + x) ^ 2 - 2 * (mollify φ g u * mollify φ g (u + x)) +
          mollify φ g u ^ 2 := by
      funext u
      ring
    rw [e]
    exact hi12.add (hsq hGm hGb hGs)
  have hRi : Integrable ((φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) :=
    (φ.integrable_normed (μ := volume)).integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hwi
  have hint : ∫ u, ((φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) u =
      ∫ v, w v := by
    rw [integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) (φ.integrable_normed (μ := volume))
      hwi, φ.integral_normed]
    simp
  have hmono := integral_mono hLi hRi hpt
  rw [hint, ← hG, ← hg] at hmono
  linarith

end Mollify

/-! ### Convergence of the smoothed packets -/

section Limit

variable {g : ℝ → ℝ} {M l r : ℝ} (hgm : Measurable g) (hgb : ∀ u, |g u| ≤ M)
  (hsupp : ∀ u, g u ≠ 0 → l ≤ u ∧ u ≤ r)

include hgm hgb hsupp in
theorem ae_tendsto_mollify :
    ∀ᵐ u : ℝ, Tendsto (fun i : ℕ => mollify (shrinkingBump i) g u) atTop (𝓝 (g u)) := by
  have hr : Tendsto (fun i : ℕ => (shrinkingBump i).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hK : ∀ᶠ i : ℕ in atTop, (shrinkingBump i).rOut ≤ 2 * (shrinkingBump i).rIn :=
    Eventually.of_forall fun i => by
      show 1 / ((i : ℝ) + 1) ≤ 2 * (1 / (2 * ((i : ℝ) + 1)))
      have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
      rw [show 2 * (1 / (2 * ((i : ℝ) + 1))) = 1 / ((i : ℝ) + 1) by field_simp]
  exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hr hK
    (locallyIntegrable_packet hgm hgb hsupp)

include hgm hgb hsupp in
/-- The smoothed packets vanish off a fixed interval. -/
theorem mollify_eq_zero_of_notMem (i : ℕ) {u : ℝ} (hu : u ∉ Set.Icc (l - 1) (r + 1)) :
    mollify (shrinkingBump i) g u = 0 := by
  by_contra hne
  obtain ⟨h1, h2⟩ := mollify_ne_zero (shrinkingBump i) hsupp u hne
  have h3 := shrinkingBump_rOut_le_one i
  exact hu ⟨by linarith, by linarith⟩

include hgm hgb hsupp in
/-- The degrees of the smoothed packets converge. -/
theorem tendsto_integral_mollify_mul {e : ℝ → ℝ} (he : Continuous e) :
    Tendsto (fun i : ℕ => ∫ u, mollify (shrinkingBump i) g u * e u) atTop
      (𝓝 (∫ u, g u * e u)) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hgb 0)
  refine tendsto_integral_of_dominated_convergence
    (Set.indicator (Set.Icc (l - 1) (r + 1)) fun u => M * |e u|) (fun i => ?_) ?_ (fun i => ?_) ?_
  · exact ((contDiff_mollify (shrinkingBump i) hgm hgb hsupp).continuous.mul
      he).aestronglyMeasurable
  · exact ((continuous_const.mul he.abs).integrableOn_Icc).integrable_indicator measurableSet_Icc
  · refine Eventually.of_forall fun u => ?_
    by_cases hu : u ∈ Set.Icc (l - 1) (r + 1)
    · rw [Set.indicator_of_mem hu, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (abs_mollify_le (shrinkingBump i) hgm hgb u)
        (abs_nonneg _)
    · rw [Set.indicator_of_notMem hu, mollify_eq_zero_of_notMem hgm hgb hsupp i hu, zero_mul,
        norm_zero]
  · exact (ae_tendsto_mollify hgm hgb hsupp).mono fun u hu => hu.mul_const (e u)

include hgm hgb hsupp in
/-- The autocorrelations of the smoothed packets converge at every displacement. -/
theorem tendsto_packetAutocorr_mollify (x : ℝ) :
    Tendsto (fun i : ℕ => packetAutocorr (mollify (shrinkingBump i) g) x) atTop
      (𝓝 (packetAutocorr g x)) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hgb 0)
  have hae := ae_tendsto_mollify hgm hgb hsupp
  have hae' : ∀ᵐ u : ℝ, Tendsto (fun i : ℕ => mollify (shrinkingBump i) g (u + x)) atTop
      (𝓝 (g (u + x))) := (quasiMeasurePreserving_add_right volume x).ae hae
  refine tendsto_integral_of_dominated_convergence
    (Set.indicator (Set.Icc (l - 1) (r + 1)) fun _ => M * M) (fun i => ?_) ?_ (fun i => ?_) ?_
  · have hc := (contDiff_mollify (shrinkingBump i) hgm hgb hsupp).continuous
    exact (hc.mul (hc.comp (continuous_id.add continuous_const))).aestronglyMeasurable
  · exact (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  · refine Eventually.of_forall fun u => ?_
    by_cases hu : u ∈ Set.Icc (l - 1) (r + 1)
    · rw [Set.indicator_of_mem hu, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul (abs_mollify_le (shrinkingBump i) hgm hgb u)
        (abs_mollify_le (shrinkingBump i) hgm hgb _) (abs_nonneg _) hM0
    · rw [Set.indicator_of_notMem hu, mollify_eq_zero_of_notMem hgm hgb hsupp i hu, zero_mul,
        norm_zero]
  · filter_upwards [hae, hae'] with u h1 h2
    exact h1.mul h2

end Limit

/-! ### The sign under the Riemann hypothesis -/

/-- **Under the Riemann hypothesis Weil's form is nonnegative on bounded packets.** For `g`
measurable, bounded, supported in an interval of length less than `log(Q + 1)`, with an
integrable jump integrand: `𝔚_Q(g) ≥ 0`. -/
theorem packetForm_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis) {g : ℝ → ℝ}
    (hgm : Measurable g) {M l r : ℝ} (hgb : ∀ u, |g u| ≤ M)
    (hsupp : ∀ u, g u ≠ 0 → l ≤ u ∧ u ≤ r) {Q : ℕ} (hQ : r - l < Real.log ((Q : ℝ) + 1))
    (hJ : IntegrableOn (levyJump g) (Set.Ioi 0)) : 0 ≤ packetForm Q g := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hgb 0)
  -- the part of the form that converges under smoothing
  set P : (ℝ → ℝ) → ℝ := fun f =>
    2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) +
      EF.gammaBracket 0 * packetAutocorr f 0 -
      2 * ∑ k ∈ Icc 2 Q, contactWeight k * packetAutocorr f (Real.log k) with hP
  have hPform : ∀ f : ℝ → ℝ, packetForm Q f = P f + ∫ x in Set.Ioi 0, levyJump f x := fun f => by
    simp only [packetForm, hP]
    ring
  have hPlim : Tendsto (fun i : ℕ => P (mollify (shrinkingBump i) g)) atTop (𝓝 (P g)) := by
    have h1 := tendsto_integral_mollify_mul hgm hgb hsupp
      (e := fun u => Real.exp (-u / 2)) (by fun_prop)
    have h2 := tendsto_integral_mollify_mul hgm hgb hsupp
      (e := fun u => Real.exp (u / 2)) (by fun_prop)
    have h0 := tendsto_packetAutocorr_mollify hgm hgb hsupp 0
    have hk : Tendsto (fun i : ℕ => ∑ k ∈ Icc 2 Q,
        contactWeight k * packetAutocorr (mollify (shrinkingBump i) g) (Real.log k)) atTop
        (𝓝 (∑ k ∈ Icc 2 Q, contactWeight k * packetAutocorr g (Real.log k))) :=
      tendsto_finsetSum _ fun k _ =>
        (tendsto_packetAutocorr_mollify hgm hgb hsupp (Real.log k)).const_mul (contactWeight k)
    exact (((h1.mul h2).const_mul 2).add (h0.const_mul (EF.gammaBracket 0))).sub
      (hk.const_mul 2)
  -- the jump integrand is nonnegative
  have hg2 : Integrable fun u => g u ^ 2 :=
    integrable_of_bounded_of_support (hgm.pow_const 2)
      (fun u => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hgb u) 2)
      (fun u hu => hsupp u fun h0 => hu (by rw [h0]; ring))
  have hgx : ∀ x : ℝ, Integrable fun u => g u * g (u + x) := fun x =>
    integrable_of_bounded_of_support (hgm.mul (hgm.comp (measurable_id.add_const x)))
      (C := M * M)
      (fun u => by
        rw [abs_mul]
        exact mul_le_mul (hgb u) (hgb _) (abs_nonneg _) hM0)
      (fun u hu => hsupp u fun h0 => hu (by rw [h0, zero_mul]))
  have hJnn : ∀ x ∈ Set.Ioi (0 : ℝ), 0 ≤ levyJump g x := fun x hx => by
    have h := two_mul_packetAutocorr_zero_sub hg2 (hgx x)
    have hnn : 0 ≤ ∫ u, (g (u + x) - g u) ^ 2 := integral_nonneg fun u => sq_nonneg _
    have hω := _root_.RHTower.archLevyDensity_pos hx
    rw [levyJump]
    nlinarith
  have hJle : ∀ i : ℕ, ∫ x in Set.Ioi 0, levyJump (mollify (shrinkingBump i) g) x ≤
      ∫ x in Set.Ioi 0, levyJump g x := fun i => by
    by_cases hint : IntegrableOn (levyJump (mollify (shrinkingBump i) g)) (Set.Ioi 0)
    · refine setIntegral_mono_on hint hJ measurableSet_Ioi fun x hx => ?_
      rw [levyJump, levyJump]
      exact mul_le_mul_of_nonneg_left
        (packetAutocorr_mollify_sub_le (shrinkingBump i) hgm hgb hsupp x)
        (by have := _root_.RHTower.archLevyDensity_pos hx; positivity)
    · rw [integral_undef hint]
      exact setIntegral_nonneg measurableSet_Ioi hJnn
  -- the smoothed packets: the form is the sum over the zeros
  have hδ : 0 < Real.log ((Q : ℝ) + 1) - (r - l) := sub_pos.mpr hQ
  have hsmall : ∀ᶠ i : ℕ in atTop, 2 * (shrinkingBump i).rOut ≤
      Real.log ((Q : ℝ) + 1) - (r - l) := by
    have ht : Tendsto (fun i : ℕ => 2 * (shrinkingBump i).rOut) atTop (𝓝 (2 * 0)) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
    rw [mul_zero] at ht
    exact ht.eventually (Iic_mem_nhds hδ)
  have hpos : ∀ᶠ i : ℕ in atTop, 0 ≤ P (mollify (shrinkingBump i) g) +
      ∫ x in Set.Ioi 0, levyJump (mollify (shrinkingBump i) g) x := by
    filter_upwards [hsmall] with i hi
    have hC2 := contDiff_mollify (shrinkingBump i) hgm hgb hsupp
    have hcs := hasCompactSupport_mollify (shrinkingBump i) hsupp
    have hQi : ∀ n : ℕ, Q < n →
        packetAutocorr (mollify (shrinkingBump i) g) (Real.log n) = 0 := by
      intro n hn
      refine packetAutocorr_eq_zero_of_support (mollify_ne_zero (shrinkingBump i) hsupp) ?_
      have hlog : Real.log ((Q : ℝ) + 1) ≤ Real.log n := by
        refine Real.log_le_log (by positivity) ?_
        exact_mod_cast hn
      linarith
    rw [← hPform, ← zeroSum_eq_packetForm hC2 hcs hQi]
    have h1 := neg_offLineDefect_le_zeroSum hC2 hcs
    have h2 := riemannHypothesis_iff_offLineDefect_eq_zero.mp hRH _ hC2 hcs
    linarith
  have hfin : ∀ᶠ i : ℕ in atTop, 0 ≤ P (mollify (shrinkingBump i) g) +
      ∫ x in Set.Ioi 0, levyJump g x := hpos.mono fun i hi => by linarith [hJle i]
  rw [hPform g]
  exact ge_of_tendsto (hPlim.add_const _) hfin

/-! ### Step packets -/

section Step

variable {ι : Type*} {s : Finset ι} {x : ι → ℕ} {x₀ X Q : ℕ}

/-- The jump integrand of a combination of nested flat packets is integrable. -/
theorem integrableOn_levyJump_step (hx₀ : 1 ≤ x₀) (hx : ∀ j ∈ s, x₀ ≤ x j) (τ : ι → ℝ) :
    IntegrableOn (levyJump fun u => ∑ j ∈ s, τ j * flatPacket x₀ (x j) u) (Set.Ioi 0) := by
  have hx₀' : (0 : ℝ) < x₀ := by exact_mod_cast hx₀
  have hxr : ∀ j ∈ s, (x₀ : ℝ) ≤ ((x j : ℕ) : ℝ) := fun j hj => by exact_mod_cast hx j hj
  have hA := polarOn_packetAutocorr (v := fun j => flatPacket (x₀ : ℝ) ((x j : ℕ) : ℝ)) (s := s)
    fun j _ l _ y => integrable_flatPacket_mul_flatPacket _ _ _ _ _
  have hpol : ∀ y : ℝ, PolarOn (fun f : ℝ → ℝ => levyJump f y)
      (fun j => flatPacket (x₀ : ℝ) ((x j : ℕ) : ℝ)) s := fun y =>
    ((hA 0).sub (hA y)).const_mul (2 * _root_.RHTower.archLevyDensity y)
  have hJ : ∀ j ∈ s, IntegrableOn (levyJump (flatPacket (x₀ : ℝ) ((x j : ℕ) : ℝ))) (Set.Ioi 0) :=
    fun j hj => integrableOn_levyJump_flatPacket hx₀' (hxr j hj)
  have hJd : ∀ j ∈ s, ∀ l ∈ s, IntegrableOn (levyJump fun u =>
      flatPacket (x₀ : ℝ) ((x l : ℕ) : ℝ) u - flatPacket (x₀ : ℝ) ((x j : ℕ) : ℝ) u)
      (Set.Ioi 0) := fun j hj l hl => by
    have hpos : (0 : ℝ) < min ((x j : ℕ) : ℝ) ((x l : ℕ) : ℝ) :=
      lt_min (hx₀'.trans_le (hxr j hj)) (hx₀'.trans_le (hxr l hl))
    have hI := integrableOn_levyJump_flatPacket hpos
      (min_le_max (a := ((x j : ℕ) : ℝ)) (b := ((x l : ℕ) : ℝ)))
    rcases flatPacket_sub_eq hx₀' (hxr j hj) (hxr l hl) with h | h
    · rw [h]
      exact hI
    · rw [h, levyJump_neg_fun]
      exact hI
  have e : (levyJump fun u => ∑ j ∈ s, τ j * flatPacket x₀ (x j) u) = fun y =>
      1 / 2 * ∑ j ∈ s, ∑ l ∈ s, τ j * τ l *
        (levyJump (flatPacket (x₀ : ℝ) ((x j : ℕ) : ℝ)) y +
          levyJump (flatPacket (x₀ : ℝ) ((x l : ℕ) : ℝ)) y -
          levyJump (fun u => flatPacket (x₀ : ℝ) ((x l : ℕ) : ℝ) u -
            flatPacket (x₀ : ℝ) ((x j : ℕ) : ℝ) u) y) := by
    funext y
    exact hpol y τ
  rw [e]
  exact (integrable_finsetSum _ fun j hj => integrable_finsetSum _ fun l hl =>
    (((hJ j hj).add (hJ l hl)).sub (hJd j hj l hl)).const_mul (τ j * τ l)).const_mul (1 / 2)

/-- **Under the Riemann hypothesis Weil's form of a step packet is nonnegative.** -/
theorem packetForm_step_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis) (hx₀ : 1 ≤ x₀)
    (hx : ∀ j ∈ s, x₀ ≤ x j ∧ x j ≤ X) (hQ : X ≤ Q * x₀) (τ : ι → ℝ) :
    0 ≤ packetForm Q (fun u => ∑ j ∈ s, τ j * flatPacket x₀ (x j) u) := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨j₀, hj₀⟩
  · have e : (fun u : ℝ => ∑ j ∈ (∅ : Finset ι), τ j * flatPacket x₀ (x j) u) = fun _ => 0 := by
      funext u
      simp
    rw [e]
    simp [packetForm, packetAutocorr, levyJump]
  have hx₀' : (0 : ℝ) < x₀ := by exact_mod_cast hx₀
  have hQ1 : 1 ≤ Q := by
    by_contra h
    have hQ0 : Q = 0 := by omega
    rw [hQ0, zero_mul] at hQ
    have := (hx j₀ hj₀).1.trans ((hx j₀ hj₀).2.trans hQ)
    omega
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ1
  refine packetForm_nonneg_of_riemannHypothesis hRH
    (M := ∑ j ∈ s, |τ j| * Real.exp (Real.log (x j) / 2))
    (l := Real.log x₀) (r := Real.log x₀ + Real.log Q) ?_ ?_ ?_ ?_
    (integrableOn_levyJump_step hx₀ (fun j hj => (hx j hj).1) τ)
  · exact Finset.measurable_sum _ fun j _ => (measurable_flatPacket _ _).const_mul (τ j)
  · intro u
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_flatPacket_le _ _ _) (abs_nonneg _)
  · intro u hu
    obtain ⟨j, hj, hne⟩ : ∃ j ∈ s, τ j * flatPacket x₀ (x j) u ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hu (Finset.sum_eq_zero hcon)
    have hfp : flatPacket (x₀ : ℝ) ((x j : ℕ) : ℝ) u ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
    have hmem : u ∈ Set.Ioc (Real.log x₀) (Real.log (x j)) := by
      by_contra hnot
      exact hfp (by simp only [flatPacket]; exact Set.indicator_of_notMem hnot _)
    have hxj : ((x j : ℕ) : ℝ) ≤ (Q : ℝ) * x₀ := by exact_mod_cast (hx j hj).2.trans hQ
    have hxj0 : (0 : ℝ) < ((x j : ℕ) : ℝ) := hx₀'.trans_le (by exact_mod_cast (hx j hj).1)
    have hlog : Real.log (x j) ≤ Real.log x₀ + Real.log Q := by
      rw [add_comm, ← Real.log_mul hQ'.ne' hx₀'.ne']
      exact Real.log_le_log hxj0 hxj
    exact ⟨hmem.1.le, hmem.2.trans hlog⟩
  · rw [add_sub_cancel_left]
    exact Real.log_lt_log hQ' (by linarith)

end Step

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
