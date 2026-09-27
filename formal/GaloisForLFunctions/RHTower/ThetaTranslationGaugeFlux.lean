import GaloisForLFunctions.RHTower.ThetaOneSidedBernsteinGauge
import GaloisForLFunctions.RHTower.MobiusThetaNativeMeyerAdmission

/-!
# Real-shift translation gauges of the theta source: flux, Laplace factorization, rate cone

For real coefficients `c_i` and real shifts `s_i` with `∑ |c_i| e^{|s_i|/2} < ∞`, the gauge
`g = ∑ c_i k(· + s_i)` of the completed theta source `k` is continuous, has the Laplace transform
`∫ e^{wx} g = M(w) XiC(iw)` with `M(w) = ∑ c_i e^{-w s_i}` on the closed critical strip, and its
normalized critical flux is the Gaussian atom sum

`b_g(t) = ∑_{i,n} 2π n² e^{5 s_i/2} c_i e^{-π n² e^{2 s_i} t}`.

* **Grouped Bernstein criterion.**  An absolutely convergent exponential sum is completely
  monotone iff its total coefficient at every rate is nonnegative.
* **Rate cone.**  `b_g` is completely monotone iff for every `r > 0` the rate coefficient
  `∑_{i : r e^{-s_i} ∈ ℕ} c_i e^{s_i/2}` is nonnegative.
* **Zero transfer.**  Where `M(w₀) ≠ 0`, `|Re w₀| < 1/2`, the Mellin transform of `g` has the
  same analytic order at `w₀` as that of `k`.
-/

open MeasureTheory Set Filter Topology Complex
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-! ## Grouped exponential sums -/

theorem grouped_mul_exp {ι : Type*} (c lam : ι → ℝ) (μ t : ℝ) :
    (∑' i, if lam i = μ then c i else 0) * Real.exp (-μ * t) =
      ∑' i, if lam i = μ then c i * Real.exp (-lam i * t) else 0 := by
  rw [← tsum_mul_right]
  refine tsum_congr fun i => ?_
  split_ifs with h
  · rw [h]
  · rw [zero_mul]

theorem hasSum_grouped_exp {ι : Type*} (c lam : ι → ℝ) {t : ℝ}
    (habs : Summable fun i => |c i| * Real.exp (-lam i * t)) :
    HasSum (fun μ : ℝ => (∑' i, if lam i = μ then c i else 0) * Real.exp (-μ * t))
      (∑' i, c i * Real.exp (-lam i * t)) := by
  have hs : Summable fun i => c i * Real.exp (-lam i * t) :=
    Summable.of_norm (habs.congr fun i => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)])
  refine (hs.hasSum.tsum_fiberwise lam).congr_fun fun μ => ?_
  rw [grouped_mul_exp, tsum_subtype (lam ⁻¹' {μ}) (fun i => c i * Real.exp (-lam i * t))]
  refine tsum_congr fun i => ?_
  by_cases h : lam i = μ
  · rw [if_pos h, Set.indicator_of_mem (by simpa using h)]
  · rw [if_neg h, Set.indicator_of_notMem (by simpa using h)]

theorem summable_grouped_exp {ι : Type*} (c lam : ι → ℝ) {t : ℝ}
    (habs : Summable fun i => |c i| * Real.exp (-lam i * t)) :
    Summable fun μ : ℝ => |∑' i, if lam i = μ then c i else 0| * Real.exp (-μ * t) := by
  have h := (habs.hasSum.tsum_fiberwise lam).summable
  refine Summable.of_nonneg_of_le (fun μ => by positivity) (fun μ => ?_) h
  have hind : ∀ i, |if lam i = μ then c i * Real.exp (-lam i * t) else 0| =
      (lam ⁻¹' {μ}).indicator (fun i => |c i| * Real.exp (-lam i * t)) i := by
    intro i
    by_cases h : lam i = μ
    · rw [if_pos h, Set.indicator_of_mem (by simpa using h), abs_mul, abs_of_pos (Real.exp_pos _)]
    · rw [if_neg h, Set.indicator_of_notMem (by simpa using h), abs_zero]
  have hs : Summable fun i => ‖if lam i = μ then c i * Real.exp (-lam i * t) else 0‖ :=
    (habs.indicator (lam ⁻¹' {μ})).congr fun i => by rw [Real.norm_eq_abs, hind]
  rw [← abs_of_pos (Real.exp_pos (-μ * t)), ← abs_mul, grouped_mul_exp,
    tsum_subtype (lam ⁻¹' {μ}) (fun i => |c i| * Real.exp (-lam i * t))]
  calc |∑' i, if lam i = μ then c i * Real.exp (-lam i * t) else 0|
      ≤ ∑' i, ‖if lam i = μ then c i * Real.exp (-lam i * t) else 0‖ := by
        rw [← Real.norm_eq_abs]; exact norm_tsum_le_tsum_norm hs
    _ = _ := tsum_congr fun i => by rw [Real.norm_eq_abs, hind]

theorem grouped_eq_zero_of_neg {ι : Type*} (c lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i) {μ : ℝ}
    (hμ : μ < 0) : (∑' i, if lam i = μ then c i else 0) = 0 := by
  refine (tsum_congr fun i => ?_).trans tsum_zero
  rw [if_neg (fun h => by have := hlam i; linarith)]

/-- **Grouped Bernstein criterion, sufficiency.**  An absolutely convergent exponential sum whose
total coefficient at every rate is nonnegative is completely monotone. -/
theorem completelyMonotoneOn_tsum_exp_of_grouped_nonneg {ι : Type*} (c lam : ι → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hsum : ∀ t, 0 < t → Summable fun i => |c i| * Real.exp (-lam i * t))
    (hW : ∀ μ, 0 ≤ ∑' i, if lam i = μ then c i else 0) :
    CompletelyMonotoneOn (fun t => ∑' i, c i * Real.exp (-lam i * t)) := by
  have hWe : ∀ μ t, (∑' i, if lam i = μ then c i else 0) * Real.exp (-max μ 0 * t) =
      (∑' i, if lam i = μ then c i else 0) * Real.exp (-μ * t) := by
    intro μ t
    rcases le_or_gt 0 μ with h | h
    · rw [max_eq_left h]
    · rw [grouped_eq_zero_of_neg c lam hlam h, zero_mul, zero_mul]
  have hCM := completelyMonotoneOn_tsum_exp (fun μ => ∑' i, if lam i = μ then c i else 0)
    (fun μ => max μ 0) hW (fun μ => le_max_right _ _) (fun t ht => by
      refine Summable.of_norm ((summable_grouped_exp c lam (hsum t ht)).congr fun μ => ?_)
      rw [hWe, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)])
  refine hCM.congr_Ioi fun t ht => ?_
  simp only [hWe]
  exact (hasSum_grouped_exp c lam (hsum t ht)).tsum_eq

/-- **Grouped Bernstein criterion.**  An absolutely convergent exponential sum is completely
monotone on `(0,∞)` iff its total coefficient at every rate is nonnegative. -/
theorem completelyMonotoneOn_tsum_exp_iff_grouped {ι : Type*} [Countable ι] (c lam : ι → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hsum : ∀ t, 0 < t → Summable fun i => |c i| * Real.exp (-lam i * t)) :
    CompletelyMonotoneOn (fun t => ∑' i, c i * Real.exp (-lam i * t)) ↔
      ∀ μ, 0 ≤ ∑' i, if lam i = μ then c i else 0 :=
  ⟨fun h μ => tsum_coeff_nonneg_of_completelyMonotoneOn c lam hlam hsum h μ,
    completelyMonotoneOn_tsum_exp_of_grouped_nonneg c lam hlam hsum⟩

/-! ## Real-shift translation gauges -/

/-- The real-shift translation gauge `∑ c_i k(· + s_i)` of the completed theta source. -/
noncomputable def thetaTranslationGauge {ι : Type*} (c s : ι → ℝ) (x : ℝ) : ℝ :=
  ∑' i, c i * thetaCuspFullSource (x + s i)

theorem exists_abs_thetaCuspFullSource_le_const : ∃ C, ∀ x, |thetaCuspFullSource x| ≤ C := by
  obtain ⟨C, hC⟩ := thetaCuspFullSource_derivative_exp_bound 0 0
  exact ⟨C, fun x => by simpa using hC x⟩

theorem summable_abs_of_gauge {ι : Type*} {c s : ι → ℝ}
    (hc : Summable fun i => |c i| * Real.exp (|s i| / 2)) : Summable fun i => |c i| :=
  hc.of_nonneg_of_le (fun i => abs_nonneg _)
    (fun i => le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (by positivity)))

theorem summable_abs_mul_exp_of_gauge {ι : Type*} {c s : ι → ℝ}
    (hc : Summable fun i => |c i| * Real.exp (|s i| / 2)) {σ : ℝ} (hσ : |σ| ≤ 1 / 2) :
    Summable fun i => |c i| * Real.exp (σ * s i) :=
  hc.of_nonneg_of_le (fun i => by positivity) (fun i => by
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
    calc σ * s i ≤ |σ * s i| := le_abs_self _
      _ = |σ| * |s i| := abs_mul _ _
      _ ≤ 1 / 2 * |s i| := by gcongr
      _ = |s i| / 2 := by ring)

theorem summable_thetaTranslationGauge {ι : Type*} {c s : ι → ℝ} (hc : Summable fun i => |c i|)
    (x : ℝ) : Summable fun i => c i * thetaCuspFullSource (x + s i) := by
  obtain ⟨C, hC⟩ := exists_abs_thetaCuspFullSource_le_const
  exact Summable.of_norm_bounded (hc.mul_right C) fun i => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _)

theorem continuous_thetaTranslationGauge {ι : Type*} {c s : ι → ℝ}
    (hc : Summable fun i => |c i|) : Continuous (thetaTranslationGauge c s) := by
  obtain ⟨C, hC⟩ := exists_abs_thetaCuspFullSource_le_const
  exact continuous_tsum (fun i => continuous_const.mul
      (continuous_thetaCuspFullSource.comp (continuous_id.add continuous_const)))
    (hc.mul_right C) (fun i x => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _))

theorem integral_exp_mul_comp_add_thetaCuspFullSource (w s : ℝ) :
    (∫ x, Real.exp (w * x) * thetaCuspFullSource (x + s)) =
      Real.exp (-(w * s)) * ∫ y, Real.exp (w * y) * thetaCuspFullSource y := by
  have h := integral_exp_mul_comp_sub w (-s) thetaCuspFullSource
  simp only [sub_neg_eq_add] at h
  rw [h, mul_neg]

theorem integrable_exp_mul_comp_add_thetaCuspFullSource (w s : ℝ) :
    Integrable (fun x => Real.exp (w * x) * thetaCuspFullSource (x + s)) := by
  have h := ((integrable_exp_mul_thetaCuspFullSource_real w).comp_add_right s).const_mul
    (Real.exp (-(w * s)))
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only
  rw [← mul_assoc, ← Real.exp_add]
  ring_nf

/-- **Real Laplace factorization of a translation gauge** on the critical strip. -/
theorem integral_exp_mul_thetaTranslationGauge {ι : Type*} [Countable ι] {c s : ι → ℝ}
    (hc : Summable fun i => |c i| * Real.exp (|s i| / 2)) {w : ℝ} (hw : |w| ≤ 1 / 2) :
    Integrable (fun x => Real.exp (w * x) * thetaTranslationGauge c s x) ∧
    (∫ x, Real.exp (w * x) * thetaTranslationGauge c s x) =
      (∑' i, c i * Real.exp (-(w * s i))) *
        ∫ y, Real.exp (w * y) * thetaCuspFullSource y := by
  set K := ∫ y, Real.exp (w * y) * thetaCuspFullSource y
  set F : ι → ℝ → ℝ := fun i x => Real.exp (w * x) * (c i * thetaCuspFullSource (x + s i))
  have hFi : ∀ i, Integrable (F i) := fun i =>
    ((integrable_exp_mul_comp_add_thetaCuspFullSource w (s i)).const_mul (c i)).congr
      (ae_of_all _ fun x => by simp only [F]; ring)
  have hnorm : ∀ i, (∫ x, ‖F i x‖) = |c i| * Real.exp (-(w * s i)) * K := by
    intro i
    have : (fun x => ‖F i x‖) =
        fun x => |c i| * (Real.exp (w * x) * thetaCuspFullSource (x + s i)) := by
      funext x
      simp only [F, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
        abs_of_pos (thetaCuspFullSource_pos_all _)]
      ring
    rw [this, integral_const_mul, integral_exp_mul_comp_add_thetaCuspFullSource]
    ring
  have hsum : Summable fun i => ∫ x, ‖F i x‖ := by
    simp_rw [hnorm]
    exact ((summable_abs_mul_exp_of_gauge hc (σ := -w) (by rwa [abs_neg])).mul_right K).congr
      fun i => by rw [neg_mul]
  have heq : ∀ x, ∑' i, F i x = Real.exp (w * x) * thetaTranslationGauge c s x := by
    intro x
    simp only [F, thetaTranslationGauge]
    rw [tsum_mul_left]
  refine ⟨(integrable_tsum_of_summable_integral_norm hFi hsum).congr (ae_of_all _ heq), ?_⟩
  rw [← funext heq, ← integral_tsum_of_summable_integral_norm hFi hsum, ← tsum_mul_right]
  refine tsum_congr fun i => ?_
  simp only [F]
  simp_rw [← mul_assoc, mul_comm (Real.exp (w * _)) (c i), mul_assoc]
  rw [integral_const_mul, integral_exp_mul_comp_add_thetaCuspFullSource]

/-- **Complex Laplace factorization of a translation gauge** on the closed critical strip:
`∫ e^{wx} g = M(w) · XiC(iw)` with `M(w) = ∑ c_i e^{-w s_i}`. -/
theorem integral_cexp_mul_thetaTranslationGauge {ι : Type*} [Countable ι] {c s : ι → ℝ}
    (hc : Summable fun i => |c i| * Real.exp (|s i| / 2)) {w : ℂ} (hw : |w.re| ≤ 1 / 2) :
    Integrable (fun x : ℝ => Complex.exp (w * x) * (thetaTranslationGauge c s x : ℂ)) ∧
    (∫ x : ℝ, Complex.exp (w * x) * (thetaTranslationGauge c s x : ℂ)) =
      (∑' i, (c i : ℂ) * Complex.exp (-(w * s i))) * XiC (I * w) := by
  set K := ∫ y, Real.exp (w.re * y) * thetaCuspFullSource y
  set F : ι → ℝ → ℂ := fun i x =>
    Complex.exp (w * x) * ((c i : ℂ) * (thetaCuspFullSource (x + s i) : ℂ))
  have hFi : ∀ i, Integrable (F i) := fun i =>
    ((integrable_cexp_mul_comp_add (s i) (integrable_cexp_mul_thetaCuspFullSource w)).const_mul
      (c i : ℂ)).congr (ae_of_all _ fun x => by simp only [F]; ring)
  have hnorm : ∀ i, (∫ x, ‖F i x‖) = |c i| * Real.exp (-(w.re * s i)) * K := by
    intro i
    have : (fun x => ‖F i x‖) =
        fun x => |c i| * (Real.exp (w.re * x) * thetaCuspFullSource (x + s i)) := by
      funext x
      simp only [F, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (thetaCuspFullSource_pos_all _), Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
      ring
    rw [this, integral_const_mul, integral_exp_mul_comp_add_thetaCuspFullSource]
    ring
  have hsum : Summable fun i => ∫ x, ‖F i x‖ := by
    simp_rw [hnorm]
    exact ((summable_abs_mul_exp_of_gauge hc (σ := -w.re) (by rwa [abs_neg])).mul_right K).congr
      fun i => by rw [neg_mul]
  have heq : ∀ x : ℝ, ∑' i, F i x = Complex.exp (w * x) * (thetaTranslationGauge c s x : ℂ) := by
    intro x
    simp only [F, thetaTranslationGauge]
    rw [tsum_mul_left, Complex.ofReal_tsum]
    congr 1
    exact tsum_congr fun i => by push_cast; ring
  refine ⟨(integrable_tsum_of_summable_integral_norm hFi hsum).congr (ae_of_all _ heq), ?_⟩
  rw [← funext heq, ← integral_tsum_of_summable_integral_norm hFi hsum, ← tsum_mul_right]
  refine tsum_congr fun i => ?_
  have h1 := integral_cexp_mul_comp_add w (s i) (fun y => (thetaCuspFullSource y : ℂ))
  have h2 : (∫ x : ℝ, F i x) =
      (c i : ℂ) * ∫ x : ℝ, Complex.exp (w * x) * (thetaCuspFullSource (x + s i) : ℂ) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun x => by simp only [F]; ring)
  rw [h2, h1, integral_cexp_mul_thetaCuspFullSource]
  ring

/-! ## Flux of a translation gauge -/

theorem integrable_exp_half_mul_thetaTranslationGauge {ι : Type*} [Countable ι] {c s : ι → ℝ}
    (hc : Summable fun i => |c i| * Real.exp (|s i| / 2)) :
    Integrable (fun x => Real.exp (x / 2) * thetaTranslationGauge c s x) :=
  (integral_exp_mul_thetaTranslationGauge hc (w := 1 / 2) (by norm_num [abs_of_pos])).1.congr
    (ae_of_all _ fun x => by simp only; ring_nf)

theorem thetaFluxSource_thetaTranslationGauge {ι : Type*} [Countable ι] {c s : ι → ℝ}
    (hc : Summable fun i => |c i| * Real.exp (|s i| / 2)) :
    ThetaFluxSource (thetaTranslationGauge c s) :=
  ⟨continuous_thetaTranslationGauge (summable_abs_of_gauge hc),
    fun _ => (integrable_exp_half_mul_thetaTranslationGauge hc).integrableOn⟩

theorem integrable_exp_half_mul_thetaCuspFullSource :
    Integrable (fun x => Real.exp (x / 2) * thetaCuspFullSource x) :=
  (integrable_exp_mul_thetaCuspFullSource_real (1 / 2)).congr
    (ae_of_all _ fun x => by simp only; ring_nf)

theorem thetaNormalizedFlux_thetaCuspFullSource_nonneg {u : ℝ} (hu : 0 < u) :
    0 ≤ thetaNormalizedFlux thetaCuspFullSource u := by
  rw [thetaNormalizedFlux_thetaCuspFullSource hu]
  exact tsum_nonneg fun n => by positivity

/-- The theta flux is at most `u^{-3/2}/2`, since the whole half-density moment is `1/2`. -/
theorem thetaNormalizedFlux_thetaCuspFullSource_le {u : ℝ} (hu : 0 < u) :
    thetaNormalizedFlux thetaCuspFullSource u ≤ u ^ (-(3 / 2 : ℝ)) / 2 := by
  unfold thetaNormalizedFlux
  have h1 : (∫ x in Ici (Real.log u / 2), Real.exp (x / 2) * thetaCuspFullSource x) ≤ 1 / 2 := by
    calc _ ≤ ∫ x, Real.exp (x / 2) * thetaCuspFullSource x :=
          setIntegral_le_integral integrable_exp_half_mul_thetaCuspFullSource
            (ae_of_all _ fun x => mul_nonneg (Real.exp_pos _).le (thetaCuspFullSource_pos_all x).le)
      _ = 1 / 2 := by
          rw [← integral_exp_half_mul_thetaCuspFullSource_eq_half]
          congr 1
          funext x
          ring_nf
  calc u ^ (-(3 / 2 : ℝ)) * ∫ x in Ici (Real.log u / 2), Real.exp (x / 2) * thetaCuspFullSource x
      ≤ u ^ (-(3 / 2 : ℝ)) * (1 / 2) := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hu.le _)
    _ = u ^ (-(3 / 2 : ℝ)) / 2 := by ring

/-- **Flux of a translation gauge**: `b_g(t) = ∑ c_i e^{5 s_i/2} b_k(e^{2 s_i} t)`. -/
theorem thetaNormalizedFlux_thetaTranslationGauge {ι : Type*} [Countable ι] {c s : ι → ℝ}
    (hc : Summable fun i => |c i| * Real.exp (|s i| / 2)) {t : ℝ} (ht : 0 < t) :
    thetaNormalizedFlux (thetaTranslationGauge c s) t =
      ∑' i, c i * (Real.exp (5 * s i / 2) *
        thetaNormalizedFlux thetaCuspFullSource (Real.exp (2 * s i) * t)) := by
  simp_rw [← thetaNormalizedFlux_comp_add _ _ ht]
  set F : ι → ℝ → ℝ := fun i x => Real.exp (x / 2) * (c i * thetaCuspFullSource (x + s i))
  have hFfull : ∀ i, Integrable (F i) := fun i =>
    ((integrable_exp_mul_comp_add_thetaCuspFullSource (1 / 2) (s i)).const_mul (c i)).congr
      (ae_of_all _ fun x => by simp only [F]; ring_nf)
  have hFi : ∀ i, Integrable (F i) (volume.restrict (Ici (Real.log t / 2))) :=
    fun i => (hFfull i).integrableOn
  have hnorm : ∀ i, (∫ x, ‖F i x‖) = |c i| * Real.exp (-(1 / 2) * s i) *
      ∫ y, Real.exp (1 / 2 * y) * thetaCuspFullSource y := by
    intro i
    have : (fun x => ‖F i x‖) =
        fun x => |c i| * (Real.exp (1 / 2 * x) * thetaCuspFullSource (x + s i)) := by
      funext x
      simp only [F, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
        abs_of_pos (thetaCuspFullSource_pos_all _)]
      ring_nf
    rw [this, integral_const_mul, integral_exp_mul_comp_add_thetaCuspFullSource, neg_mul]
    ring
  have hsum : Summable fun i => ∫ x in Ici (Real.log t / 2), ‖F i x‖ := by
    refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun x => norm_nonneg _)
      (fun i => ?_) ((summable_abs_mul_exp_of_gauge hc (σ := -(1 / 2))
        (by norm_num [abs_of_pos])).mul_right
          (∫ y, Real.exp (1 / 2 * y) * thetaCuspFullSource y))
    rw [← hnorm i]
    exact setIntegral_le_integral (hFfull i).norm (ae_of_all _ fun x => norm_nonneg _)
  have heq : (fun x => Real.exp (x / 2) * thetaTranslationGauge c s x) = fun x => ∑' i, F i x := by
    funext x
    simp only [F, thetaTranslationGauge]
    rw [tsum_mul_left]
  simp only [thetaNormalizedFlux]
  rw [heq, ← integral_tsum_of_summable_integral_norm hFi hsum, ← tsum_mul_left]
  refine tsum_congr fun i => ?_
  simp only [F]
  simp_rw [mul_left_comm (Real.exp (_ / 2)) (c i)]
  rw [integral_const_mul]
  ring

/-! ## Gaussian atoms of a translation gauge -/

/-- Rate `π n² e^{2 s_i}` of the atom `(i,n)`. -/
noncomputable def thetaGaugeAtomRate {ι : Type*} (s : ι → ℝ) (p : ι × ℕ) : ℝ :=
  Real.pi * (p.2 : ℝ) ^ 2 * Real.exp (2 * s p.1)

/-- Weight `2π n² e^{5 s_i/2} c_i` of the atom `(i,n)`. -/
noncomputable def thetaGaugeAtomWeight {ι : Type*} (c s : ι → ℝ) (p : ι × ℕ) : ℝ :=
  2 * Real.pi * (p.2 : ℝ) ^ 2 * Real.exp (5 * s p.1 / 2) * c p.1

theorem thetaGaugeAtomRate_nonneg {ι : Type*} (s : ι → ℝ) (p : ι × ℕ) :
    0 ≤ thetaGaugeAtomRate s p := by
  unfold thetaGaugeAtomRate
  positivity

theorem hasSum_thetaGaugeAtom_fiber {ι : Type*} (c s : ι → ℝ) (i : ι) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => thetaGaugeAtomWeight c s (i, n) *
        Real.exp (-thetaGaugeAtomRate s (i, n) * t))
      (c i * (Real.exp (5 * s i / 2) *
        thetaNormalizedFlux thetaCuspFullSource (Real.exp (2 * s i) * t))) := by
  have hu : 0 < Real.exp (2 * s i) * t := mul_pos (Real.exp_pos _) ht
  have hS := (summable_pow_mul_exp_neg_nat_sq 2 (sigma := Real.pi * (Real.exp (2 * s i) * t))
    (by positivity)).mul_left (2 * Real.pi * Real.exp (5 * s i / 2) * c i)
  have hf : (fun n : ℕ => thetaGaugeAtomWeight c s (i, n) *
      Real.exp (-thetaGaugeAtomRate s (i, n) * t)) = fun n : ℕ =>
        2 * Real.pi * Real.exp (5 * s i / 2) * c i *
          ((n : ℝ) ^ 2 * Real.exp (-(Real.pi * (Real.exp (2 * s i) * t)) * (n : ℝ) ^ 2)) := by
    funext n
    simp only [thetaGaugeAtomWeight, thetaGaugeAtomRate]
    rw [show -(Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * s i)) * t =
      -(Real.pi * (Real.exp (2 * s i) * t)) * (n : ℝ) ^ 2 by ring]
    ring
  rw [hf]
  have : (∑' n : ℕ, 2 * Real.pi * (n : ℝ) ^ 2 *
      Real.exp (-Real.pi * (n : ℝ) ^ 2 * (Real.exp (2 * s i) * t))) =
      2 * Real.pi * ∑' n : ℕ, (n : ℝ) ^ 2 *
        Real.exp (-(Real.pi * (Real.exp (2 * s i) * t)) * (n : ℝ) ^ 2) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [show -Real.pi * (n : ℝ) ^ 2 * (Real.exp (2 * s i) * t) =
      -(Real.pi * (Real.exp (2 * s i) * t)) * (n : ℝ) ^ 2 by ring]
    ring
  have hv : c i * (Real.exp (5 * s i / 2) *
      thetaNormalizedFlux thetaCuspFullSource (Real.exp (2 * s i) * t)) =
      ∑' n : ℕ, 2 * Real.pi * Real.exp (5 * s i / 2) * c i *
        ((n : ℝ) ^ 2 * Real.exp (-(Real.pi * (Real.exp (2 * s i) * t)) * (n : ℝ) ^ 2)) := by
    rw [thetaNormalizedFlux_thetaCuspFullSource hu, tsum_mul_left, this]
    ring
  rw [hv]
  exact hS.hasSum

theorem abs_thetaGaugeAtomWeight {ι : Type*} (c s : ι → ℝ) (p : ι × ℕ) :
    |thetaGaugeAtomWeight c s p| = thetaGaugeAtomWeight (fun i => |c i|) s p := by
  unfold thetaGaugeAtomWeight
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi * (p.2 : ℝ) ^ 2 *
    Real.exp (5 * s p.1 / 2))]

theorem summable_abs_thetaGaugeAtom {ι : Type*} {c s : ι → ℝ}
    (hc : Summable fun i => |c i| * Real.exp (|s i| / 2)) {t : ℝ} (ht : 0 < t) :
    Summable fun p : ι × ℕ => |thetaGaugeAtomWeight c s p| *
      Real.exp (-thetaGaugeAtomRate s p * t) := by
  simp_rw [abs_thetaGaugeAtomWeight]
  have hfib := fun i => hasSum_thetaGaugeAtom_fiber (fun i => |c i|) s i ht
  refine (summable_prod_of_nonneg (fun p => ?_)).mpr ⟨fun i => (hfib i).summable, ?_⟩
  · rw [← abs_thetaGaugeAtomWeight]
    positivity
  · simp_rw [fun i => (hfib i).tsum_eq]
    refine Summable.of_nonneg_of_le (fun i => mul_nonneg (abs_nonneg _) (mul_nonneg
      (Real.exp_pos _).le (thetaNormalizedFlux_thetaCuspFullSource_nonneg
        (mul_pos (Real.exp_pos _) ht)))) (fun i => ?_)
      ((summable_abs_mul_exp_of_gauge hc (σ := -(1 / 2)) (by norm_num [abs_of_pos])).mul_right
        (t ^ (-(3 / 2 : ℝ)) / 2))
    have hb := thetaNormalizedFlux_thetaCuspFullSource_le (mul_pos (Real.exp_pos (2 * s i)) ht)
    rw [Real.mul_rpow (Real.exp_pos _).le ht.le, ← Real.exp_mul] at hb
    have he : Real.exp (5 * s i / 2) * Real.exp (2 * s i * (-(3 / 2 : ℝ))) =
        Real.exp (-(1 / 2) * s i) := by
      rw [← Real.exp_add]; ring_nf
    calc |c i| * (Real.exp (5 * s i / 2) *
          thetaNormalizedFlux thetaCuspFullSource (Real.exp (2 * s i) * t))
        ≤ |c i| * (Real.exp (5 * s i / 2) *
          (Real.exp (2 * s i * (-(3 / 2 : ℝ))) * t ^ (-(3 / 2 : ℝ)) / 2)) := by
          gcongr
      _ = |c i| * Real.exp (-(1 / 2) * s i) * (t ^ (-(3 / 2 : ℝ)) / 2) := by
          rw [← he]; ring

/-- **Gaussian atom expansion of the gauge flux.** -/
theorem thetaNormalizedFlux_thetaTranslationGauge_eq_tsum {ι : Type*} [Countable ι]
    {c s : ι → ℝ} (hc : Summable fun i => |c i| * Real.exp (|s i| / 2)) {t : ℝ} (ht : 0 < t) :
    thetaNormalizedFlux (thetaTranslationGauge c s) t =
      ∑' p : ι × ℕ, thetaGaugeAtomWeight c s p * Real.exp (-thetaGaugeAtomRate s p * t) := by
  have hs : Summable fun p : ι × ℕ => thetaGaugeAtomWeight c s p *
      Real.exp (-thetaGaugeAtomRate s p * t) :=
    Summable.of_norm ((summable_abs_thetaGaugeAtom hc ht).congr fun p => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)])
  rw [thetaNormalizedFlux_thetaTranslationGauge hc ht, hs.tsum_prod]
  exact tsum_congr fun i => (hasSum_thetaGaugeAtom_fiber c s i ht).tsum_eq.symm

/-- **Bernstein criterion for translation gauges, atom form.** -/
theorem completelyMonotoneOn_thetaNormalizedFlux_gauge_iff {ι : Type*} [Countable ι]
    {c s : ι → ℝ} (hc : Summable fun i => |c i| * Real.exp (|s i| / 2)) :
    CompletelyMonotoneOn (thetaNormalizedFlux (thetaTranslationGauge c s)) ↔
      ∀ μ, 0 ≤ ∑' p : ι × ℕ,
        if thetaGaugeAtomRate s p = μ then thetaGaugeAtomWeight c s p else 0 := by
  have hEq : EqOn (thetaNormalizedFlux (thetaTranslationGauge c s))
      (fun t => ∑' p : ι × ℕ, thetaGaugeAtomWeight c s p *
        Real.exp (-thetaGaugeAtomRate s p * t)) (Ioi 0) :=
    fun t ht => thetaNormalizedFlux_thetaTranslationGauge_eq_tsum hc ht
  rw [← completelyMonotoneOn_tsum_exp_iff_grouped _ _ (thetaGaugeAtomRate_nonneg s)
    (fun t ht => summable_abs_thetaGaugeAtom hc ht)]
  exact ⟨fun h => h.congr_Ioi hEq, fun h => h.congr_Ioi hEq.symm⟩

/-! ## Rate coefficients -/

open Classical in
/-- The total translation coefficient `∑_{i : r e^{-s_i} ∈ ℕ} c_i e^{s_i/2}` reaching the
Gaussian rate `π r²`. -/
noncomputable def thetaGaugeRateCoeff {ι : Type*} (c s : ι → ℝ) (r : ℝ) : ℝ :=
  ∑' i, if ∃ n : ℕ, (n : ℝ) * Real.exp (s i) = r then c i * Real.exp (s i / 2) else 0

theorem thetaGaugeAtomRate_eq_iff {ι : Type*} (s : ι → ℝ) (p : ι × ℕ) {r : ℝ} (hr : 0 < r) :
    thetaGaugeAtomRate s p = Real.pi * r ^ 2 ↔ (p.2 : ℝ) * Real.exp (s p.1) = r := by
  unfold thetaGaugeAtomRate
  rw [show Real.pi * (p.2 : ℝ) ^ 2 * Real.exp (2 * s p.1) =
      Real.pi * ((p.2 : ℝ) * Real.exp (s p.1)) ^ 2 by
    rw [show (2 : ℝ) * s p.1 = s p.1 + s p.1 by ring, Real.exp_add]; ring,
    mul_right_inj' Real.pi_ne_zero, sq_eq_sq₀ (by positivity) hr.le]

theorem thetaGaugeAtomWeight_of_rate {ι : Type*} (c s : ι → ℝ) (p : ι × ℕ) {r : ℝ}
    (hp : (p.2 : ℝ) * Real.exp (s p.1) = r) :
    thetaGaugeAtomWeight c s p = 2 * Real.pi * r ^ 2 * (c p.1 * Real.exp (s p.1 / 2)) := by
  rw [← hp]
  unfold thetaGaugeAtomWeight
  rw [show 5 * s p.1 / 2 = s p.1 + s p.1 + s p.1 / 2 by ring, Real.exp_add, Real.exp_add]
  ring

/-- The grouped atom weight at the rate `π r²` is `2π r²` times the rate coefficient. -/
theorem grouped_thetaGaugeAtom_eq {ι : Type*} (c s : ι → ℝ) {r : ℝ} (hr : 0 < r) :
    (∑' p : ι × ℕ, if thetaGaugeAtomRate s p = Real.pi * r ^ 2 then
        thetaGaugeAtomWeight c s p else 0) =
      2 * Real.pi * r ^ 2 * thetaGaugeRateCoeff c s r := by
  unfold thetaGaugeRateCoeff
  rw [← tsum_mul_left]
  symm
  refine tsum_eq_tsum_of_ne_zero_bij (fun x => x.1.1) ?_ ?_ ?_
  · rintro ⟨⟨i, n⟩, hx⟩ ⟨⟨j, m⟩, hy⟩ hij
    simp only at hij
    subst hij
    have hx' : (n : ℝ) * Real.exp (s i) = r := by
      by_contra h
      exact hx (by simp only; rw [if_neg (by rwa [thetaGaugeAtomRate_eq_iff s _ hr])])
    have hy' : (m : ℝ) * Real.exp (s i) = r := by
      by_contra h
      exact hy (by simp only; rw [if_neg (by rwa [thetaGaugeAtomRate_eq_iff s _ hr])])
    have : (n : ℝ) = m := mul_right_cancel₀ (Real.exp_pos _).ne' (hx'.trans hy'.symm)
    obtain rfl : n = m := Nat.cast_inj.mp this
    rfl
  · intro i hi
    have hex : ∃ n : ℕ, (n : ℝ) * Real.exp (s i) = r := by
      by_contra h
      exact hi (by simp only; rw [if_neg h, mul_zero])
    obtain ⟨n, hn⟩ := hex
    refine ⟨⟨(i, n), ?_⟩, rfl⟩
    have hne := hi
    simp only [Function.mem_support, ne_eq] at hne ⊢
    rw [if_pos ((thetaGaugeAtomRate_eq_iff s (i, n) hr).mpr hn),
      thetaGaugeAtomWeight_of_rate c s (i, n) hn]
    rwa [if_pos ⟨n, hn⟩] at hne
  · rintro ⟨⟨i, n⟩, hx⟩
    have hx' : (n : ℝ) * Real.exp (s i) = r := by
      by_contra h
      exact hx (by simp only; rw [if_neg (by rwa [thetaGaugeAtomRate_eq_iff s _ hr])])
    simp only
    rw [if_pos ((thetaGaugeAtomRate_eq_iff s (i, n) hr).mpr hx'), if_pos ⟨n, hx'⟩,
      thetaGaugeAtomWeight_of_rate c s (i, n) hx']

theorem grouped_thetaGaugeAtom_eq_zero_of_nonpos {ι : Type*} (c s : ι → ℝ) {μ : ℝ}
    (hμ : μ ≤ 0) :
    (∑' p : ι × ℕ, if thetaGaugeAtomRate s p = μ then thetaGaugeAtomWeight c s p else 0) = 0 := by
  refine (tsum_congr fun p => ?_).trans tsum_zero
  split_ifs with h
  · have h0 : thetaGaugeAtomRate s p = 0 := le_antisymm (h ▸ hμ) (thetaGaugeAtomRate_nonneg s p)
    unfold thetaGaugeAtomRate at h0
    have hn : (p.2 : ℝ) = 0 := by
      have := mul_eq_zero.mp h0
      rcases this with h1 | h1
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · exact absurd h2 Real.pi_ne_zero
        · exact pow_eq_zero_iff (two_ne_zero) |>.mp h2
      · exact absurd h1 (Real.exp_pos _).ne'
    unfold thetaGaugeAtomWeight
    rw [hn]
    ring
  · rfl

/-- **Bernstein criterion for translation gauges.**  The flux of `∑ c_i k(· + s_i)` is completely
monotone iff every rate coefficient `∑_{i : r e^{-s_i} ∈ ℕ} c_i e^{s_i/2}`, `r > 0`, is
nonnegative. -/
theorem completelyMonotoneOn_thetaNormalizedFlux_gauge_iff_rateCoeff {ι : Type*} [Countable ι]
    {c s : ι → ℝ} (hc : Summable fun i => |c i| * Real.exp (|s i| / 2)) :
    CompletelyMonotoneOn (thetaNormalizedFlux (thetaTranslationGauge c s)) ↔
      ∀ r, 0 < r → 0 ≤ thetaGaugeRateCoeff c s r := by
  rw [completelyMonotoneOn_thetaNormalizedFlux_gauge_iff hc]
  constructor
  · intro h r hr
    have := h (Real.pi * r ^ 2)
    rw [grouped_thetaGaugeAtom_eq c s hr] at this
    exact (mul_nonneg_iff_of_pos_left (by positivity)).mp this
  · intro h μ
    rcases le_or_gt μ 0 with hμ | hμ
    · rw [grouped_thetaGaugeAtom_eq_zero_of_nonpos c s hμ]
    · have hq : 0 < μ / Real.pi := div_pos hμ Real.pi_pos
      have hr : 0 < Real.sqrt (μ / Real.pi) := Real.sqrt_pos.mpr hq
      have hμr : μ = Real.pi * Real.sqrt (μ / Real.pi) ^ 2 := by
        rw [Real.sq_sqrt hq.le]
        field_simp
      rw [hμr, grouped_thetaGaugeAtom_eq c s hr]
      exact mul_nonneg (by positivity) (h _ hr)

/-! ## The Mellin multiplier -/

/-- The Mellin multiplier `M(w) = ∑ c_i e^{-w s_i}` of a translation gauge. -/
noncomputable def thetaGaugeMultiplier {ι : Type*} (c s : ι → ℝ) (w : ℂ) : ℂ :=
  ∑' i, (c i : ℂ) * Complex.exp (-(w * s i))

theorem norm_thetaGaugeMultiplier_term {ι : Type*} (c s : ι → ℝ) (i : ι) (w : ℂ) :
    ‖(c i : ℂ) * Complex.exp (-(w * s i))‖ = |c i| * Real.exp (-(w.re * s i)) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  simp

theorem isOpen_abs_re_lt_half : IsOpen {w : ℂ | |w.re| < 1 / 2} :=
  isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const

theorem differentiableOn_thetaGaugeMultiplier {ι : Type*} {c s : ι → ℝ}
    (hc : Summable fun i => |c i| * Real.exp (|s i| / 2)) :
    DifferentiableOn ℂ (thetaGaugeMultiplier c s) {w : ℂ | |w.re| < 1 / 2} := by
  refine Complex.differentiableOn_tsum_of_summable_norm hc (fun i => ?_) isOpen_abs_re_lt_half
    (fun i w hw => ?_)
  · exact (Differentiable.const_mul (Differentiable.cexp
      ((differentiable_id.mul_const _).neg)) _).differentiableOn
  · rw [norm_thetaGaugeMultiplier_term]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
    have hw' : |w.re| ≤ 1 / 2 := le_of_lt hw
    calc -(w.re * s i) ≤ |w.re * s i| := neg_le_abs _
      _ = |w.re| * |s i| := abs_mul _ _
      _ ≤ 1 / 2 * |s i| := by gcongr
      _ = |s i| / 2 := by ring

/-- **Zero divisor transfer.**  Where the multiplier does not vanish inside the open critical
strip, the Mellin transform of the gauge has the same analytic order as that of `k`. -/
theorem analyticOrderAt_integral_cexp_mul_thetaTranslationGauge {ι : Type*} [Countable ι]
    {c s : ι → ℝ} (hc : Summable fun i => |c i| * Real.exp (|s i| / 2)) {w₀ : ℂ}
    (hw₀ : |w₀.re| < 1 / 2) (hM : thetaGaugeMultiplier c s w₀ ≠ 0) :
    analyticOrderAt (fun w : ℂ => ∫ x : ℝ,
        Complex.exp (w * x) * (thetaTranslationGauge c s x : ℂ)) w₀ =
      analyticOrderAt (fun w : ℂ => XiC (I * w)) w₀ := by
  have hev : (fun w : ℂ => ∫ x : ℝ, Complex.exp (w * x) * (thetaTranslationGauge c s x : ℂ))
      =ᶠ[𝓝 w₀] (fun w : ℂ => XiC (I * w)) * thetaGaugeMultiplier c s := by
    filter_upwards [isOpen_abs_re_lt_half.mem_nhds hw₀] with w hw
    rw [(integral_cexp_mul_thetaTranslationGauge hc (le_of_lt hw)).2, Pi.mul_apply, mul_comm]
    rfl
  have hXi : AnalyticAt ℂ (fun w : ℂ => XiC (I * w)) w₀ :=
    (XiC_differentiable.comp (differentiable_id.const_mul I)).analyticAt w₀
  have hMa : AnalyticAt ℂ (thetaGaugeMultiplier c s) w₀ :=
    (differentiableOn_thetaGaugeMultiplier hc).analyticAt (isOpen_abs_re_lt_half.mem_nhds hw₀)
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul hXi hMa,
    analyticOrderAt_eq_zero.mpr (Or.inr hM), add_zero]

end RHTower
