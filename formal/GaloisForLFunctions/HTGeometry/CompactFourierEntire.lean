import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# The Fourier transform of a compactly supported amplitude is entire

For a continuous amplitude on a compact interval the frequency variable may be moved into the complex
plane:

```text
F(z) = ∫_a^b f(x) exp (i z x) dx
```

is differentiable at every `z`, because on the interval the derivative of the integrand is dominated
by the constant `sup|f| · max(|a|,|b|) · exp((‖z‖+1) max(|a|,|b|))`.  So `F` is entire, and the identity
theorem applies to it: if `F` vanishes on a nondegenerate interval of *real* frequencies, its zero set
has an accumulation point, hence `F` vanishes on all of `ℂ`.

This is the analytic half of the qualitative uncertainty principle — a compactly supported amplitude
cannot have a Fourier transform that vanishes on an interval unless it vanishes altogether — and it is
absent from mathlib, which has no Paley–Wiener theory.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory intervalIntegral

/-- The Fourier transform of an amplitude over a compact interval, at a complex frequency. -/
def compactFourier (f : ℝ → ℂ) (a b : ℝ) (z : ℂ) : ℂ :=
  ∫ x in a..b, f x * Complex.exp (Complex.I * (z * (x : ℂ)))

theorem continuous_compactFourier_integrand {f : ℝ → ℂ} (hf : Continuous f) (z : ℂ) :
    Continuous fun x : ℝ => f x * Complex.exp (Complex.I * (z * (x : ℂ))) := by
  fun_prop

theorem continuous_compactFourier_derivIntegrand {f : ℝ → ℂ} (hf : Continuous f) (z : ℂ) :
    Continuous fun x : ℝ =>
      f x * (Complex.I * (x : ℂ)) * Complex.exp (Complex.I * (z * (x : ℂ))) := by
  fun_prop

/-- On the integration interval the variable is bounded by the larger endpoint modulus. -/
theorem abs_le_max_abs_of_mem_uIoc {a b x : ℝ} (hx : x ∈ Set.uIoc a b) : |x| ≤ max |a| |b| := by
  rcases Set.mem_uIoc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_le]
    exact ⟨by linarith [neg_abs_le a, le_max_left |a| |b|],
      by linarith [le_abs_self b, le_max_right |a| |b|]⟩
  · rw [abs_le]
    exact ⟨by linarith [neg_abs_le b, le_max_right |a| |b|],
      by linarith [le_abs_self a, le_max_left |a| |b|]⟩

/-- The pointwise derivative of the integrand in the frequency. -/
theorem hasDerivAt_compactFourier_integrand (f : ℝ → ℂ) (x : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => f x * Complex.exp (Complex.I * (w * (x : ℂ))))
      (f x * (Complex.I * (x : ℂ)) * Complex.exp (Complex.I * (z * (x : ℂ)))) z := by
  have h0 : HasDerivAt (fun w : ℂ => w * (x : ℂ)) ((x : ℂ)) z := by
    simpa using (hasDerivAt_id z).mul_const ((x : ℂ))
  have h1 : HasDerivAt (fun w : ℂ => Complex.I * (w * (x : ℂ))) (Complex.I * (x : ℂ)) z :=
    h0.const_mul Complex.I
  have h2 := h1.cexp
  have h3 := h2.const_mul (f x)
  refine h3.congr_deriv ?_
  ring

/-- **Differentiation under a compact Fourier integral in the frequency.**  The derivative is the
integral of the differentiated integrand, dominated on the interval by a constant. -/
theorem hasDerivAt_compactFourier {f : ℝ → ℂ} (hf : Continuous f) (a b : ℝ) (z₀ : ℂ) :
    HasDerivAt (compactFourier f a b)
      (∫ x in a..b, f x * (Complex.I * (x : ℂ)) * Complex.exp (Complex.I * (z₀ * (x : ℂ)))) z₀ := by
  obtain ⟨M, hM⟩ := (isCompact_uIcc (a := a) (b := b)).exists_bound_of_continuousOn
    hf.continuousOn
  set R : ℝ := max |a| |b| with hR
  have hRnonneg : 0 ≤ R := le_trans (abs_nonneg a) (le_max_left _ _)
  have hball : Metric.ball z₀ 1 ∈ nhds z₀ := Metric.ball_mem_nhds z₀ one_pos
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w x => f x * Complex.exp (Complex.I * (w * (x : ℂ))))
    (F' := fun w x => f x * (Complex.I * (x : ℂ)) * Complex.exp (Complex.I * (w * (x : ℂ))))
    (bound := fun _ => M * R * Real.exp ((‖z₀‖ + 1) * R)) hball ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Filter.Eventually.of_forall fun w =>
      ((continuous_compactFourier_integrand hf w).aestronglyMeasurable).restrict
  · exact (continuous_compactFourier_integrand hf z₀).intervalIntegrable a b
  · exact ((continuous_compactFourier_derivIntegrand hf z₀).aestronglyMeasurable).restrict
  · filter_upwards with x
    intro hx w hw
    have hxR : |x| ≤ R := abs_le_max_abs_of_mem_uIoc hx
    have hxmem : x ∈ Set.uIcc a b := Set.uIoc_subset_uIcc hx
    have hfx : ‖f x‖ ≤ M := hM x hxmem
    have hMnonneg : 0 ≤ M := le_trans (norm_nonneg _) hfx
    have hwnorm : ‖w‖ ≤ ‖z₀‖ + 1 := by
      have hd : dist w z₀ < 1 := Metric.mem_ball.mp hw
      have := norm_sub_norm_le w z₀
      rw [dist_eq_norm] at hd
      linarith
    have hIx : ‖Complex.I * (x : ℂ)‖ = |x| := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have hnorm : ‖f x * (Complex.I * (x : ℂ)) * Complex.exp (Complex.I * (w * (x : ℂ)))‖
        = ‖f x‖ * |x| * Real.exp ((Complex.I * (w * (x : ℂ))).re) := by
      rw [norm_mul, norm_mul, Complex.norm_exp, hIx]
    rw [hnorm]
    have hre : (Complex.I * (w * (x : ℂ))).re ≤ (‖z₀‖ + 1) * R := by
      have h1 : (Complex.I * (w * (x : ℂ))).re ≤ ‖Complex.I * (w * (x : ℂ))‖ :=
        Complex.re_le_norm _
      have h2 : ‖Complex.I * (w * (x : ℂ))‖ = ‖w‖ * |x| := by
        rw [norm_mul, Complex.norm_I, one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h3 : ‖w‖ * |x| ≤ (‖z₀‖ + 1) * R := by
        have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
        have := abs_nonneg x
        gcongr
      rw [h2] at h1
      linarith
    have hexp : Real.exp ((Complex.I * (w * (x : ℂ))).re) ≤ Real.exp ((‖z₀‖ + 1) * R) :=
      Real.exp_le_exp.mpr hre
    have habs : (0 : ℝ) ≤ |x| := abs_nonneg x
    have hexppos : (0 : ℝ) < Real.exp ((Complex.I * (w * (x : ℂ))).re) := Real.exp_pos _
    calc ‖f x‖ * |x| * Real.exp ((Complex.I * (w * (x : ℂ))).re)
        ≤ M * R * Real.exp ((Complex.I * (w * (x : ℂ))).re) := by gcongr
      _ ≤ M * R * Real.exp ((‖z₀‖ + 1) * R) := by
          have hMR : 0 ≤ M * R := mul_nonneg hMnonneg hRnonneg
          exact mul_le_mul_of_nonneg_left hexp hMR
  · exact intervalIntegrable_const
  · filter_upwards with x
    intro _ w _
    exact hasDerivAt_compactFourier_integrand f x w

/-- **The compact Fourier transform is entire.** -/
theorem differentiable_compactFourier {f : ℝ → ℂ} (hf : Continuous f) (a b : ℝ) :
    Differentiable ℂ (compactFourier f a b) := fun z =>
  (hasDerivAt_compactFourier hf a b z).differentiableAt

/-! ## The identity theorem along the real axis -/

/-- **An entire function vanishing almost everywhere on a nondegenerate real interval vanishes
identically.**  A null set cannot swallow a punctured interval, so every punctured neighbourhood of
the centre still contains a zero, and the zero set is not isolated there. -/
theorem entire_eq_zero_of_ae_vanishing_on_real_interval {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    {t₀ r : ℝ} (hr : 0 < r)
    (h : ∀ᵐ t ∂(volume.restrict (Set.Ioo (t₀ - r) (t₀ + r))), G ((t : ℝ) : ℂ) = 0) (z : ℂ) :
    G z = 0 := by
  have hA : AnalyticOnNhd ℂ G Set.univ := hG.differentiableOn.analyticOnNhd isOpen_univ
  haveI : (nhdsWithin ((t₀ : ℝ) : ℂ) {((t₀ : ℝ) : ℂ)}ᶜ).NeBot := NormedField.nhdsNE_neBot _
  have hnull : (volume.restrict (Set.Ioo (t₀ - r) (t₀ + r))) {t : ℝ | ¬ G ((t : ℝ) : ℂ) = 0} = 0 :=
    MeasureTheory.ae_iff.mp h
  have hfreq : ∃ᶠ w in nhdsWithin ((t₀ : ℝ) : ℂ) {((t₀ : ℝ) : ℂ)}ᶜ, G w = 0 := by
    rw [Filter.frequently_iff]
    intro U hU
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hU
    -- work inside a small punctured interval around the centre
    set δ : ℝ := min (ε / 2) (r / 2) with hδdef
    have hδpos : 0 < δ := lt_min (by positivity) (by positivity)
    have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hδr : δ ≤ r := le_trans (min_le_right _ _) (by linarith)
    have hSsub : Set.Ioo (t₀ - δ) (t₀ + δ) ⊆ Set.Ioo (t₀ - r) (t₀ + r) := by
      intro t ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    -- the punctured interval has positive measure, so it is not contained in the null set
    have hmeas : MeasurableSet (Set.Ioo (t₀ - δ) (t₀ + δ) \ {t₀}) :=
      measurableSet_Ioo.diff (measurableSet_singleton _)
    have hpos : (volume.restrict (Set.Ioo (t₀ - r) (t₀ + r)))
        (Set.Ioo (t₀ - δ) (t₀ + δ) \ {t₀}) ≠ 0 := by
      rw [Measure.restrict_apply hmeas,
        Set.inter_eq_self_of_subset_left (Set.sdiff_subset.trans hSsub),
        measure_sdiff_null (measure_singleton t₀), Real.volume_Ioo]
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      linarith
    have hexists : ∃ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ) \ {t₀}, G ((t : ℝ) : ℂ) = 0 := by
      by_contra hcon
      push Not at hcon
      refine hpos (measure_mono_null (fun t ht => ?_) hnull)
      exact hcon t ht
    obtain ⟨t, ⟨htmem, htne⟩, htzero⟩ := hexists
    refine ⟨((t : ℝ) : ℂ), hsub ⟨?_, ?_⟩, htzero⟩
    · rw [Metric.mem_ball]
      have hdist : dist ((t : ℝ) : ℂ) ((t₀ : ℝ) : ℂ) = |t - t₀| := by
        rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rw [hdist, abs_lt]
      exact ⟨by linarith [htmem.1], by linarith [htmem.2]⟩
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hcontra
      have hreal : t = t₀ := by exact_mod_cast hcontra
      exact htne (by simpa using hreal)
  have hEq := hA.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ _) hfreq
  exact hEq (Set.mem_univ z)

/-- **An entire function vanishing on a nondegenerate real interval vanishes identically.**  The real
points of the interval accumulate at its centre, so the zero set is not isolated there. -/
theorem entire_eq_zero_of_vanishing_on_real_interval {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    {t₀ r : ℝ} (hr : 0 < r) (h : ∀ t : ℝ, |t - t₀| < r → G ((t : ℝ) : ℂ) = 0) (z : ℂ) :
    G z = 0 := by
  refine entire_eq_zero_of_ae_vanishing_on_real_interval (t₀ := t₀) hG hr ?_ z
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => ?_
  refine h t ?_
  rw [abs_lt]
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- **The compact Fourier transform vanishes identically once it vanishes on an interval of real
frequencies.** -/
theorem compactFourier_eq_zero_of_vanishing_on_real_interval {f : ℝ → ℂ} (hf : Continuous f)
    (a b : ℝ) {t₀ r : ℝ} (hr : 0 < r)
    (h : ∀ t : ℝ, |t - t₀| < r → compactFourier f a b ((t : ℝ) : ℂ) = 0) (z : ℂ) :
    compactFourier f a b z = 0 :=
  entire_eq_zero_of_vanishing_on_real_interval (differentiable_compactFourier hf a b) hr h z

end GaloisForLFunctions.HTGeometry

end
