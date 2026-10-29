import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Comparison across exceptional times

A continuous function whose right derivative is controlled on short punctured
forward intervals obeys the integrated bound on the whole interval. No count or
discreteness assumption on exceptional times is needed. Bounded continuous
approximants recover discontinuous dissipation terms under integration.
-/

open Filter Topology Set

namespace GaloisForLFunctions.HTGeometry

/-- A continuous function with nonpositive right derivative is nonincreasing. -/
private theorem le_initial_of_right_derivative_nonpos {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ico a b, ∃ D : ℝ, HasDerivWithinAt f D (Ici x) x ∧ D ≤ 0) :
    f b ≤ f a := by
  apply image_le_of_liminf_slope_right_le_deriv_boundary hf
    (B := fun _ => f a) (B' := fun _ => 0) le_rfl continuousOn_const
    (fun x _ => (hasDerivAt_const x (f a)).hasDerivWithinAt)
    _ (right_mem_Icc.mpr hab)
  intro x hx r hr
  obtain ⟨D, hD, hD0⟩ := hd x hx
  exact hD.liminf_right_slope_le (hD0.trans_lt hr)

/-- Punctured forward intervals suffice for global comparison; no discreteness
or finiteness assumption on exceptional times is required. -/
theorem le_initial_of_forward_intervals {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ico a b, ∃ δ > 0, ∀ s ∈ Ioo x (x + δ), s < b →
      ∃ D : ℝ, HasDerivWithinAt f D (Ici s) s ∧ D ≤ 0) :
    f b ≤ f a := by
  have hclosed : IsClosed ({t | f t ≤ f a} ∩ Icc a b) := by
    rw [Set.inter_comm]
    exact hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hsub := hclosed.Icc_subset_of_forall_mem_nhdsWithin
    (show a ∈ {t | f t ≤ f a} from by change f a ≤ f a; exact le_rfl) (fun x hx => by
      obtain ⟨δ, hδ, hregular⟩ := hd x hx.2
      filter_upwards [Ioo_mem_nhdsGT (show x < min (x + δ) b from
        lt_min (by linarith only [hδ]) hx.2.2)] with z hz
      have hzx : f z ≤ f x := by
        have hcx : ContinuousWithinAt f (Ioi x) x :=
          (hf x ⟨hx.2.1, hx.2.2.le⟩).mono_of_mem_nhdsWithin
            (mem_of_superset (Ioo_mem_nhdsGT hx.2.2) (fun u hu =>
              ⟨hx.2.1.trans hu.1.le, hu.2.le⟩))
        apply ge_of_tendsto hcx.tendsto
        filter_upwards [Ioo_mem_nhdsGT hz.1] with u hu
        apply le_initial_of_right_derivative_nonpos hu.2.le
          (hf.mono (Icc_subset_Icc (hx.2.1.trans hu.1.le) (hz.2.trans_le (min_le_right _ _)).le))
        intro s hs
        exact hregular s ⟨hu.1.trans_le hs.1,
          hs.2.trans (hz.2.trans_le (min_le_left _ _))⟩
          (hs.2.trans (hz.2.trans_le (min_le_right _ _)))
      exact hzx.trans hx.1)
  exact hsub ⟨hab, le_rfl⟩

/-- Continuity removes any regularity requirement at the initial endpoint. -/
theorem le_initial_of_forward_intervals_interior {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, ∃ δ > 0, ∀ s ∈ Ioo x (x + δ), s < b →
      ∃ D : ℝ, HasDerivWithinAt f D (Ici s) s ∧ D ≤ 0) :
    f b ≤ f a := by
  rcases eq_or_lt_of_le hab with heq | hlt
  · rw [heq]
  have hca : ContinuousWithinAt f (Ioi a) a :=
    (hf a ⟨le_rfl, hab⟩).mono_of_mem_nhdsWithin
      (mem_of_superset (Ioo_mem_nhdsGT hlt) Ioo_subset_Icc_self)
  apply ge_of_tendsto hca.tendsto
  filter_upwards [Ioo_mem_nhdsGT hlt] with c hc
  apply le_initial_of_forward_intervals hc.2.le
    (hf.mono (Icc_subset_Icc hc.1.le le_rfl))
  intro x hx
  exact hd x ⟨hc.1.trans_le hx.1, hx.2⟩

/-- An upper derivative estimate on short punctured forward intervals integrates
through exceptional times, provided the function and majorant are continuous. -/
theorem sub_le_integral_of_forward_deriv_le {f B : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (hB : Continuous B)
    (hd : ∀ x ∈ Ioo a b, ∃ δ > 0, ∀ s ∈ Ioo x (x + δ), s < b →
      ∃ D : ℝ, HasDerivWithinAt f D (Ici s) s ∧ D ≤ B s) :
    f b - f a ≤ ∫ s in a..b, B s := by
  let P : ℝ → ℝ := fun x => ∫ s in a..x, B s
  have hP (x : ℝ) : HasDerivAt P (B x) x :=
    intervalIntegral.integral_hasDerivAt_right (hB.intervalIntegrable a x)
      hB.stronglyMeasurable.stronglyMeasurableAtFilter hB.continuousAt
  have hPc : Continuous P := continuous_iff_continuousAt.mpr fun x => (hP x).continuousAt
  have h := le_initial_of_forward_intervals_interior hab (hf.sub hPc.continuousOn) (by
    intro x hx
    obtain ⟨δ, hδ, hreg⟩ := hd x hx
    refine ⟨δ, hδ, ?_⟩
    intro s hs hsb
    obtain ⟨D, hD, hDb⟩ := hreg s hs hsb
    exact ⟨D - B s, hD.sub (hP s).hasDerivWithinAt, sub_nonpos.mpr hDb⟩)
  have h' : f b - (∫ s in a..b, B s) ≤ f a := by
    simpa only [Pi.sub_apply, P, intervalIntegral.integral_same, sub_zero] using h
  linarith only [h']

open MeasureTheory

/-- Bounded continuous approximants converge under integration on a compact time interval. -/
theorem tendsto_intervalIntegral_of_continuous_bounded
    {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {a b K : ℝ} (hab : a ≤ b)
    (hF : ∀ n, Continuous (F n))
    (hbound : ∀ n, ∀ s ∈ Icc a b, |F n s| ≤ K)
    (hlim : ∀ s ∈ Icc a b, Tendsto (fun n => F n s) atTop (𝓝 (f s))) :
    Tendsto (fun n => ∫ s in a..b, F n s) atTop (𝓝 (∫ s in a..b, f s)) := by
  simp only [intervalIntegral.integral_of_le hab]
  apply tendsto_integral_of_dominated_convergence (fun _ : ℝ => K)
  · exact fun n => (hF n).aestronglyMeasurable
  · exact integrableOn_const (measure_Ioc_lt_top.ne)
  · intro n
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun s hs => by
      rw [Real.norm_eq_abs]
      exact hbound n s ⟨hs.1.le, hs.2⟩
  · rw [ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun s hs => hlim s ⟨hs.1.le, hs.2⟩

/-- A bounded pointwise limit of continuous functions is integrable on a compact interval. -/
theorem intervalIntegrable_of_continuous_bounded_limit
    {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {a b K : ℝ} (hab : a ≤ b)
    (hF : ∀ n, Continuous (F n))
    (hbound : ∀ n, ∀ s ∈ Icc a b, |F n s| ≤ K)
    (hlim : ∀ s ∈ Icc a b, Tendsto (fun n => F n s) atTop (𝓝 (f s))) :
    IntervalIntegrable f volume a b := by
  apply intervalIntegrable_iff.mpr
  rw [uIoc_of_le hab]
  have hlimAE : ∀ᵐ s ∂volume.restrict (Ioc a b),
      Tendsto (fun n => F n s) atTop (𝓝 (f s)) := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun s hs => hlim s ⟨hs.1.le, hs.2⟩
  have hm : AEStronglyMeasurable f (volume.restrict (Ioc a b)) :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hF n).aestronglyMeasurable) hlimAE
  have hK : IntegrableOn (fun _ : ℝ => K) (Ioc a b) volume :=
    integrableOn_const (measure_Ioc_lt_top.ne)
  apply hK.mono' hm
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun s hs => ?_
  apply le_of_tendsto (tendsto_norm.comp (hlim s ⟨hs.1.le, hs.2⟩))
  exact Eventually.of_forall fun n => by
    change ‖F n s‖ ≤ K
    rw [Real.norm_eq_abs]
    exact hbound n s ⟨hs.1.le, hs.2⟩

/-- A continuous integral majorant controls the upper right difference quotients. -/
theorem eventually_right_slope_le_of_integral_majorant
    {f B : ℝ → ℝ} {a r : ℝ} (hB : Continuous B) (hr : B a < r)
    (hbound : ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ,
      f (a + h) - f a ≤ ∫ s in a..(a + h), B s) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), (f (a + h) - f a) / h ≤ r := by
  obtain ⟨δ, hδ, hbound⟩ := hbound
  obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp
    (hB.continuousAt.eventually (gt_mem_nhds hr))
  filter_upwards [Ioo_mem_nhdsGT (lt_min hδ hε)] with h hh
  apply (div_le_iff₀ hh.1).mpr
  have hhδ : h ∈ Ioo (0 : ℝ) δ := ⟨hh.1, hh.2.trans_le (min_le_left _ _)⟩
  have hahr : a ≤ a + h := le_add_of_nonneg_right hh.1.le
  have hle := intervalIntegral.integral_mono_on hahr (hB.intervalIntegrable a (a + h))
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => r) volume a (a + h)) (by
      intro s hs
      apply (hnear ?_).le
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1)]
      have hsah : s - a ≤ h := by linarith only [hs.2]
      exact hsah.trans_lt (hh.2.trans_le (min_le_right _ _)))
  have hc : (∫ s in a..(a + h), r) = r * h := by
    rw [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left, mul_comm]
  exact (hbound h hhδ).trans (by rwa [hc] at hle)

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.sub_le_integral_of_forward_deriv_le
#print axioms GaloisForLFunctions.HTGeometry.tendsto_intervalIntegral_of_continuous_bounded
#print axioms GaloisForLFunctions.HTGeometry.intervalIntegrable_of_continuous_bounded_limit
#print axioms GaloisForLFunctions.HTGeometry.eventually_right_slope_le_of_integral_majorant
