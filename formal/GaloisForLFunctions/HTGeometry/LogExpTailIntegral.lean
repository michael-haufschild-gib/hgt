import GaloisForLFunctions.HTGeometry.GammaLogIntegralEulerMascheroni

/-!
# The logarithmic exponential tail integral

The logarithmic moment of the exponential density is absolutely convergent on `(0, ∞)`, and its
tail from a positive endpoint converges to the whole integral:

```text
∫_a^∞ (log u) e^(-u) du → ∫_0^∞ (log u) e^(-u) du = -γ      (a → 0⁺).
```
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators

namespace HTGeometry

noncomputable section

private theorem log_le_self {u : ℝ} (hu : 0 < u) : Real.log u ≤ u := by
  have := Real.log_le_sub_one_of_pos hu
  linarith

private theorem self_mul_exp_neg_le {u : ℝ} (_hu : 0 ≤ u) :
    u * Real.exp (-u) ≤ 2 * Real.exp (-(1 / 2) * u) := by
  have h1 : u / 2 ≤ Real.exp (u / 2) := by
    have := Real.add_one_le_exp (u / 2)
    linarith
  have hexppos : (0 : ℝ) < Real.exp (-(1 / 2) * u) := Real.exp_pos _
  have hsplit : Real.exp (-u) = Real.exp (-(1 / 2) * u) * Real.exp (-(1 / 2) * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hinv : Real.exp (-(1 / 2) * u) = (Real.exp (u / 2))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  have hkey : u * Real.exp (-(1 / 2) * u) ≤ 2 := by
    rw [hinv, mul_inv_le_iff₀ (Real.exp_pos _)]
    linarith
  rw [hsplit]
  nlinarith [hexppos, hkey]

private theorem measurable_logExp :
    Measurable (fun u : ℝ => Real.log u * Real.exp (-u)) :=
  Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg)

theorem integrableOn_log_mul_exp_neg_Ioi_one :
    IntegrableOn (fun u : ℝ => Real.log u * Real.exp (-u)) (Ioi (1 : ℝ)) := by
  have hmajor : IntegrableOn (fun u : ℝ => 2 * Real.exp (-(1 / 2) * u)) (Ioi (1 : ℝ)) :=
    (integrableOn_exp_mul_Ioi (by norm_num) 1).const_mul 2
  refine Integrable.mono hmajor measurable_logExp.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu1 : (1 : ℝ) < u := hu
  have hu0 : (0 : ℝ) < u := by linarith
  have hlog : 0 ≤ Real.log u := Real.log_nonneg hu1.le
  have hlogle : Real.log u ≤ u := log_le_self hu0
  have hexp : (0 : ℝ) < Real.exp (-u) := Real.exp_pos _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hlog hexp.le), Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.exp (-(1 / 2) * u))]
  calc Real.log u * Real.exp (-u) ≤ u * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right hlogle hexp.le
    _ ≤ 2 * Real.exp (-(1 / 2) * u) := self_mul_exp_neg_le hu0.le

theorem integrableOn_log_mul_exp_neg_Ioc_zero_one :
    IntegrableOn (fun u : ℝ => Real.log u * Real.exp (-u)) (Ioc (0 : ℝ) 1) := by
  have hlog : IntegrableOn Real.log (Ioc (0 : ℝ) 1) := by
    have h := intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := (1 : ℝ))
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at h
  refine Integrable.mono hlog measurable_logExp.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  have hu0 : (0 : ℝ) < u := hu.1
  have hexp1 : Real.exp (-u) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hexp0 : (0 : ℝ) < Real.exp (-u) := Real.exp_pos _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos hexp0]
  nlinarith [abs_nonneg (Real.log u)]

theorem integrableOn_log_mul_exp_neg_Ioi_zero :
    IntegrableOn (fun u : ℝ => Real.log u * Real.exp (-u)) (Ioi (0 : ℝ)) := by
  have hunion : Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) = Ioi (0 : ℝ) :=
    Ioc_union_Ioi_eq_Ioi (by norm_num)
  rw [← hunion]
  exact integrableOn_log_mul_exp_neg_Ioc_zero_one.union integrableOn_log_mul_exp_neg_Ioi_one

theorem integrableOn_log_mul_exp_neg_Ioi {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun u : ℝ => Real.log u * Real.exp (-u)) (Ioi a) := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · exact integrableOn_log_mul_exp_neg_Ioi_zero
  · exact integrableOn_log_mul_exp_neg_Ioi_zero.mono_set (Ioi_subset_Ioi ha)

/-- **The tail of the logarithmic exponential integral converges to `-γ`.** -/
theorem tendsto_integral_Ioi_log_mul_exp_neg :
    Tendsto (fun a : ℝ => ∫ u in Ioi a, Real.log u * Real.exp (-u))
      (nhdsWithin 0 (Ioi 0)) (nhds (-Real.eulerMascheroniConstant)) := by
  set f : ℝ → ℝ := fun u => Real.log u * Real.exp (-u) with hf
  set g : ℝ → ℝ := (Ioi (0 : ℝ)).indicator f with hg
  have hgint : Integrable g := by
    rw [hg, integrable_indicator_iff measurableSet_Ioi]
    exact integrableOn_log_mul_exp_neg_Ioi_zero
  have hFmeas : ∀ᶠ a : ℝ in nhdsWithin 0 (Ioi 0),
      AEStronglyMeasurable ((Ioi a).indicator f) volume := by
    filter_upwards with a
    exact (measurable_logExp.indicator measurableSet_Ioi).aestronglyMeasurable
  have hbound : ∀ᶠ a : ℝ in nhdsWithin 0 (Ioi 0),
      ∀ᵐ u : ℝ, ‖(Ioi a).indicator f u‖ ≤ ‖g u‖ := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    filter_upwards with u
    by_cases hu : u ∈ Ioi a
    · have hu0 : (0 : ℝ) < u := lt_trans ha hu
      rw [indicator_of_mem hu, hg, indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu0)]
    · rw [indicator_of_notMem hu, norm_zero]
      exact norm_nonneg _
  have hlim : ∀ᵐ u : ℝ,
      Tendsto (fun a : ℝ => (Ioi a).indicator f u) (nhdsWithin 0 (Ioi 0)) (nhds (g u)) := by
    filter_upwards with u
    by_cases hu : (0 : ℝ) < u
    · have heq : (fun _ : ℝ => g u) =ᶠ[nhdsWithin 0 (Ioi 0)]
          fun a : ℝ => (Ioi a).indicator f u := by
        filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds hu)] with a ha
        rw [indicator_of_mem (show u ∈ Ioi a from ha), hg,
          indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu)]
      exact Tendsto.congr' heq tendsto_const_nhds
    · have hgu : g u = 0 := by
        rw [hg, indicator_of_notMem (by simpa using hu)]
      have heq : (fun _ : ℝ => g u) =ᶠ[nhdsWithin 0 (Ioi 0)]
          fun a : ℝ => (Ioi a).indicator f u := by
        filter_upwards [self_mem_nhdsWithin] with a ha
        rw [indicator_of_notMem (by
          simp only [mem_Ioi, not_lt]
          exact le_trans (not_lt.mp hu) ha.le), hgu]
      exact Tendsto.congr' heq tendsto_const_nhds
  have hmain := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun u => ‖g u‖) hFmeas hbound hgint.norm hlim
  have hleft : ∀ a : ℝ, (∫ u, (Ioi a).indicator f u) = ∫ u in Ioi a, f u := by
    intro a
    rw [integral_indicator measurableSet_Ioi]
  have hright : (∫ u, g u) = -Real.eulerMascheroniConstant := by
    rw [hg, integral_indicator measurableSet_Ioi]
    exact integral_log_mul_exp_neg_Ioi
  rw [hright] at hmain
  exact hmain.congr fun a => hleft a

end

end HTGeometry
