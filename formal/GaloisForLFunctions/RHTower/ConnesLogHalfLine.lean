import GaloisForLFunctions.RHTower.ConnesLogPartsUnit

/-!
# Step 2, the half line: `∫_{(0,∞)} G'(u) log u du = −∫_{(0,∞)} H`

Step 2 of the route to the last §V identification of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Adding the two integrations by parts of `ConnesLogPartsTail` and `ConnesLogPartsUnit` — whose
non-`log` summands are exactly the principal-value integrand of `ConnesPVIntegrand` on `(0,1]`
and on `(1,∞)` — gives the half-line identity.
-/

open MeasureTheory Set Filter Topology Real
open scoped SchwartzMap Interval

namespace GaloisForLFunctions.RHTower

noncomputable section

theorem connes_derivLog_integrableOn_unit (G : 𝓢(ℝ, ℂ)) :
    IntegrableOn (fun u : ℝ => deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ))
      (Ioc (0 : ℝ) 1) volume := by
  set D : 𝓢(ℝ, ℂ) := SchwartzMap.derivCLM ℂ ℂ G with hD
  set σ : ℝ := SchwartzMap.seminorm ℂ 0 0 D with hσ
  have hσ0 : (0 : ℝ) ≤ σ := apply_nonneg _ D
  have hDb : ∀ u : ℝ, ‖deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u‖ ≤ σ := by
    intro u
    rw [connes_deriv_eq_derivCLM G u, ← hD]
    have h0 := SchwartzMap.norm_pow_mul_le_seminorm ℂ D 0 u
    simpa using h0
  have hlogI : IntegrableOn (fun u : ℝ => ‖Real.log u‖) (Ioc (0 : ℝ) 1) volume := by
    have h := (intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := 1)).norm
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h
    exact h
  refine Integrable.mono' (hlogI.const_mul σ) ?_ ?_
  · refine AEStronglyMeasurable.restrict ?_
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact ((SchwartzMap.derivCLM ℂ ℂ G).continuous.aestronglyMeasurable).congr
        (Filter.Eventually.of_forall fun u => (connes_deriv_eq_derivCLM G u).symm)
    · exact (Complex.measurable_ofReal.comp Real.measurable_log).aestronglyMeasurable
  · filter_upwards with u
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hDb u) (abs_nonneg _)

theorem connes_pvUnit_integrableOn (G : 𝓢(ℝ, ℂ)) :
    IntegrableOn (fun u : ℝ => ((G : ℝ → ℂ) u - (G : ℝ → ℂ) 0) * ((u⁻¹ : ℝ) : ℂ))
      (Ioc (0 : ℝ) 1) volume := by
  obtain ⟨C, hC0, hC⟩ := connes_schwartz_diffQuotient_bound G
  refine Measure.integrableOn_of_bounded (M := C) measure_Ioc_lt_top.ne ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    refine (G.continuous.measurable.sub measurable_const).mul ?_
    exact Complex.measurable_ofReal.comp measurable_inv
  · filter_upwards with u
    rcases eq_or_ne u 0 with hu | hu
    · simp [hu, hC0]
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv]
      have h1 : ‖(G : ℝ → ℂ) u - (G : ℝ → ℂ) 0‖ * |u|⁻¹ ≤ (C * |u|) * |u|⁻¹ :=
        mul_le_mul_of_nonneg_right (hC u) (by positivity)
      have h2 : (C * |u|) * |u|⁻¹ = C := by
        field_simp
      rw [h2] at h1
      exact h1

theorem connes_derivLog_integrableOn_tail (G : 𝓢(ℝ, ℂ)) :
    IntegrableOn (fun u : ℝ => deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ))
      (Ioi (1 : ℝ)) volume := by
  set D : 𝓢(ℝ, ℂ) := SchwartzMap.derivCLM ℂ ℂ G with hD
  set σ₃ : ℝ := SchwartzMap.seminorm ℂ 3 0 D with hσ₃
  have hσ₃0 : (0 : ℝ) ≤ σ₃ := apply_nonneg _ D
  have hpow : IntegrableOn (fun u : ℝ => u ^ (-(2 : ℝ))) (Ioi (1 : ℝ)) volume :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
  refine Integrable.mono' (hpow.const_mul σ₃) ?_ ?_
  · refine AEStronglyMeasurable.restrict ?_
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact ((SchwartzMap.derivCLM ℂ ℂ G).continuous.aestronglyMeasurable).congr
        (Filter.Eventually.of_forall fun u => (connes_deriv_eq_derivCLM G u).symm)
    · exact (Complex.measurable_ofReal.comp Real.measurable_log).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu1 : (1 : ℝ) < u := hu
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one hu1
    have hlognn : (0 : ℝ) ≤ Real.log u := Real.log_nonneg hu1.le
    have hlogle : Real.log u ≤ u := by
      have := Real.log_le_sub_one_of_pos hu0
      linarith
    have hu2 : u ^ (-(2 : ℝ)) = (u ^ 2)⁻¹ := by
      rw [Real.rpow_neg hu0.le, ← Real.rpow_natCast u 2]
      norm_num
    rw [connes_deriv_eq_derivCLM G u, ← hD, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hlognn, hu2]
    have hDb := connes_schwartz_le_pow D 3 hu0
    calc ‖(D : ℝ → ℂ) u‖ * Real.log u ≤ (σ₃ / u ^ 3) * u :=
          mul_le_mul hDb hlogle hlognn (by positivity)
      _ = σ₃ * (u ^ 2)⁻¹ := by field_simp

theorem connes_pvTail_integrableOn (G : 𝓢(ℝ, ℂ)) :
    IntegrableOn (fun u : ℝ => (G : ℝ → ℂ) u * ((u⁻¹ : ℝ) : ℂ)) (Ioi (1 : ℝ)) volume := by
  set σ₂ : ℝ := SchwartzMap.seminorm ℂ 2 0 G with hσ₂
  have hσ₂0 : (0 : ℝ) ≤ σ₂ := apply_nonneg _ G
  have hpow : IntegrableOn (fun u : ℝ => u ^ (-(2 : ℝ))) (Ioi (1 : ℝ)) volume :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
  refine Integrable.mono' (hpow.const_mul σ₂) ?_ ?_
  · refine AEStronglyMeasurable.restrict ?_
    refine AEStronglyMeasurable.mul (G.continuous.aestronglyMeasurable) ?_
    exact (Complex.measurable_ofReal.comp measurable_inv).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu1 : (1 : ℝ) < u := hu
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one hu1
    have hu2 : u ^ (-(2 : ℝ)) = (u ^ 2)⁻¹ := by
      rw [Real.rpow_neg hu0.le, ← Real.rpow_natCast u 2]
      norm_num
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), hu2]
    have hGb := connes_schwartz_le_pow G 2 hu0
    have hle1 : u⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right
      exact hu1.le
    calc ‖(G : ℝ → ℂ) u‖ * u⁻¹ ≤ (σ₂ / u ^ 2) * 1 :=
          mul_le_mul hGb hle1 (by positivity) (by positivity)
      _ = σ₂ * (u ^ 2)⁻¹ := by field_simp

/-- **Step 2 on the positive half line.** -/
theorem connes_log_halfline (G : 𝓢(ℝ, ℂ)) :
    (∫ u in Ioi (0 : ℝ), deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ))
      = - ∫ u in Ioi (0 : ℝ), connesPVintegrand ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u := by
  have hle : (0 : ℝ) ≤ 1 := by norm_num
  have hunit0 := connes_log_ftc_unit G
  rw [intervalIntegral.integral_of_le hle,
    MeasureTheory.integral_add (connes_derivLog_integrableOn_unit G)
      (connes_pvUnit_integrableOn G)] at hunit0
  have htail0 := connes_log_ftc_tail G
  rw [MeasureTheory.integral_add (connes_derivLog_integrableOn_tail G)
      (connes_pvTail_integrableOn G)] at htail0
  have hHunit : (∫ u in Ioc (0 : ℝ) 1, ((G : ℝ → ℂ) u - (G : ℝ → ℂ) 0) * ((u⁻¹ : ℝ) : ℂ))
      = ∫ u in Ioc (0 : ℝ) 1, connesPVintegrand ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    have humem : u ∈ {v : ℝ | |v| ≤ 1} := by
      rw [Set.mem_setOf_eq, abs_of_pos hu.1]
      exact hu.2
    rw [connes_pvIntegrand_on_ball humem, div_eq_mul_inv]
    push_cast
    ring
  have hHtail : (∫ u in Ioi (1 : ℝ), (G : ℝ → ℂ) u * ((u⁻¹ : ℝ) : ℂ))
      = ∫ u in Ioi (1 : ℝ), connesPVintegrand ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu1 : (1 : ℝ) < u := hu
    have hnot : u ∉ {v : ℝ | |v| ≤ 1} := by
      rw [Set.mem_setOf_eq, abs_of_pos (lt_trans zero_lt_one hu1)]
      exact not_le.mpr hu1
    rw [connes_pvIntegrand_off_ball hnot, div_eq_mul_inv]
    push_cast
    ring
  have hsplitset : Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) := by
    ext u
    simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro hu
      rcases le_or_gt u 1 with h | h
      · exact Or.inl ⟨hu, h⟩
      · exact Or.inr h
    · rintro (⟨h1, _⟩ | h)
      · exact h1
      · linarith
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi (1 : ℝ)) := by
    rw [Set.disjoint_left]
    rintro u hu h3
    exact absurd h3 (not_lt.mpr hu.2)
  have hHu_int : IntegrableOn (connesPVintegrand ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ))
      (Ioc (0 : ℝ) 1) volume := by
    refine (connes_pvIntegrand_integrableOn_ball G).mono_set fun u hu => ?_
    rw [Set.mem_setOf_eq, abs_of_pos hu.1]
    exact hu.2
  have hHt_int : IntegrableOn (connesPVintegrand ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ))
      (Ioi (1 : ℝ)) volume := by
    refine (connes_pvIntegrand_integrableOn_compl G).mono_set fun u hu => ?_
    have hu1 : (1 : ℝ) < u := hu
    rw [connes_unitBall_compl, Set.mem_setOf_eq, abs_of_pos (lt_trans zero_lt_one hu1)]
    exact hu1
  have hsplitL : (∫ u in Ioi (0 : ℝ), deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ))
      = (∫ u in Ioc (0 : ℝ) 1, deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ))
        + ∫ u in Ioi (1 : ℝ), deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ) := by
    rw [hsplitset, MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
      (connes_derivLog_integrableOn_unit G) (connes_derivLog_integrableOn_tail G)]
  have hsplitR : (∫ u in Ioi (0 : ℝ), connesPVintegrand ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u)
      = (∫ u in Ioc (0 : ℝ) 1, connesPVintegrand ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u)
        + ∫ u in Ioi (1 : ℝ), connesPVintegrand ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u := by
    rw [hsplitset, MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hHu_int hHt_int]
  rw [hsplitL, hsplitR, ← hHunit, ← hHtail]
  linear_combination hunit0 + htail0

end

end GaloisForLFunctions.RHTower
