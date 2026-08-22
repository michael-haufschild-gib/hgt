import GaloisForLFunctions.RHTower.ConnesSchwartzReflect

/-!
# Step 2 on the negative half line, and on the whole line

Step 2 of the route to the last §V identification of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Applying `connes_log_halfline` to the reflected Schwartz map and substituting `u ↦ −u` transports
the positive-half identity to the negative half; adding the two gives

  `∫_ℝ G'(u) log|u| du = −PV ∫ G(u)/u du`.

(`Real.log` is even, so `log u` *is* `log |u|`; no absolute values need to be carried.)
-/

open MeasureTheory Set Filter Topology Real
open scoped SchwartzMap

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- **Step 2 on the negative half line.** -/
theorem connes_log_negline (G : 𝓢(ℝ, ℂ)) :
    (∫ u in Iio (0 : ℝ), deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ))
      = - ∫ u in Iio (0 : ℝ), connesPVintegrand ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u := by
  have hR := connes_log_halfline (connesReflect G)
  have hL : (∫ v in Ioi (0 : ℝ),
        deriv ((connesReflect G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) v * ((Real.log v : ℝ) : ℂ))
      = - ∫ v in Ioi (0 : ℝ),
          deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (-v) * ((Real.log v : ℝ) : ℂ) := by
    rw [← MeasureTheory.integral_neg]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    rw [connes_deriv_reflect G v]
    ring
  have hRr : (∫ v in Ioi (0 : ℝ), connesPVintegrand ((connesReflect G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) v)
      = - ∫ v in Ioi (0 : ℝ), connesPVintegrand ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (-v) := by
    rw [← MeasureTheory.integral_neg]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    rw [connes_pvIntegrand_reflect G v]
  rw [hL, hRr] at hR
  -- hR : - ∫_{Ioi 0} G'(-v) log v = - (- ∫_{Ioi 0} H(-v))
  have hkey : (∫ v in Ioi (0 : ℝ), deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (-v) * ((Real.log v : ℝ) : ℂ))
      = - ∫ v in Ioi (0 : ℝ), connesPVintegrand ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (-v) := by
    linear_combination -hR
  have hsubL : (∫ v in Ioi (0 : ℝ),
        deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (-v) * ((Real.log v : ℝ) : ℂ))
      = ∫ u in Iic (0 : ℝ), deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ) := by
    have h := _root_.integral_comp_neg_Ioi (0 : ℝ)
      (fun u : ℝ => deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ))
    rw [neg_zero] at h
    rw [← h]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    rw [Real.log_neg_eq_log]
  have hsubR : (∫ v in Ioi (0 : ℝ), connesPVintegrand ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (-v))
      = ∫ u in Iic (0 : ℝ), connesPVintegrand ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u := by
    have h := _root_.integral_comp_neg_Ioi (0 : ℝ)
      (fun u : ℝ => connesPVintegrand ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u)
    rw [neg_zero] at h
    exact h
  rw [hsubL, hsubR] at hkey
  have hIic : (Iic (0 : ℝ)) =ᵐ[volume] (Iio (0 : ℝ)) := by
    have hnull : (volume : Measure ℝ) ({(0 : ℝ)}) = 0 := Real.volume_singleton
    have hdiff : Iic (0 : ℝ) \ Iio (0 : ℝ) = {(0 : ℝ)} := by
      ext u
      simp only [Set.mem_sdiff, Set.mem_Iic, Set.mem_Iio, Set.mem_singleton_iff, not_lt]
      constructor
      · rintro ⟨h1, h2⟩
        exact le_antisymm h1 h2
      · rintro rfl
        exact ⟨le_refl _, le_refl _⟩
    refine MeasureTheory.ae_eq_set.mpr ⟨?_, ?_⟩
    · rw [hdiff]
      exact hnull
    · have : Iio (0 : ℝ) \ Iic (0 : ℝ) = (∅ : Set ℝ) := by
        ext u
        simp only [Set.mem_sdiff, Set.mem_Iio, Set.mem_Iic, Set.mem_empty_iff_false, not_le,
          iff_false, not_and, not_lt]
        intro h
        exact h.le
      rw [this]
      simp
  rw [MeasureTheory.setIntegral_congr_set hIic,
    MeasureTheory.setIntegral_congr_set hIic] at hkey
  exact hkey

/-- `G' · log` is globally integrable. -/
theorem connes_derivLog_integrable (G : 𝓢(ℝ, ℂ)) :
    Integrable (fun u : ℝ => deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ))
      volume := by
  set D : 𝓢(ℝ, ℂ) := SchwartzMap.derivCLM ℂ ℂ G with hD
  set σ₀ : ℝ := SchwartzMap.seminorm ℂ 0 0 D with hσ₀
  set σ₃ : ℝ := SchwartzMap.seminorm ℂ 3 0 D with hσ₃
  have hσ₀0 : (0 : ℝ) ≤ σ₀ := apply_nonneg _ D
  have hσ₃0 : (0 : ℝ) ≤ σ₃ := apply_nonneg _ D
  have hDeq : ∀ u : ℝ, deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u = (D : ℝ → ℂ) u := by
    intro u
    rw [hD]
    exact connes_deriv_eq_derivCLM G u
  have hmeas : AEStronglyMeasurable
      (fun u : ℝ => deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ)) volume := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (D.continuous.aestronglyMeasurable).congr
        (Filter.Eventually.of_forall fun u => (hDeq u).symm)
    · exact (Complex.measurable_ofReal.comp Real.measurable_log).aestronglyMeasurable
  have huniv : (Set.univ : Set ℝ) = Icc (-1 : ℝ) 1 ∪ (Icc (-1 : ℝ) 1)ᶜ :=
    (Set.union_compl_self _).symm
  rw [← MeasureTheory.integrableOn_univ, huniv]
  refine IntegrableOn.union ?_ ?_
  · have hlogI : IntegrableOn (fun u : ℝ => ‖Real.log u‖) (Icc (-1 : ℝ) 1) volume := by
      have h := (intervalIntegral.intervalIntegrable_log' (a := (-1 : ℝ)) (b := 1)).norm
      rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at h
      exact (integrableOn_Icc_iff_integrableOn_Ioc
        (f := fun u : ℝ => ‖Real.log u‖) (μ := volume) (a := (-1 : ℝ)) (b := 1)).mpr h
    refine Integrable.mono' (hlogI.const_mul σ₀) hmeas.restrict ?_
    filter_upwards with u
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [hDeq u]
    have h0 := SchwartzMap.norm_pow_mul_le_seminorm ℂ D 0 u
    simpa using h0
  · have hsub : ((Icc (-1 : ℝ) 1)ᶜ) ⊆ {x : ℝ | (1 : ℝ) ≤ |x|} := by
      intro u hu
      rw [Set.mem_setOf_eq]
      by_contra hlt
      rw [not_le] at hlt
      exact hu (Set.mem_Icc.mpr (abs_le.mp hlt.le))
    have htail : IntegrableOn (fun x : ℝ => |x| ^ (-(2 : ℝ))) ((Icc (-1 : ℝ) 1)ᶜ) volume :=
      (connes_absRpow_tail_integrable (by norm_num) (by norm_num : (0 : ℝ) < 1)).mono_set hsub
    refine Integrable.mono' (htail.const_mul σ₃) hmeas.restrict ?_
    filter_upwards [ae_restrict_mem (measurableSet_Icc.compl)] with u hu
    have hu1 : (1 : ℝ) ≤ |u| := hsub hu
    have hu0 : (0 : ℝ) < |u| := lt_of_lt_of_le zero_lt_one hu1
    have hlognn : (0 : ℝ) ≤ Real.log |u| := Real.log_nonneg hu1
    have hlogle : Real.log |u| ≤ |u| := by
      have := Real.log_le_sub_one_of_pos hu0
      linarith
    have habs : (|u| : ℝ) ^ (-(2 : ℝ)) = (|u| ^ 2)⁻¹ := by
      rw [Real.rpow_neg hu0.le, ← Real.rpow_natCast |u| 2]
      norm_num
    have hDb : ‖(D : ℝ → ℂ) u‖ ≤ σ₃ / |u| ^ 3 := by
      have hsem := SchwartzMap.norm_pow_mul_le_seminorm ℂ D 3 u
      rw [Real.norm_eq_abs] at hsem
      rw [le_div_iff₀ (by positivity)]
      calc ‖(D : ℝ → ℂ) u‖ * |u| ^ 3 = |u| ^ 3 * ‖(D : ℝ → ℂ) u‖ := by ring
        _ ≤ σ₃ := hsem
    rw [hDeq u, norm_mul, Complex.norm_real, Real.norm_eq_abs, habs]
    have hlogabs : |Real.log u| = Real.log |u| := by
      rw [Real.log_abs u]
      exact abs_of_nonneg (by rw [← Real.log_abs u]; exact hlognn)
    rw [hlogabs]
    calc ‖(D : ℝ → ℂ) u‖ * Real.log |u| ≤ (σ₃ / |u| ^ 3) * |u| :=
          mul_le_mul hDb hlogle hlognn (by positivity)
      _ = σ₃ * (|u| ^ 2)⁻¹ := by field_simp

/-- **Step 2, the whole line.**  `∫_ℝ G'(u) log|u| du = −PV ∫ G(u)/u du`. -/
theorem connes_log_fullline (G : 𝓢(ℝ, ℂ)) :
    (∫ u : ℝ, deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ))
      = - connesPVinv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
  have hIntf := connes_derivLog_integrable G
  have hIntH := connes_pvIntegrand_integrable G
  have hIci : (Ici (0 : ℝ)) =ᵐ[volume] (Ioi (0 : ℝ)) := by
    have hnull : (volume : Measure ℝ) ({(0 : ℝ)}) = 0 := Real.volume_singleton
    refine MeasureTheory.ae_eq_set.mpr ⟨?_, ?_⟩
    · have hdiff : Ici (0 : ℝ) \ Ioi (0 : ℝ) = {(0 : ℝ)} := by
        ext u
        simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_Ioi, Set.mem_singleton_iff, not_lt]
        constructor
        · rintro ⟨h1, h2⟩
          exact le_antisymm h2 h1
        · rintro rfl
          exact ⟨le_refl _, le_refl _⟩
      rw [hdiff]
      exact hnull
    · have hdiff : Ioi (0 : ℝ) \ Ici (0 : ℝ) = (∅ : Set ℝ) := by
        ext u
        simp only [Set.mem_sdiff, Set.mem_Ioi, Set.mem_Ici, Set.mem_empty_iff_false, not_le,
          iff_false, not_and, not_lt]
        intro h
        exact h.le
      rw [hdiff]
      simp
  have huniv : (Set.univ : Set ℝ) = Iio (0 : ℝ) ∪ Ici (0 : ℝ) := by
    ext u
    simp only [Set.mem_univ, Set.mem_union, Set.mem_Iio, Set.mem_Ici, true_iff]
    exact lt_or_ge u 0
  have hdisj : Disjoint (Iio (0 : ℝ)) (Ici (0 : ℝ)) := by
    rw [Set.disjoint_left]
    intro u hu hu'
    exact absurd (Set.mem_Ici.mp hu') (not_le.mpr (Set.mem_Iio.mp hu))
  have hsplitf : (∫ u : ℝ, deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ))
      = (∫ u in Iio (0 : ℝ), deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ))
        + ∫ u in Ioi (0 : ℝ), deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ) := by
    rw [← MeasureTheory.setIntegral_univ, huniv,
      MeasureTheory.setIntegral_union hdisj measurableSet_Ici hIntf.integrableOn
        hIntf.integrableOn, MeasureTheory.setIntegral_congr_set hIci]
  have hsplitH : (∫ u : ℝ, connesPVintegrand ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u)
      = (∫ u in Iio (0 : ℝ), connesPVintegrand ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u)
        + ∫ u in Ioi (0 : ℝ), connesPVintegrand ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u := by
    rw [← MeasureTheory.setIntegral_univ, huniv,
      MeasureTheory.setIntegral_union hdisj measurableSet_Ici hIntH.integrableOn
        hIntH.integrableOn, MeasureTheory.setIntegral_congr_set hIci]
  rw [hsplitf, connes_log_negline G, connes_log_halfline G,
    ← connes_integral_pvIntegrand G, hsplitH]
  ring

end

end GaloisForLFunctions.RHTower
