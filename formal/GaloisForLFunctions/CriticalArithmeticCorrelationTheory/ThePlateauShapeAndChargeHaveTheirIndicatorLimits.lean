import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.SmoothPlateausRecoverTheCompletedRobinMargin

/-!
# The indicator limits of smooth plateau shape and charge

As the transition layers shrink, the Robin integral, square mass, and charge
each tend to one. Consequently the completed shape tends to two. The positive
margin is attained while retaining almost all of the unit support's mass;
it is not obtained by concentrating the profile into a short subinterval.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis

/-- The square mass of a smooth plateau tends to the length of its support. -/
theorem tendsto_integral_plateau_sq :
    Tendsto (fun η : ℝ => ∫ u, plateau η u ^ 2) (𝓝[>] 0) (𝓝 1) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    have hid : Tendsto (fun η : ℝ => η) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    have hlim : Tendsto (fun η : ℝ => 1 - 2 * η) (𝓝[>] 0) (𝓝 1) := by
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub (hid.const_mul 2))
    have hsmall : ∀ᶠ η : ℝ in 𝓝[>] 0, η < 1 / 2 :=
      nhdsWithin_le_nhds (gt_mem_nhds (by norm_num))
    filter_upwards [hlim.eventually (lt_mem_nhds ha), self_mem_nhdsWithin, hsmall]
      with η hlo hη hη2
    exact hlo.trans_le (integral_plateau_sq_ge hη hη2.le)
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact (integral_plateau_sq_le hη).trans_lt ha

/-- The plateau charge also tends to the length of its support. -/
theorem tendsto_integral_plateau :
    Tendsto (fun η : ℝ => ∫ u, plateau η u) (𝓝[>] 0) (𝓝 1) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    have hid : Tendsto (fun η : ℝ => η) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    have hlim : Tendsto (fun η : ℝ => 1 - 2 * η) (𝓝[>] 0) (𝓝 1) := by
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub (hid.const_mul 2))
    have hsmall : ∀ᶠ η : ℝ in 𝓝[>] 0, η < 1 / 2 :=
      nhdsWithin_le_nhds (gt_mem_nhds (by norm_num))
    filter_upwards [hlim.eventually (lt_mem_nhds ha), self_mem_nhdsWithin, hsmall]
      with η hlo hη hη2
    exact hlo.trans_le (integral_plateau_ge hη hη2.le)
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with η hη
    have hI : (∫ u, plateau η u) ≤ 1 := by
      simpa only [abs_of_nonneg (plateau_nonneg _)] using integral_abs_plateau_le hη
    exact hI.trans_lt ha

/-- The singular Robin integral converges despite the narrowing transition layers. -/
theorem tendsto_bumpRobin_plateau :
    Tendsto (fun η : ℝ => bumpRobin (plateau η) 1) (𝓝[>] 0) (𝓝 1) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    let δ := min ((1 - a) / 2) (1 / 2)
    have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
    have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (by norm_num)
    have haδ : a < 1 - δ := by
      have hd : δ ≤ (1 - a) / 2 := min_le_left _ _
      linarith only [hd, ha]
    let F : ℝ → ℝ := fun η => (1 - δ) * (1 - 2 * η / δ)
    have hlim : Tendsto F (𝓝[>] 0) (𝓝 (1 - δ)) := by
      have hc : Continuous F := by dsimp [F]; fun_prop
      have hv : F 0 = 1 - δ := by dsimp [F]; ring
      rw [← hv]
      exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hsmall : ∀ᶠ η : ℝ in 𝓝[>] 0, η < 1 / 2 :=
      nhdsWithin_le_nhds (gt_mem_nhds (by norm_num))
    filter_upwards [hlim.eventually (lt_mem_nhds haδ), self_mem_nhdsWithin, hsmall]
      with η hF hη hη2
    exact hF.trans_le (bumpRobin_plateau_ge hη hη2.le hδ hδ1)
  · intro a ha
    obtain ⟨C, hC0, hC⟩ := exists_lipschitz_smoothTransition
    have hid : Tendsto (fun η : ℝ => η) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    have hlog : Tendsto (fun η : ℝ => Real.log η * η) (𝓝[>] 0) (𝓝 0) := by
      simpa using tendsto_log_mul_rpow_nhdsGT_zero (r := 1) one_pos
    have hlim : Tendsto (fun η : ℝ => 1 + 2 * C * η - 4 * (Real.log η * η))
        (𝓝[>] 0) (𝓝 1) := by
      simpa using (((tendsto_const_nhds (x := (1 : ℝ))).add (hid.const_mul (2 * C))).sub
        (hlog.const_mul 4))
    have hsmall : ∀ᶠ η : ℝ in 𝓝[>] 0, η < 1 :=
      nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)
    filter_upwards [hlim.eventually (gt_mem_nhds ha), self_mem_nhdsWithin, hsmall]
      with η hF hη hη1
    have hB := bumpRobin_plateau_le hC0 hC hη hη1
    nlinarith only [hF, hB]

/-- Unit mass normalization preserves the plateau's Robin limit. -/
theorem tendsto_normalized_bumpRobin_plateau :
    Tendsto (fun η : ℝ => bumpRobin (plateau η) 1 / (∫ u, plateau η u ^ 2))
      (𝓝[>] 0) (𝓝 1) := by
  convert tendsto_bumpRobin_plateau.div tendsto_integral_plateau_sq one_ne_zero using 1 <;> norm_num
  funext η
  rfl

/-- The normalized squared charge approaches one. -/
theorem tendsto_plateau_charge_ratio :
    Tendsto (fun η : ℝ => (∫ u, plateau η u) ^ 2 / (∫ u, plateau η u ^ 2))
      (𝓝[>] 0) (𝓝 1) := by
  convert (tendsto_integral_plateau.pow 2).div tendsto_integral_plateau_sq one_ne_zero using 1 <;> norm_num
  funext η
  rfl

/-- Both independent contributions survive the smooth approximation to the indicator. -/
theorem tendsto_plateau_completed_shape :
    Tendsto (fun η : ℝ => bumpRobin (plateau η) 1 / (∫ u, plateau η u ^ 2) +
      (∫ u, plateau η u) ^ 2 / (∫ u, plateau η u ^ 2)) (𝓝[>] 0) (𝓝 2) := by
  convert tendsto_normalized_bumpRobin_plateau.add tendsto_plateau_charge_ratio using 1
  norm_num

/-- The completed margin tends to `2 - log (2π)` while the full support is filled. -/
theorem tendsto_plateau_completed_margin :
    Tendsto (fun η : ℝ => bumpRobin (plateau η) 1 / (∫ u, plateau η u ^ 2) +
      (∫ u, plateau η u) ^ 2 / (∫ u, plateau η u ^ 2) - Real.log (2 * Real.pi))
      (𝓝[>] 0) (𝓝 (2 - Real.log (2 * Real.pi))) :=
  tendsto_plateau_completed_shape.sub_const _

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_plateau_completed_shape
