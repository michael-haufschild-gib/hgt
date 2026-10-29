import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheMarkovFormFailsInsideTheSeparatedRegime
import GaloisForLFunctions.RHTower.SharpWeilNearRadicalCount

/-!
# Smooth plateaus recover the completed Robin margin

A plateau's autocorrelation cannot exceed the length of the overlapping supports.
This gives a lower Robin bound without differentiating the transition layer.
Together with its nearly unit charge, smooth plateaus have completed shape energy
arbitrarily close to two from below, above the archimedean loss `log (2π)`.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
open _root_.RHTower (archLevyDensity)

/-- The Robin density is integrable because it is dominated by the Lévy density. -/
theorem integrableOn_robinDensity {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) :
    IntegrableOn (fun y => (∫ u, (g u - g (u + y)) ^ 2) / (2 * y)) (Set.Ioc 0 1) := by
  have hQm : StronglyMeasurable (fun y => ∫ u, (g u - g (u + y)) ^ 2) := by
    have hc : Continuous fun p : ℝ × ℝ => (g p.2 - g (p.2 + p.1)) ^ 2 := by
      have := hg.continuous
      fun_prop
    exact hc.stronglyMeasurable.integral_prod_right'
  have hi := (_root_.RHTower.integrableOn_levyIntegrand hg hgc).mono_set
    (show Set.Ioc (0 : ℝ) 1 ⊆ Set.Ioi 0 from Set.Ioc_subset_Ioi_self)
  refine hi.mono' (hQm.measurable.div (measurable_const.mul measurable_id)).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun y hy => ?_)
  have hQ : 0 ≤ ∫ u, (g u - g (u + y)) ^ 2 := integral_nonneg fun _ => sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hQ (by linarith [hy.1]))]
  calc (∫ u, (g u - g (u + y)) ^ 2) / (2 * y)
      = (1 / (2 * y)) * ∫ u, (g u - g (u + y)) ^ 2 := by ring
    _ ≤ archLevyDensity y * ∫ u, (g u - g (u + y)) ^ 2 :=
      mul_le_mul_of_nonneg_right (archLevyDensity_ge_inv_two_mul hy.1 hy.2) hQ

/-- Autocorrelation is bounded by the overlap of the two unit supports. -/
theorem integral_plateau_mul_shift_le {η y : ℝ} (hη : 0 < η) (hy1 : y ≤ 1) :
    (∫ u, plateau η u * plateau η (u + y)) ≤ 1 - y := by
  have heq : (∫ u, plateau η u * plateau η (u + y)) =
      ∫ u in Set.Icc 0 (1 - y), plateau η u * plateau η (u + y) := by
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
    intro u hu
    simp only [Set.mem_Icc, not_and_or, not_le] at hu
    rcases hu with hu | hu
    · rw [plateau_eq_zero hη (by intro h; linarith [h.1]), zero_mul]
    · rw [plateau_eq_zero hη (u := u + y) (by intro h; linarith [h.2]), mul_zero]
  rw [heq]
  have hc : Continuous fun u => plateau η u * plateau η (u + y) := by
    have := (contDiff_plateau η).continuous
    fun_prop
  have hi : IntegrableOn (fun u => plateau η u * plateau η (u + y)) (Set.Icc 0 (1 - y)) :=
    hc.integrableOn_Icc
  have hi1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc 0 (1 - y)) :=
    continuous_const.integrableOn_Icc
  have hle := setIntegral_mono_on hi hi1
    measurableSet_Icc (fun u (_ : u ∈ Set.Icc 0 (1 - y)) =>
      (mul_le_mul (plateau_le_one u) (plateau_le_one (u + y))
        (plateau_nonneg (u + y)) zero_le_one).trans_eq (one_mul 1))
  simpa [show (0 : ℝ) ≤ 1 - y by linarith] using hle

/-- Truncating the nonnegative Robin density away from zero gives a lower bound. -/
theorem bumpRobin_plateau_ge {η δ : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (1 - δ) * (1 - 2 * η / δ) ≤ bumpRobin (plateau η) 1 := by
  let Q : ℝ → ℝ := fun y => ∫ u, (plateau η u - plateau η (u + y)) ^ 2
  have hi := integrableOn_robinDensity (contDiff_plateau η) (hasCompactSupport_plateau hη)
  have hiδ : IntegrableOn (fun y => Q y / (2 * y)) (Set.Ioc δ 1) :=
    hi.mono_set fun y hy => ⟨lt_trans hδ hy.1, hy.2⟩
  have hpt : ∀ y ∈ Set.Ioc δ 1, 1 - 2 * η / δ ≤ Q y / (2 * y) := by
    intro y hy
    have hy0 : 0 < y := lt_trans hδ hy.1
    have hQ : 2 * y - 4 * η ≤ Q y := by
      dsimp [Q]
      rw [integral_sub_shift_sq_eq (contDiff_plateau η).continuous (hasCompactSupport_plateau hη)]
      linarith only [integral_plateau_sq_ge hη hη2,
        integral_plateau_mul_shift_le hη hy.2]
    have hdiv : 2 * η / y ≤ 2 * η / δ :=
      div_le_div_of_nonneg_left (by positivity) hδ hy.1.le
    have hsmall : 1 - 2 * η / y ≤ Q y / (2 * y) := by
      rw [le_div_iff₀ (by positivity)]
      calc (1 - 2 * η / y) * (2 * y) = 2 * y - 4 * η := by field_simp; ring
        _ ≤ Q y := hQ
    linarith only [hsmall, hdiv]
  have hfar : (1 - δ) * (1 - 2 * η / δ) ≤ ∫ y in Set.Ioc δ 1, Q y / (2 * y) := by
    have h := setIntegral_mono_on (integrableOn_const (C := 1 - 2 * η / δ) (by simp))
      hiδ measurableSet_Ioc hpt
    simpa [Real.volume_Ioc, hδ1] using h
  have hsplit : Set.Ioc (0 : ℝ) 1 = Set.Ioc 0 δ ∪ Set.Ioc δ 1 :=
    (Set.Ioc_union_Ioc_eq_Ioc hδ.le hδ1).symm
  have hnear : 0 ≤ ∫ y in Set.Ioc 0 δ, Q y / (2 * y) := by
    apply setIntegral_nonneg measurableSet_Ioc
    intro y hy
    exact div_nonneg (integral_nonneg fun _ => sq_nonneg _) (by linarith [hy.1])
  change _ ≤ ∫ y in Set.Ioc 0 1, Q y / (2 * y)
  rw [hsplit, setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
    (hi.mono_set fun y hy => ⟨hy.1, hy.2.trans hδ1⟩) hiδ]
  linarith only [hfar, hnear]

/-- The plateau carries almost the full charge of its unit support. -/
theorem integral_plateau_ge {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    1 - 2 * η ≤ ∫ u, plateau η u := by
  have hi : Integrable (plateau η) := (contDiff_plateau η).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_plateau hη)
  have h := le_integral_of_eq_one_on hi (fun u => plateau_nonneg u)
    (a := η) (b := 1 - η) (by linarith) (fun u hu => plateau_eq_one hη hu)
  linarith only [h]

/-- The Robin term and the completed pole charge have limiting lower margin two. -/
theorem plateau_completed_shape_ge {η δ : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (1 - δ) * (1 - 2 * η / δ) + (1 - 2 * η) ^ 2 ≤
      bumpRobin (plateau η) 1 / (∫ u, plateau η u ^ 2) +
        (∫ u, plateau η u) ^ 2 / (∫ u, plateau η u ^ 2) := by
  have hM : 0 < ∫ u, plateau η u ^ 2 :=
    lt_of_lt_of_le (by linarith) (integral_plateau_sq_ge hη hη2.le)
  have hM1 := integral_plateau_sq_le hη
  have hB : 0 ≤ bumpRobin (plateau η) 1 := by
    apply setIntegral_nonneg measurableSet_Ioc
    intro y hy
    exact div_nonneg (integral_nonneg fun _ => sq_nonneg _) (by linarith [hy.1])
  have hBdiv : bumpRobin (plateau η) 1 ≤
      bumpRobin (plateau η) 1 / (∫ u, plateau η u ^ 2) := by
    rw [le_div_iff₀ hM]
    exact (mul_le_mul_of_nonneg_left hM1 hB).trans_eq (mul_one _)
  have hI := integral_plateau_ge hη hη2.le
  have hIsq : (1 - 2 * η) ^ 2 ≤ (∫ u, plateau η u) ^ 2 := by
    nlinarith only [hI, hη2]
  have hIdiv : (∫ u, plateau η u) ^ 2 ≤
      (∫ u, plateau η u) ^ 2 / (∫ u, plateau η u ^ 2) := by
    rw [le_div_iff₀ hM]
    exact (mul_le_mul_of_nonneg_left hM1 (sq_nonneg _)).trans_eq (mul_one _)
  linarith only [bumpRobin_plateau_ge hη hη2.le hδ hδ1, hBdiv, hIsq, hIdiv]

/-- One smooth profile beats any strict threshold below the completed shape value two. -/
theorem exists_plateau_completed_shape_gt {a : ℝ} (ha : a < 2) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧
      a < bumpRobin (plateau η) 1 / (∫ u, plateau η u ^ 2) +
        (∫ u, plateau η u) ^ 2 / (∫ u, plateau η u ^ 2) := by
  let δ := min ((2 - a) / 2) (1 / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have haδ : a < 2 - δ := by
    have hd : δ ≤ (2 - a) / 2 := min_le_left _ _
    linarith only [hd, ha]
  let F : ℝ → ℝ := fun η => (1 - δ) * (1 - 2 * η / δ) + (1 - 2 * η) ^ 2
  have hlim : Tendsto F (𝓝[>] 0) (𝓝 (2 - δ)) := by
    have hc : Continuous F := by dsimp [F]; fun_prop
    have hv : F 0 = 2 - δ := by dsimp [F]; ring
    rw [← hv]
    exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlarge := hlim.eventually (lt_mem_nhds haδ)
  have hsmall : ∀ᶠ η : ℝ in 𝓝[>] 0, η < 1 / 2 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by norm_num))
  obtain ⟨η, hF, hη2, hη⟩ := (hlarge.and (hsmall.and self_mem_nhdsWithin)).exists
  exact ⟨η, hη, hη2, hF.trans_le (plateau_completed_shape_ge hη hη2 hδ hδ1)⟩

/-- A smooth compact profile has a strictly positive completed Robin margin. -/
theorem exists_plateau_completed_robin_margin :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧
      Real.log (2 * Real.pi) <
        bumpRobin (plateau η) 1 / (∫ u, plateau η u ^ 2) +
          (∫ u, plateau η u) ^ 2 / (∫ u, plateau η u ^ 2) :=
  exists_plateau_completed_shape_gt RHTower.log_two_pi_lt_two

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_plateau_completed_robin_margin
