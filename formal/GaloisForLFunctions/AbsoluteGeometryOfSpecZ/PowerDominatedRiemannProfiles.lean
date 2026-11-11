import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailRiemannSums

/-!
# Power-dominated profiles with jumps

A power envelope controls both the mesh mass and integral near zero.
Convergence after every positive cutoff therefore gives convergence of
the full profile, including arithmetic staircases.
-/

noncomputable section

open Finset Filter Topology MeasureTheory

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- A power envelope gives integrability without continuity. -/
theorem integrableOn_of_measurable_powerBound {g : ℝ → ℝ} {a C : ℝ}
    (ha1 : a < 1) (hg : Measurable g)
    (hB : ∀ t ∈ Set.Ioc (0 : ℝ) 1, |g t| ≤ C * t ^ (-a)) :
    IntegrableOn g (Set.Ioc 0 1) := by
  have hp : IntervalIntegrable (fun t : ℝ => t ^ (-a)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith only [ha1])
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hp
  refine (hi.const_mul C).mono' hg.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  simpa only [Real.norm_eq_abs] using hB t ht

/-- The contribution below a cutoff is uniformly small on every mesh. -/
theorem abs_tailRiemannSum_indicator_Iic_le {g : ℝ → ℝ} {a C δ : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hδ : 0 ≤ δ)
    (hB : ∀ t ∈ Set.Ioc (0 : ℝ) 1, |g t| ≤ C * t ^ (-a))
    {N : ℕ} (hN : 1 ≤ N) :
    |tailRiemannSum ((Set.Iic δ).indicator g) N| ≤
      C * (δ ^ (1 - a) / (1 - a)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hC : 0 ≤ C := by
    have h := hB 1 ⟨one_pos, le_rfl⟩
    simpa only [Real.one_rpow, mul_one] using (abs_nonneg (g 1)).trans h
  let S : Finset ℕ := (Icc 1 N).filter (fun n : ℕ => (n : ℝ) / N ≤ δ)
  have hsub : S ⊆ Icc 1 ⌊δ * N⌋₊ := by
    intro n hn
    obtain ⟨hnN, hnδ⟩ := mem_filter.mp hn
    refine mem_Icc.mpr ⟨(mem_Icc.mp hnN).1, ?_⟩
    exact (Nat.le_floor_iff (mul_nonneg hδ hNp.le)).mpr ((div_le_iff₀ hNp).mp hnδ)
  have he : (∑ n ∈ Icc 1 N, (Set.Iic δ).indicator g ((n : ℝ) / N)) =
      ∑ n ∈ S, g ((n : ℝ) / N) := by
    simp only [Set.indicator, Set.mem_Iic, sum_filter, S]
  rw [tailRiemannSum, he, abs_div, abs_of_pos hNp, div_eq_inv_mul]
  calc
    _ ≤ (N : ℝ)⁻¹ * ∑ n ∈ S, |g ((n : ℝ) / N)| :=
      mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (inv_nonneg.mpr hNp.le)
    _ ≤ (N : ℝ)⁻¹ * ∑ n ∈ S, C * ((n : ℝ) / N) ^ (-a) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hNp.le)
      exact sum_le_sum fun n hn => hB _ (natCast_div_mem_Ioc (mem_filter.mp hn).1)
    _ = C * ((N : ℝ)⁻¹ * ∑ n ∈ S, ((n : ℝ) / N) ^ (-a)) := by
      rw [← mul_sum]
      ring
    _ ≤ C * ((N : ℝ)⁻¹ * ∑ n ∈ Icc 1 ⌊δ * N⌋₊, ((n : ℝ) / N) ^ (-a)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hNp.le)
      exact sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
        Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg n) hNp.le) _
    _ ≤ _ := mul_le_mul_of_nonneg_left (normalized_powerTail_head_le ha ha1 hδ hN) hC

/-- The integral below a cutoff obeys the same power bound as the mesh. -/
theorem abs_integral_indicator_Iic_powerBound_le {g : ℝ → ℝ} {a C δ : ℝ}
    (ha1 : a < 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hB : ∀ t ∈ Set.Ioc (0 : ℝ) 1, |g t| ≤ C * t ^ (-a)) :
    |∫ t in Set.Ioc (0 : ℝ) 1, (Set.Iic δ).indicator g t| ≤
      C * (δ ^ (1 - a) / (1 - a)) := by
  have hset : Set.Ioc (0 : ℝ) 1 ∩ Set.Iic δ = Set.Ioc 0 δ := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iic]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans hδ1⟩, h.2⟩⟩
  rw [setIntegral_indicator measurableSet_Iic, hset]
  have hp : IntervalIntegrable (fun t : ℝ => C * t ^ (-a)) volume 0 δ :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith only [ha1])).const_mul C
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le hδ.le).mp hp
  have hbound : |∫ t in Set.Ioc (0 : ℝ) δ, g t| ≤
      ∫ t in Set.Ioc (0 : ℝ) δ, C * t ^ (-a) := by
    rw [← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le hi
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [Real.norm_eq_abs] using hB t ⟨ht.1, ht.2.trans hδ1⟩
  apply hbound.trans_eq
  rw [← intervalIntegral.integral_of_le hδ.le, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith only [ha1])),
    show -a + 1 = 1 - a by ring, Real.zero_rpow (by linarith only [ha1]), sub_zero]

/-- Convergence on every truncated interval extends across an integrable power
singularity. Jumps of the profile are allowed. -/
theorem riemannOn_of_powerBound_and_cuts {g : ℝ → ℝ} {a C : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hg : Measurable g)
    (hB : ∀ t ∈ Set.Ioc (0 : ℝ) 1, |g t| ≤ C * t ^ (-a))
    (hcut : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → RiemannOn ((Set.Ioi δ).indicator g)) :
    RiemannOn g := by
  have hi := integrableOn_of_measurable_powerBound ha1 hg hB
  refine ⟨hi, ?_⟩
  have hb : 0 < 1 - a := by linarith only [ha1]
  have hC : 0 ≤ C := by
    have h := hB 1 ⟨one_pos, le_rfl⟩
    simpa only [Real.one_rpow, mul_one] using (abs_nonneg (g 1)).trans h
  have hz : Tendsto (fun δ : ℝ => C * (δ ^ (1 - a) / (1 - a))) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun δ : ℝ => C * (δ ^ (1 - a) / (1 - a))) 0 :=
      ((continuousAt_id.rpow_const (Or.inr hb.le)).div_const _).const_mul _
    simpa only [Real.zero_rpow hb.ne', zero_div, mul_zero] using hc.tendsto
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨r, hr, hrbound⟩ := (Metric.tendsto_nhds_nhds.mp hz) (ε / 3) (by positivity)
  let δ := min (r / 2) (1 / 2)
  have hδ : 0 < δ := lt_min (half_pos hr) (by norm_num)
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hδr : δ < r := (min_le_left _ _).trans_lt (by linarith only [hr])
  have hsmall : C * (δ ^ (1 - a) / (1 - a)) < ε / 3 := by
    have h := hrbound (show dist δ 0 < r by
      simpa only [Real.dist_eq, sub_zero, abs_of_pos hδ] using hδr)
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg (show 0 ≤ C * (δ ^ (1 - a) / (1 - a)) by positivity)] using h
  let l := (Set.Iic δ).indicator g
  let u := (Set.Ioi δ).indicator g
  have he (t : ℝ) : g t = l t + u t := by
    dsimp only [l, u]
    by_cases ht : t ≤ δ
    · rw [Set.indicator_of_mem ht, Set.indicator_of_notMem (not_lt.mpr ht), add_zero]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_mem (lt_of_not_ge ht), zero_add]
  have hm (N : ℕ) : tailRiemannSum g N = tailRiemannSum l N + tailRiemannSum u N := by
    rw [tailRiemannSum, sum_congr rfl (fun n _ => he ((n : ℝ) / N)),
      sum_add_distrib, add_div]
    rfl
  have hint : (∫ t in Set.Ioc (0 : ℝ) 1, g t) =
      (∫ t in Set.Ioc (0 : ℝ) 1, l t) + ∫ t in Set.Ioc (0 : ℝ) 1, u t := by
    calc
      _ = ∫ t in Set.Ioc (0 : ℝ) 1, l t + u t := integral_congr_ae (Eventually.of_forall he)
      _ = _ := integral_add (hi.indicator measurableSet_Iic) (hi.indicator measurableSet_Ioi)
  obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.mp (hcut δ hδ hδ1).2) (ε / 3) (by positivity)
  refine ⟨max M 1, fun N hN => ?_⟩
  have hmB := abs_tailRiemannSum_indicator_Iic_le ha ha1 hδ.le hB
    ((le_max_right M 1).trans hN)
  have hiB := abs_integral_indicator_Iic_powerBound_le ha1 hδ hδ1 hB
  have hmid := hM N ((le_max_left M 1).trans hN)
  rw [Real.dist_eq] at hmid ⊢
  rw [hm, hint]
  have ht : |tailRiemannSum l N + tailRiemannSum u N -
      ((∫ t in Set.Ioc (0 : ℝ) 1, l t) + ∫ t in Set.Ioc (0 : ℝ) 1, u t)| ≤
      |tailRiemannSum l N| + |∫ t in Set.Ioc (0 : ℝ) 1, l t| +
        |tailRiemannSum u N - ∫ t in Set.Ioc (0 : ℝ) 1, u t| := by
    have heq : tailRiemannSum l N + tailRiemannSum u N -
        ((∫ t in Set.Ioc (0 : ℝ) 1, l t) + ∫ t in Set.Ioc (0 : ℝ) 1, u t) =
        (tailRiemannSum l N - ∫ t in Set.Ioc (0 : ℝ) 1, l t) +
          (tailRiemannSum u N - ∫ t in Set.Ioc (0 : ℝ) 1, u t) := by ring
    rw [heq]
    exact (abs_add _ _).trans (add_le_add (abs_sub _ _) le_rfl)
  linarith only [ht, hmB, hiB, hmid, hsmall]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
