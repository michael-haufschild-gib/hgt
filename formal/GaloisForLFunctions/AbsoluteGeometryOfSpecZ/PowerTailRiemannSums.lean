import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailReferenceRemainder
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheTwistedDensityOfTheCarrierIsWeilsSymbol

/-!
# Riemann sums with a subcritical power singularity

Integral comparison controls the mesh mass near zero uniformly. Removing
a small initial interval therefore reduces power-dominated profiles to
bounded profiles on a compact interval.
-/

noncomputable section

open Finset Filter Topology MeasureTheory

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- A small initial interval has uniformly small mesh mass for a subunit power. -/
theorem normalized_powerTail_head_le {a δ : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hδ : 0 ≤ δ) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ)⁻¹ * (∑ n ∈ Icc 1 ⌊δ * N⌋₊, ((n : ℝ) / N) ^ (-a)) ≤
      δ ^ (1 - a) / (1 - a) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hb : 0 < 1 - a := by linarith only [ha1]
  have hscale (n : ℕ) : ((n : ℝ) / N) ^ (-a) =
      (N : ℝ) ^ a * powerTailWeight a n := by
    rw [Real.div_rpow (Nat.cast_nonneg n) hNp.le, Real.rpow_neg hNp.le, div_eq_mul_inv, inv_inv]
    rw [powerTailWeight, mul_comm]
  simp_rw [hscale]
  rw [← mul_sum]
  have hprefix := (powerTailPrefix_sub_integral_bounds ha ha1 (mul_nonneg hδ hNp.le)).2
  have hup : (∑ n ∈ Icc 1 ⌊δ * N⌋₊, powerTailWeight a n) ≤
      (δ * N) ^ (1 - a) / (1 - a) := by
    change powerTailPrefix a (δ * N) ≤ _
    linarith only [hprefix]
  calc
    _ ≤ (N : ℝ)⁻¹ * ((N : ℝ) ^ a * ((δ * N) ^ (1 - a) / (1 - a))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hup
        (Real.rpow_nonneg hNp.le _)) (inv_nonneg.mpr hNp.le)
    _ = (δ ^ (1 - a) / (1 - a)) *
        ((N : ℝ) ^ a * (N : ℝ) ^ (1 - a)) / N := by
      rw [Real.mul_rpow hδ hNp.le]
      ring
    _ = _ := by
      rw [← Real.rpow_add hNp, show a + (1 - a) = 1 by ring, Real.rpow_one,
        mul_div_cancel_right₀ _ hNp.ne']

/-- Clip the singular endpoint by holding its value constant below `δ`. -/
def powerTailClip (g : ℝ → ℝ) (δ t : ℝ) : ℝ := g (max δ t)

/-- Right-endpoint mesh average on the unit interval. -/
def powerTailMesh (g : ℝ → ℝ) (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Icc 1 N, g ((n : ℝ) / N)

theorem continuousOn_powerTailClip {g : ℝ → ℝ} {δ : ℝ}
    (hg : ContinuousOn g (Set.Ioc 0 1)) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ContinuousOn (powerTailClip g δ) (Set.Icc 0 1) := by
  apply hg.comp (continuous_const.max continuous_id).continuousOn
  intro t ht
  exact ⟨hδ.trans_le (le_max_left _ _), max_le hδ1 ht.2⟩

/-- The clipping error is supported near zero and retains the power envelope. -/
theorem abs_sub_powerTailClip_le {g : ℝ → ℝ} {a C δ : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hB : ∀ t ∈ Set.Ioc (0 : ℝ) 1, |g t| ≤ C * t ^ (-a))
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    |g t - powerTailClip g δ t| ≤ if t < δ then 2 * C * t ^ (-a) else 0 := by
  have hC : 0 ≤ C := by
    have h := hB 1 ⟨one_pos, le_rfl⟩
    simpa only [Real.one_rpow, mul_one] using (abs_nonneg (g 1)).trans h
  by_cases hlt : t < δ
  · rw [if_pos hlt, powerTailClip, max_eq_left hlt.le]
    have hδt : δ ^ (-a) ≤ t ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos ht.1 hlt.le (by linarith only [ha])
    calc
      _ ≤ |g t| + |g δ| := abs_sub _ _
      _ ≤ C * t ^ (-a) + C * δ ^ (-a) := add_le_add (hB t ht) (hB δ ⟨hδ, hδ1⟩)
      _ ≤ C * t ^ (-a) + C * t ^ (-a) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hδt hC)
      _ = _ := by ring
  · rw [if_neg hlt, powerTailClip, max_eq_right (le_of_not_gt hlt), sub_self, abs_zero]

/-- Continuity away from zero and a subunit power envelope give integrability. -/
theorem intervalIntegrable_of_powerTailBound {g : ℝ → ℝ} {a C : ℝ}
    (ha1 : a < 1) (hg : ContinuousOn g (Set.Ioc 0 1))
    (hB : ∀ t ∈ Set.Ioc (0 : ℝ) 1, |g t| ≤ C * t ^ (-a)) :
    IntervalIntegrable g volume 0 1 := by
  have hp : IntervalIntegrable (fun t : ℝ => t ^ (-a)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith only [ha1])
  have hCp := hp.const_mul C
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hCp ⊢
  refine hCp.mono' (hg.aestronglyMeasurable measurableSet_Ioc) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs]
  exact hB t ht

/-- Clipping a power-dominated profile changes every mesh average by a uniformly
small quantity, including meshes meeting the singular endpoint. -/
theorem abs_powerTailMesh_sub_clip_le {g : ℝ → ℝ} {a C δ : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hB : ∀ t ∈ Set.Ioc (0 : ℝ) 1, |g t| ≤ C * t ^ (-a))
    {N : ℕ} (hN : 1 ≤ N) :
    |powerTailMesh g N - powerTailMesh (powerTailClip g δ) N| ≤
      2 * C * (δ ^ (1 - a) / (1 - a)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hC : 0 ≤ C := by
    have h := hB 1 ⟨one_pos, le_rfl⟩
    simpa only [Real.one_rpow, mul_one] using (abs_nonneg (g 1)).trans h
  let S := (Icc 1 N).filter (fun n => (n : ℝ) / N < δ)
  have hsub : S ⊆ Icc 1 ⌊δ * N⌋₊ := by
    intro n hn
    obtain ⟨hnN, hnδ⟩ := mem_filter.mp hn
    refine mem_Icc.mpr ⟨(mem_Icc.mp hnN).1, ?_⟩
    rw [div_lt_iff₀ hNp] at hnδ
    by_contra hbad
    have hle : (⌊δ * N⌋₊ : ℝ) + 1 ≤ n := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.lt_of_not_ge hbad)
    have hx := Nat.lt_floor_add_one (δ * N)
    linarith only [hnδ, hle, hx]
  have hterm (n : ℕ) (hn : n ∈ Icc 1 N) :
      |g ((n : ℝ) / N) - powerTailClip g δ ((n : ℝ) / N)| ≤
        if (n : ℝ) / N < δ then 2 * C * ((n : ℝ) / N) ^ (-a) else 0 := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
    exact abs_sub_powerTailClip_le ha hδ hδ1 hB
      ⟨div_pos hnR hNp, (div_le_one hNp).mpr hnN⟩
  have hsum : (∑ n ∈ Icc 1 N,
      if (n : ℝ) / N < δ then 2 * C * ((n : ℝ) / N) ^ (-a) else 0) ≤
        2 * C * ∑ n ∈ Icc 1 ⌊δ * N⌋₊, ((n : ℝ) / N) ^ (-a) := by
    rw [← sum_filter, ← mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ =>
      Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg n) hNp.le) _)
  rw [powerTailMesh, powerTailMesh, ← mul_sub, ← sum_sub_distrib,
    abs_mul, abs_of_pos (inv_pos.mpr hNp)]
  calc
    _ ≤ (N : ℝ)⁻¹ * (2 * C * ∑ n ∈ Icc 1 ⌊δ * N⌋₊, ((n : ℝ) / N) ^ (-a)) :=
      mul_le_mul_of_nonneg_left
        (((abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)).trans hsum)
        (inv_nonneg.mpr hNp.le)
    _ = 2 * C * ((N : ℝ)⁻¹ * ∑ n ∈ Icc 1 ⌊δ * N⌋₊, ((n : ℝ) / N) ^ (-a)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (normalized_powerTail_head_le ha ha1 hδ.le hN)
      (by positivity)

theorem abs_integral_sub_powerTailClip_le {g : ℝ → ℝ} {a C δ : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hg : ContinuousOn g (Set.Ioc 0 1))
    (hB : ∀ t ∈ Set.Ioc (0 : ℝ) 1, |g t| ≤ C * t ^ (-a)) :
    |(∫ t in (0 : ℝ)..1, g t) - ∫ t in (0 : ℝ)..1, powerTailClip g δ t| ≤
      2 * C * (δ ^ (1 - a) / (1 - a)) := by
  have hC : 0 ≤ C := by
    have h := hB 1 ⟨one_pos, le_rfl⟩
    simpa only [Real.one_rpow, mul_one] using (abs_nonneg (g 1)).trans h
  have hi := intervalIntegrable_of_powerTailBound ha1 hg hB
  have hci := (continuousOn_powerTailClip hg hδ hδ1).intervalIntegrable_of_Icc zero_le_one
  rw [← intervalIntegral.integral_sub hi hci]
  have hdiff := hi.sub hci
  have hleft : IntervalIntegrable (fun t => g t - powerTailClip g δ t) volume 0 δ :=
    hdiff.mono_set (by
      rw [Set.uIcc_of_le hδ.le, Set.uIcc_of_le zero_le_one]
      exact Set.Icc_subset_Icc_right hδ1)
  have hright : IntervalIntegrable (fun t => g t - powerTailClip g δ t) volume δ 1 :=
    hdiff.mono_set (by
      rw [Set.uIcc_of_le hδ1, Set.uIcc_of_le zero_le_one]
      exact Set.Icc_subset_Icc_left hδ.le)
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright]
  have hz : (∫ t in δ..1, g t - powerTailClip g δ t) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun t ht => ?_)]
    · exact intervalIntegral.integral_zero
    · rw [Set.uIcc_of_le hδ1] at ht
      rw [powerTailClip, max_eq_right ht.1, sub_self]
  rw [hz, add_zero]
  have hp : IntervalIntegrable (fun t : ℝ => 2 * C * t ^ (-a)) volume 0 δ :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith only [ha1])).const_mul _
  have hpi : IntegrableOn (fun t : ℝ => 2 * C * t ^ (-a)) (Set.Ioc 0 δ) := by
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hδ.le] at hp
  have hbound : |∫ t in (0 : ℝ)..δ, g t - powerTailClip g δ t| ≤
      ∫ t in (0 : ℝ)..δ, 2 * C * t ^ (-a) := by
    rw [intervalIntegral.integral_of_le hδ.le, intervalIntegral.integral_of_le hδ.le,
      ← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le hpi
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs]
    have h := abs_sub_powerTailClip_le ha hδ hδ1 hB ⟨ht.1, ht.2.trans hδ1⟩
    apply h.trans
    split_ifs
    · exact le_rfl
    · positivity
  apply hbound.trans_eq
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith only [ha1])),
    show -a + 1 = 1 - a by ring, Real.zero_rpow (by linarith only [ha1]), sub_zero]

/-- Riemann sums converge for every profile dominated by an integrable power
at zero and continuous at every positive point of the unit interval. -/
theorem tendsto_powerTailMesh_of_powerBound {g : ℝ → ℝ} {a C : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hg : ContinuousOn g (Set.Ioc 0 1))
    (hB : ∀ t ∈ Set.Ioc (0 : ℝ) 1, |g t| ≤ C * t ^ (-a)) :
    Tendsto (powerTailMesh g) atTop (𝓝 (∫ t in (0 : ℝ)..1, g t)) := by
  have hb : 0 < 1 - a := by linarith only [ha1]
  have hC : 0 ≤ C := by
    have h := hB 1 ⟨one_pos, le_rfl⟩
    simpa only [Real.one_rpow, mul_one] using (abs_nonneg (g 1)).trans h
  have hzero : Tendsto (fun δ : ℝ => 2 * C * (δ ^ (1 - a) / (1 - a)))
      (𝓝 0) (𝓝 0) := by
    have hcont : ContinuousAt (fun δ : ℝ => 2 * C * (δ ^ (1 - a) / (1 - a))) 0 :=
      ((continuousAt_id.rpow_const (Or.inr hb.le)).div_const _).const_mul _
    simpa only [Real.zero_rpow hb.ne', zero_div, mul_zero] using hcont.tendsto
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨r, hr, hrbound⟩ := (Metric.tendsto_nhds_nhds.mp hzero) (ε / 3) (by positivity)
  let δ := min (r / 2) (1 / 2)
  have hδ : 0 < δ := lt_min (half_pos hr) (by norm_num)
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hδr : δ < r := (min_le_left _ _).trans_lt (by linarith only [hr])
  have hsmall : 2 * C * (δ ^ (1 - a) / (1 - a)) < ε / 3 := by
    have h := hrbound (show dist δ 0 < r by simpa only [Real.dist_eq, sub_zero, abs_of_pos hδ] using hδr)
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (show 0 ≤ 2 * C * (δ ^ (1 - a) / (1 - a)) by positivity)] using h
  have hclip := GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.tendsto_riemannSum_of_continuousOn
    (continuousOn_powerTailClip hg hδ hδ1)
  have hclip' : Tendsto (powerTailMesh (powerTailClip g δ)) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, powerTailClip g δ t)) := by
    refine hclip.congr fun N => ?_
    have he := RHTower.sum_range_succ_eq_sourcePartialSum
      (fun n => powerTailClip g δ ((n : ℝ) / N)) N
    simpa only [RHTower.sourcePartialSum, powerTailMesh, Nat.cast_add, Nat.cast_one] using
      congrArg (fun z : ℝ => (N : ℝ)⁻¹ * z) he
  obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.mp hclip') (ε / 3) (by positivity)
  refine ⟨max M 1, fun N hN => ?_⟩
  have hN1 := (le_max_right M 1).trans hN
  have hmesh := abs_powerTailMesh_sub_clip_le ha ha1 hδ hδ1 hB hN1
  have hint := abs_integral_sub_powerTailClip_le ha ha1 hδ hδ1 hg hB
  have hmid := hM N ((le_max_left M 1).trans hN)
  rw [Real.dist_eq] at hmid ⊢
  have htriangle := abs_sub_le (powerTailMesh g N) (powerTailMesh (powerTailClip g δ) N)
    (∫ t in (0 : ℝ)..1, g t)
  have htriangle' := abs_sub_le (powerTailMesh (powerTailClip g δ) N)
    (∫ t in (0 : ℝ)..1, powerTailClip g δ t) (∫ t in (0 : ℝ)..1, g t)
  rw [abs_sub_comm (∫ t in (0 : ℝ)..1, powerTailClip g δ t)] at htriangle'
  linarith only [htriangle, htriangle', hmesh, hint, hmid, hsmall]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
