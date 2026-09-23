import GaloisForLFunctions.HTGeometry.CanonicalProduct
import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem

/-!
# Minimal order-two growth of genus-one canonical products

Square-summability of the reciprocal zero norms gives more than convergence.  The positive
Nevanlinna proximity of the product is `o(r^(2 : ℕ))`.  The proof uses both global factor bounds
`|E₁(w)| ≤ exp(2|w|)` and `|E₁(w)| ≤ exp(2|w|²)`, takes their minimum termwise, and
applies dominated convergence after division by `r²`.
-/

open Complex Metric Function Filter Topology Asymptotics

namespace RHTower

theorem weierstrassE1_norm_le_exp_two_norm_sq (w : ℂ) :
    ‖weierstrassE1 w‖ ≤ Real.exp (2 * ‖w‖ ^ (2 : ℕ)) := by
  by_cases hw : ‖w‖ ≤ 1
  · calc
      ‖weierstrassE1 w‖ ≤ ‖weierstrassE1 w - 1‖ + 1 := by
        have := norm_add_le (weierstrassE1 w - 1) 1
        simpa using this
      _ ≤ ‖w‖ ^ (2 : ℕ) + 1 := by gcongr; exact weierstrassE1_sub_one_norm_le hw
      _ ≤ Real.exp (‖w‖ ^ (2 : ℕ)) := Real.add_one_le_exp _
      _ ≤ Real.exp (2 * ‖w‖ ^ (2 : ℕ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [sq_nonneg ‖w‖]
  · have hw1 : 1 ≤ ‖w‖ := le_of_lt (lt_of_not_ge hw)
    rw [weierstrassE1, norm_mul, norm_exp]
    calc
      ‖1 - w‖ * Real.exp w.re ≤ (1 + ‖w‖) * Real.exp ‖w‖ := by
        gcongr
        · simpa [add_comm] using norm_sub_le (1 : ℂ) w
        · exact re_le_norm w
      _ ≤ Real.exp ‖w‖ * Real.exp ‖w‖ := by
        gcongr
        simpa [add_comm] using Real.add_one_le_exp ‖w‖
      _ = Real.exp (2 * ‖w‖) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (2 * ‖w‖ ^ (2 : ℕ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [norm_nonneg w]

theorem weierstrassE1_norm_le_exp_two_norm (w : ℂ) :
    ‖weierstrassE1 w‖ ≤ Real.exp (2 * ‖w‖) := by
  rw [weierstrassE1, norm_mul, norm_exp]
  calc
    ‖1 - w‖ * Real.exp w.re ≤ (1 + ‖w‖) * Real.exp ‖w‖ := by
      gcongr
      · simpa [add_comm] using norm_sub_le (1 : ℂ) w
      · exact re_le_norm w
    _ ≤ Real.exp ‖w‖ * Real.exp ‖w‖ := by
      gcongr
      simpa [add_comm] using Real.add_one_le_exp ‖w‖
    _ = Real.exp (2 * ‖w‖) := by rw [← Real.exp_add]; congr 1; ring

theorem canonicalProductE1Indexed_norm_le_exp_min {ι : Type*}
    (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => 1 / ‖a i‖ ^ (2 : ℕ))) (z : ℂ) :
    ‖canonicalProductE1Indexed a z‖ ≤ Real.exp (∑' i,
      min (2 * ‖z‖ / ‖a i‖) (2 * ‖z‖ ^ (2 : ℕ) / ‖a i‖ ^ (2 : ℕ))) := by
  let d : ι → ℂ := fun i => weierstrassE1 (z / a i) - 1
  have hdsum : Summable d :=
    (canonicalProductE1Indexed_sub_one_norm_summable a ha hsum z).of_norm
  have hfac : Multipliable (fun i => weierstrassE1 (z / a i)) := by
    have hm := Complex.multipliable_one_add_of_summable hdsum
    convert hm using 1
    ext i
    simp only [d]
    ring
  let u : ι → ℝ := fun i =>
    min (2 * ‖z‖ / ‖a i‖) (2 * ‖z‖ ^ (2 : ℕ) / ‖a i‖ ^ (2 : ℕ))
  have husum : Summable u := by
    have hdom : Summable (fun i => 2 * ‖z‖ ^ (2 : ℕ) / ‖a i‖ ^ (2 : ℕ)) := by
      refine (hsum.mul_left (2 * ‖z‖ ^ (2 : ℕ))).congr (fun i => ?_)
      ring
    exact Summable.of_nonneg_of_le
      (fun i => le_min (by positivity) (by positivity))
      (fun i => min_le_right _ _) hdom
  have hexpsum : Summable (fun i => Real.log (Real.exp (u i))) := by
    simpa using husum
  have hexpmult : Multipliable (fun i => Real.exp (u i)) :=
    Real.multipliable_of_summable_log (fun i => Real.exp_pos _) hexpsum
  rw [canonicalProductE1Indexed, hfac.norm_tprod]
  calc
    (∏' i, ‖weierstrassE1 (z / a i)‖) ≤ ∏' i, Real.exp (u i) := by
      apply le_of_tendsto_of_tendsto' hfac.norm.hasProd hexpmult.hasProd
      intro s
      apply Finset.prod_le_prod
      · intro i _
        exact norm_nonneg _
      · intro i _
        by_cases hle : 2 * ‖z‖ / ‖a i‖ ≤ 2 * ‖z‖ ^ (2 : ℕ) / ‖a i‖ ^ (2 : ℕ)
        · rw [show u i = 2 * ‖z‖ / ‖a i‖ by simp only [u]; exact min_eq_left hle]
          calc
            ‖weierstrassE1 (z / a i)‖ ≤ Real.exp (2 * ‖z / a i‖) :=
              weierstrassE1_norm_le_exp_two_norm _
            _ = Real.exp (2 * ‖z‖ / ‖a i‖) := by rw [norm_div]; congr 1; ring
        · rw [show u i = 2 * ‖z‖ ^ (2 : ℕ) / ‖a i‖ ^ (2 : ℕ) by
              simp only [u]
              exact min_eq_right (le_of_not_ge hle)]
          calc
            ‖weierstrassE1 (z / a i)‖ ≤ Real.exp (2 * ‖z / a i‖ ^ (2 : ℕ)) :=
              weierstrassE1_norm_le_exp_two_norm_sq _
            _ = Real.exp (2 * ‖z‖ ^ (2 : ℕ) / ‖a i‖ ^ (2 : ℕ)) := by
              rw [norm_div, div_pow]
              congr 1
              ring
    _ = Real.exp (∑' i, u i) := by
      simpa only [Real.log_exp] using
        (Real.rexp_tsum_eq_tprod (fun i => Real.exp_pos _) hexpsum).symm
    _ = _ := rfl

open ValueDistribution in
theorem canonicalProductE1Indexed_proximity_top_le_min {ι : Type*}
    (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => 1 / ‖a i‖ ^ (2 : ℕ))) (r : ℝ) :
    proximity (canonicalProductE1Indexed a) ⊤ r ≤
      ∑' i, min (2 * |r| / ‖a i‖) (2 * |r| ^ (2 : ℕ) / ‖a i‖ ^ (2 : ℕ)) := by
  let u : ι → ℝ := fun i =>
    min (2 * |r| / ‖a i‖) (2 * |r| ^ (2 : ℕ) / ‖a i‖ ^ (2 : ℕ))
  have husum : Summable u := by
    have hdom : Summable (fun i => 2 * |r| ^ (2 : ℕ) / ‖a i‖ ^ (2 : ℕ)) := by
      refine (hsum.mul_left (2 * |r| ^ (2 : ℕ))).congr (fun i => ?_)
      ring
    exact Summable.of_nonneg_of_le
      (fun i => le_min (by positivity) (by positivity))
      (fun i => min_le_right _ _) hdom
  rw [proximity_top]
  rw [← Real.circleAverage_const (∑' i, u i) 0 r]
  apply Real.circleAverage_mono
  · exact MeromorphicOn.circleIntegrable_posLog_norm
      (fun z _ => (canonicalProductE1Indexed_analytic a ha hsum z (Set.mem_univ _)).meromorphicAt)
  · exact circleIntegrable_const _ _ _
  · intro z hzmem
    have hnorm := canonicalProductE1Indexed_norm_le_exp_min a ha hsum z
    have hz : ‖z‖ = |r| := by simpa [mem_sphere_zero_iff_norm] using hzmem
    have harg : 0 ≤ ∑' i, min (2 * ‖z‖ / ‖a i‖)
        (2 * ‖z‖ ^ (2 : ℕ) / ‖a i‖ ^ (2 : ℕ)) :=
      tsum_nonneg (fun _ => le_min (by positivity) (by positivity))
    calc
      Real.posLog ‖canonicalProductE1Indexed a z‖ ≤
          Real.posLog (Real.exp (∑' i, min (2 * ‖z‖ / ‖a i‖)
            (2 * ‖z‖ ^ (2 : ℕ) / ‖a i‖ ^ (2 : ℕ)))) :=
        Real.monotoneOn_posLog (norm_nonneg _) (Real.exp_pos _).le hnorm
      _ = ∑' i, min (2 * ‖z‖ / ‖a i‖)
            (2 * ‖z‖ ^ (2 : ℕ) / ‖a i‖ ^ (2 : ℕ)) := by
        have hexp1 : 1 ≤ |Real.exp (∑' i, min (2 * ‖z‖ / ‖a i‖)
            (2 * ‖z‖ ^ (2 : ℕ) / ‖a i‖ ^ (2 : ℕ)))| := by
          rw [abs_of_pos (Real.exp_pos _)]
          exact Real.one_le_exp harg
        rw [Real.posLog_eq_log hexp1, Real.log_exp]
      _ = ∑' i, u i := by
        apply tsum_congr
        intro i
        simp only [u, hz]

theorem canonicalProduct_minGrowth_div_sq_tendsto_zero {ι : Type*}
    (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => 1 / ‖a i‖ ^ (2 : ℕ))) :
    Tendsto (fun r : ℝ =>
      (∑' i, min (2 * |r| / ‖a i‖) (2 * |r| ^ (2 : ℕ) / ‖a i‖ ^ (2 : ℕ))) / r ^ (2 : ℕ))
      atTop (𝓝 0) := by
  let v : ℝ → ι → ℝ := fun r i =>
    min (2 / (r * ‖a i‖)) (2 / ‖a i‖ ^ (2 : ℕ))
  have hv_tendsto : ∀ i, Tendsto (fun r => v r i) atTop (𝓝 0) := by
    intro i
    have hA : 0 < ‖a i‖ := norm_pos_iff.mpr (ha i)
    have hden : Tendsto (fun r : ℝ => r * ‖a i‖) atTop atTop :=
      tendsto_id.atTop_mul_const hA
    have hfirst : Tendsto (fun r : ℝ => 2 / (r * ‖a i‖)) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.div_atTop hden
    apply squeeze_zero'
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      exact le_min (by positivity) (by positivity)
    · exact Eventually.of_forall fun r => min_le_left _ _
    · exact hfirst
  have hv_bound : ∀ᶠ r : ℝ in atTop, ∀ i, ‖v r i‖ ≤ 2 / ‖a i‖ ^ (2 : ℕ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr i
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by positivity) (by positivity))]
    exact min_le_right _ _
  have hbound_sum : Summable (fun i => 2 / ‖a i‖ ^ (2 : ℕ)) := by
    refine (hsum.mul_left 2).congr (fun i => ?_)
    ring
  have hv_sum : Tendsto (fun r => ∑' i, v r i) atTop (𝓝 0) := by
    simpa using tendsto_tsum_of_dominated_convergence hbound_sum hv_tendsto hv_bound
  refine hv_sum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hrne : r ≠ 0 := ne_of_gt hr
  rw [abs_of_pos hr, ← tsum_div_const]
  apply tsum_congr
  intro i
  simp only [v]
  rw [← min_div_div_right (sq_nonneg r)]
  congr 1 <;> field_simp

theorem canonicalProduct_minGrowth_isLittleO_sq {ι : Type*}
    (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => 1 / ‖a i‖ ^ (2 : ℕ))) :
    (fun r : ℝ => ∑' i,
      min (2 * |r| / ‖a i‖) (2 * |r| ^ (2 : ℕ) / ‖a i‖ ^ (2 : ℕ))) =o[atTop]
      (fun r : ℝ => r ^ (2 : ℕ)) := by
  apply isLittleO_of_tendsto
  · intro r hr
    have : r = 0 := sq_eq_zero_iff.mp hr
    subst r
    simp
  · exact canonicalProduct_minGrowth_div_sq_tendsto_zero a ha hsum

open ValueDistribution in
theorem canonicalProductE1Indexed_proximity_isLittleO_sq {ι : Type*}
    (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => 1 / ‖a i‖ ^ (2 : ℕ))) :
    proximity (canonicalProductE1Indexed a) ⊤ =o[atTop] (fun r : ℝ => r ^ (2 : ℕ)) := by
  have hU := canonicalProduct_minGrowth_isLittleO_sq a ha hsum
  apply isLittleO_iff.mpr
  intro c hc
  filter_upwards [isLittleO_iff.mp hU hc] with r hr
  rw [Real.norm_eq_abs, abs_of_nonneg (proximity_nonneg r)]
  calc
    proximity (canonicalProductE1Indexed a) ⊤ r ≤
        ∑' i, min (2 * |r| / ‖a i‖) (2 * |r| ^ (2 : ℕ) / ‖a i‖ ^ (2 : ℕ)) :=
      canonicalProductE1Indexed_proximity_top_le_min a ha hsum r
    _ = ‖∑' i, min (2 * |r| / ‖a i‖) (2 * |r| ^ (2 : ℕ) / ‖a i‖ ^ (2 : ℕ))‖ := by
      rw [Real.norm_eq_abs]
      exact (abs_of_nonneg
        (tsum_nonneg (fun _ => le_min (by positivity) (by positivity)))).symm
    _ ≤ c * ‖r ^ (2 : ℕ)‖ := hr

end RHTower
