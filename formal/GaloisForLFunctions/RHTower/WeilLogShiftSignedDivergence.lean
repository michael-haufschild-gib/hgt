import GaloisForLFunctions.RHTower.WeilLogShiftDivergentMinorant

/-!
# Divergent deficit potentials with finite positive excess

Summable excess contributes a uniformly bounded amount to every truncated
log-shift probe. Divergent origin or sampled deficit potentials therefore give
fixed probes tending to minus infinity, without a coefficient sign assumption.
-/

open Filter Topology Zeta23

noncomputable section

namespace RHTower

open WeilExcess

private theorem summable_excess_potential_of_summable {lam : ℕ → ℝ}
    (hexc : Summable (deviationExcess lam)) (y : ℝ) :
    Summable fun n => deviationExcess lam n *
      (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n)) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (deviationExcess_nonneg _ _)
      (add_nonneg (riemannAutocorr_nonneg _) (riemannAutocorr_nonneg _)))
    (fun n => ?_) (hexc.mul_right (2 * riemannAutocorr 0))
  apply mul_le_mul_of_nonneg_left _ (deviationExcess_nonneg _ _)
  linarith only [riemannAutocorr_le_zero (y + Real.log n),
    riemannAutocorr_le_zero (y - Real.log n)]

/-- Finite excess makes signed-potential convergence equivalent to convergence
of the nonnegative deficit potential, at each individual real shift. -/
theorem summable_potential_iff_summable_deficit {lam : ℕ → ℝ}
    (hexc : Summable (deviationExcess lam)) (y : ℝ) :
    (Summable fun n => weilDeviation lam n *
      (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n))) ↔
    Summable fun n => deviationDeficit lam n *
      (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n)) := by
  have hsE := summable_excess_potential_of_summable hexc y
  constructor <;> intro hs
  · refine (hsE.sub hs).congr fun n => ?_
    rw [weilDeviation_eq_sub]
    ring
  · refine (hsE.sub hs).congr fun n => ?_
    rw [weilDeviation_eq_sub]
    ring

/-- Any divergent nonnegative full potential forces its truncated potentials
to infinity, using finite partial sums rather than monotonicity of cutoffs. -/
theorem tendsto_truncated_kernelPotential_atTop_of_not_summable {v : ℕ → ℝ}
    (hv : ∀ n, 0 ≤ v n) (y : ℝ)
    (hbad : ¬ Summable fun n => v n *
      (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n))) :
    Tendsto (fun L : ℝ => ∑' n, v n *
      (truncatedRiemannAutocorr L (y + Real.log n) +
        truncatedRiemannAutocorr L (y - Real.log n))) atTop atTop := by
  have hfull := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun n => mul_nonneg (hv n)
      (add_nonneg (riemannAutocorr_nonneg _) (riemannAutocorr_nonneg _)))).mp hbad
  refine tendsto_atTop.mpr fun b => ?_
  obtain ⟨N, hN⟩ := (hfull.eventually_ge_atTop (b + 1)).exists
  have hfinite := tendsto_finsetSum (Finset.range N) (fun n _ =>
    ((tendsto_truncatedRiemannAutocorr (y + Real.log n)).add
      (tendsto_truncatedRiemannAutocorr (y - Real.log n))).const_mul (v n))
  have hlt := (tendsto_order.mp hfinite).1 b (by linarith only [hN])
  filter_upwards [hlt] with L hL
  exact hL.le.trans ((summable_truncated_potential_term v L y).sum_le_tsum
    (Finset.range N) (fun n _ => mul_nonneg (hv n)
      (add_nonneg (truncatedRiemannAutocorr_nonneg _ _)
        (truncatedRiemannAutocorr_nonneg _ _))))

/-- Positive excess has a uniform probe budget; the remaining terms are the
truncated origin and shifted deficit potentials. -/
theorem logShift_probe_le_excess_deficit {lam : ℕ → ℝ}
    (hexc : Summable (deviationExcess lam)) (L c : ℝ) :
    (weilFullFunctional lam (EF.weilTest (logShiftRiemannDifference L c)
      (logShiftRiemannDifference L c))).re ≤
      (zetaZeroConfig.W (logShiftRiemannDifference L c)
        (logShiftRiemannDifference L c)).re +
      4 * riemannAutocorr 0 * (∑' n, deviationExcess lam n) +
      4 * (∑' n, deviationDeficit lam n * truncatedRiemannAutocorr L (Real.log n)) -
      2 * (∑' n, deviationDeficit lam n *
        (truncatedRiemannAutocorr L (c + Real.log n) +
          truncatedRiemannAutocorr L (c - Real.log n))) := by
  let T := fun (w : ℕ → ℝ) (y : ℝ) => ∑' n, w n *
    (truncatedRiemannAutocorr L (y + Real.log n) +
      truncatedRiemannAutocorr L (y - Real.log n))
  have hT (w : ℕ → ℝ) (y : ℝ) := summable_truncated_potential_term w L y
  have hsplit (y : ℝ) : truncatedDeviationPotential lam L y =
      T (deviationExcess lam) y - T (deviationDeficit lam) y := by
    dsimp only [truncatedDeviationPotential, T]
    rw [← (hT (deviationExcess lam) y).tsum_sub (hT (deviationDeficit lam) y)]
    apply tsum_congr
    intro n
    rw [weilDeviation_eq_sub]
    ring
  have hE0 : 0 ≤ T (deviationExcess lam) 0 :=
    tsum_nonneg (fun n => mul_nonneg (deviationExcess_nonneg _ _)
      (add_nonneg (truncatedRiemannAutocorr_nonneg _ _)
        (truncatedRiemannAutocorr_nonneg _ _)))
  have hEc : T (deviationExcess lam) c ≤
      2 * riemannAutocorr 0 * ∑' n, deviationExcess lam n := by
    calc
      _ ≤ ∑' n, deviationExcess lam n * (2 * riemannAutocorr 0) := by
        apply (hT (deviationExcess lam) c).tsum_le_tsum _ (hexc.mul_right _)
        intro n
        apply mul_le_mul_of_nonneg_left _ (deviationExcess_nonneg _ _)
        have h1 := (truncatedRiemannAutocorr_le_riemannAutocorr L (c + Real.log n)).trans
          (riemannAutocorr_le_zero _)
        have h2 := (truncatedRiemannAutocorr_le_riemannAutocorr L (c - Real.log n)).trans
          (riemannAutocorr_le_zero _)
        linarith only [h1, h2]
      _ = _ := by rw [tsum_mul_right]; ring
  have hD0 : T (deviationDeficit lam) 0 =
      2 * (∑' n, deviationDeficit lam n * truncatedRiemannAutocorr L (Real.log n)) := by
    dsimp only [T]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [zero_add, zero_sub, truncatedRiemannAutocorr_neg]
    ring
  rw [logShift_probe_potential_identity, hsplit c, hsplit 0, hD0]
  change _ ≤ _ + _ + _ - 2 * T (deviationDeficit lam) c
  linarith only [hE0, hEc]

/-- Divergent origin deficit mass forces every fixed integer-log probe of size
at least four to minus infinity, even with arbitrary signed coefficients. -/
theorem tendsto_logShift_probe_atBot_of_nonsummable_deficit_origin {lam : ℕ → ℝ}
    (hexc : Summable (deviationExcess lam))
    (hbad : ¬ Summable fun n => deviationDeficit lam n * riemannAutocorr (Real.log n))
    {m : ℕ} (hm : 4 ≤ Real.log m) :
    Tendsto (fun L : ℝ => (weilFullFunctional lam (EF.weilTest
      (logShiftRiemannDifference L (Real.log m))
      (logShiftRiemannDifference L (Real.log m)))).re) atTop atBot := by
  obtain ⟨H, hH⟩ := exists_truncated_origin_gain_bound (deviationDeficit lam)
    (deviationDeficit_nonneg lam) hm
  let C := 4 * riemannAutocorr 0 * (∑' n, deviationExcess lam n) + 8 * H
  have hdiv := tendsto_truncated_origin_atTop_of_not_summable (deviationDeficit_nonneg lam) hbad
  have hzero := (tendsto_order.mp (tendsto_logShift_zeroSide m)).2 1 (by norm_num)
  refine tendsto_atBot.mpr fun b => ?_
  filter_upwards [hzero, hdiv.eventually_ge_atTop ((1 + C - b) / 4)] with L hW hL
  have hu := logShift_probe_le_excess_deficit hexc L (Real.log m)
  have hh := hH L
  dsimp only [C] at hL
  linarith only [hu, hh, hW, hL]

/-- With finite origin deficit mass, divergence at any fixed sampled deficit
potential forces that probe to minus infinity. -/
theorem tendsto_logShift_probe_atBot_of_nonsummable_deficit_sample {lam : ℕ → ℝ}
    (hexc : Summable (deviationExcess lam))
    (horigin : Summable fun n => deviationDeficit lam n * riemannAutocorr (Real.log n))
    (m : ℕ)
    (hbad : ¬ Summable fun n => deviationDeficit lam n *
      (riemannAutocorr (Real.log m + Real.log n) +
        riemannAutocorr (Real.log m - Real.log n))) :
    Tendsto (fun L : ℝ => (weilFullFunctional lam (EF.weilTest
      (logShiftRiemannDifference L (Real.log m))
      (logShiftRiemannDifference L (Real.log m)))).re) atTop atBot := by
  let D := ∑' n, deviationDeficit lam n * riemannAutocorr (Real.log n)
  let C := 4 * riemannAutocorr 0 * (∑' n, deviationExcess lam n) + 4 * D
  have hD (L : ℝ) :
      (∑' n, deviationDeficit lam n * truncatedRiemannAutocorr L (Real.log n)) ≤ D :=
    (summable_truncated_origin_term (deviationDeficit lam) L).tsum_le_tsum
      (fun n => mul_le_mul_of_nonneg_left
        (truncatedRiemannAutocorr_le_riemannAutocorr _ _) (deviationDeficit_nonneg _ _)) horigin
  have hdiv := tendsto_truncated_kernelPotential_atTop_of_not_summable
    (deviationDeficit_nonneg lam) (Real.log m) hbad
  have hzero := (tendsto_order.mp (tendsto_logShift_zeroSide m)).2 1 (by norm_num)
  refine tendsto_atBot.mpr fun b => ?_
  filter_upwards [hzero, hdiv.eventually_ge_atTop ((1 + C - b) / 2)] with L hW hL
  have hu := logShift_probe_le_excess_deficit hexc L (Real.log m)
  have hd := hD L
  dsimp only [C] at hL
  linarith only [hu, hd, hW, hL]

end RHTower
