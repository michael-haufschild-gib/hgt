import GaloisForLFunctions.RHTower.WeilLogShiftTailComparison

/-!
# Fixed separation for arbitrary strict minorants

When the origin deficit moment diverges, every integer-log shift of size at
least four has probe values tending to minus infinity. Together with the finite
origin-moment theorem this removes every growth and summability premise from
fixed-probe separation of strict minorants.
-/

open Filter Topology Zeta23

noncomputable section

namespace RHTower

open WeilExcess

/-- The single-kernel truncated origin series is summable for arbitrary
coefficients and every real cutoff. -/
theorem summable_truncated_origin_term (v : ℕ → ℝ) (L : ℝ) :
    Summable fun n => v n * truncatedRiemannAutocorr L (Real.log n) := by
  refine ((summable_truncated_potential_term v L 0).mul_left (1 / 2 : ℝ)).congr
    (fun n => ?_)
  rw [zero_add, zero_sub, truncatedRiemannAutocorr_neg]
  ring

/-- A divergent nonnegative origin series forces its truncated sums to infinity.
The proof uses finite partial sums, without monotonicity of the cutoffs. -/
theorem tendsto_truncated_origin_atTop_of_not_summable {v : ℕ → ℝ}
    (hv : ∀ n, 0 ≤ v n)
    (hbad : ¬ Summable fun n => v n * riemannAutocorr (Real.log n)) :
    Tendsto (fun L : ℝ => ∑' n, v n * truncatedRiemannAutocorr L (Real.log n))
      atTop atTop := by
  have hfull := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun n => mul_nonneg (hv n) (riemannAutocorr_nonneg _))).mp hbad
  refine tendsto_atTop.mpr fun b => ?_
  obtain ⟨N, hN⟩ := (hfull.eventually_ge_atTop (b + 1)).exists
  have hfinite := tendsto_finsetSum (Finset.range N)
    (fun n _ => (tendsto_truncatedRiemannAutocorr (Real.log n)).const_mul (v n))
  have hlt := (tendsto_order.mp hfinite).1 b (by linarith only [hN])
  filter_upwards [hlt] with L hL
  exact hL.le.trans ((summable_truncated_origin_term v L).sum_le_tsum
    (Finset.range N) (fun n _ => mul_nonneg (hv n) (truncatedRiemannAutocorr_nonneg _ _)))

/-- A fixed inward shift of size at least four controls four times the origin
mass, up to a finite head bound independent of the cutoff. -/
theorem exists_truncated_origin_gain_bound (v : ℕ → ℝ) (hv : ∀ n, 0 ≤ v n)
    {c : ℝ} (hc : 4 ≤ c) :
    ∃ H : ℝ, ∀ L : ℝ,
      4 * (∑' n, v n * truncatedRiemannAutocorr L (Real.log n)) ≤
        (∑' n, v n * (truncatedRiemannAutocorr L (c + Real.log n) +
          truncatedRiemannAutocorr L (c - Real.log n))) + 4 * H := by
  obtain ⟨Y, hY⟩ := exists_truncatedRiemannAutocorr_tail_shift_gain hc 4
  let F := Finset.range (⌊Real.exp Y⌋₊ + 1)
  let head : ℕ → ℝ := fun n => if n ∈ F then v n * riemannAutocorr (Real.log n) else 0
  have hshead : Summable head := summable_of_ne_finset_zero (s := F)
    (fun n hn => by simp only [head, if_neg hn])
  let H := ∑' n, head n
  let D := fun L : ℝ => ∑' n, v n * truncatedRiemannAutocorr L (Real.log n)
  let T := fun L y : ℝ => ∑' n, v n *
    (truncatedRiemannAutocorr L (y + Real.log n) +
      truncatedRiemannAutocorr L (y - Real.log n))
  have hD (L : ℝ) := summable_truncated_origin_term v L
  have hT (L y : ℝ) := summable_truncated_potential_term v L y
  have hbound (L : ℝ) : 4 * D L ≤ T L c + 4 * H := by
    have hpoint (n : ℕ) :
        4 * (v n * truncatedRiemannAutocorr L (Real.log n)) ≤
          v n * (truncatedRiemannAutocorr L (c + Real.log n) +
            truncatedRiemannAutocorr L (c - Real.log n)) + 4 * head n := by
      have hplus := mul_nonneg (hv n) (truncatedRiemannAutocorr_nonneg L (c + Real.log n))
      have hminus := mul_nonneg (hv n) (truncatedRiemannAutocorr_nonneg L (c - Real.log n))
      by_cases hn : n ∈ F
      · rw [show head n = v n * riemannAutocorr (Real.log n) by simp only [head, if_pos hn]]
        have h := mul_le_mul_of_nonneg_left
          (truncatedRiemannAutocorr_le_riemannAutocorr L (Real.log n)) (hv n)
        nlinarith only [h, hplus, hminus]
      · rw [show head n = 0 by simp only [head, if_neg hn], mul_zero, add_zero]
        have hnN : ⌊Real.exp Y⌋₊ + 1 ≤ n := by
          simpa only [F, Finset.mem_range, not_lt] using hn
        have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        have hnR : (⌊Real.exp Y⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast hnN
        have hlog : Y ≤ Real.log n := ((Real.lt_log_iff_exp_lt hnpos).mpr
          ((Nat.lt_floor_add_one _).trans_le hnR)).le
        have h := mul_le_mul_of_nonneg_left (hY (Real.log n) hlog L) (hv n)
        rw [show Real.log n - c = -(c - Real.log n) by ring,
          truncatedRiemannAutocorr_neg] at h
        nlinarith only [h, hplus]
    have h := ((hD L).mul_left 4).tsum_le_tsum hpoint ((hT L c).add (hshead.mul_left 4))
    simpa only [(hT L c).tsum_add (hshead.mul_left 4), tsum_mul_left] using h
  exact ⟨H, hbound⟩

/-- If a minorant has divergent origin deficit moment, every fixed integer-log
shift of size at least four has probe values tending to minus infinity. -/
theorem tendsto_logShift_probe_atBot_of_minorant_nonsummable_origin {lam : ℕ → ℝ}
    (hminor : ∀ n : ℕ, 2 ≤ n → lam n ≤ ArithmeticFunction.vonMangoldt n)
    (hbad : ¬ Summable fun n => -weilDeviation lam n * riemannAutocorr (Real.log n))
    {m : ℕ} (hm : 4 ≤ Real.log m) :
    Tendsto (fun L : ℝ => (weilFullFunctional lam (EF.weilTest
      (logShiftRiemannDifference L (Real.log m))
      (logShiftRiemannDifference L (Real.log m)))).re) atTop atBot := by
  let v : ℕ → ℝ := fun n => -weilDeviation lam n
  have hv : ∀ n, 0 ≤ v n := by
    intro n
    dsimp only [v, weilDeviation]
    split_ifs with hn
    · exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (hminor n hn)) (Real.sqrt_nonneg _))
    · simp only [neg_zero, le_refl]
  let D := fun L : ℝ => ∑' n, v n * truncatedRiemannAutocorr L (Real.log n)
  let T := fun L y : ℝ => ∑' n, v n *
    (truncatedRiemannAutocorr L (y + Real.log n) +
      truncatedRiemannAutocorr L (y - Real.log n))
  obtain ⟨H, hbound⟩ := exists_truncated_origin_gain_bound v hv hm
  have hneg (L y : ℝ) : truncatedDeviationPotential lam L y = -T L y := by
    dsimp only [truncatedDeviationPotential, T]
    rw [← tsum_neg]
    apply tsum_congr
    intro n
    dsimp only [v]
    ring
  have hT0 (L : ℝ) : T L 0 = 2 * D L := by
    dsimp only [T, D]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [zero_add, zero_sub, truncatedRiemannAutocorr_neg]
    ring
  have hupper (L : ℝ) :
      (weilFullFunctional lam (EF.weilTest (logShiftRiemannDifference L (Real.log m))
        (logShiftRiemannDifference L (Real.log m)))).re ≤
      (zetaZeroConfig.W (logShiftRiemannDifference L (Real.log m))
        (logShiftRiemannDifference L (Real.log m))).re - 4 * D L + 8 * H := by
    rw [logShift_probe_potential_identity, hneg L (Real.log m), hneg L 0, hT0 L]
    linarith only [hbound L]
  have hdiv : Tendsto D atTop atTop := tendsto_truncated_origin_atTop_of_not_summable hv hbad
  have hzero := (tendsto_order.mp (tendsto_logShift_zeroSide m)).2 1 (by norm_num)
  refine tendsto_atBot.mpr fun b => ?_
  filter_upwards [hzero, hdiv.eventually_ge_atTop ((1 + 8 * H - b) / 4)] with L hW hL
  have hu := hupper L
  linarith only [hu, hW, hL]

/-- Every strict minorant has a persistent fixed negative probe, without any
coefficient-growth, nonnegativity, or moment-summability assumption. -/
theorem exists_fixed_logShift_separation_of_strict_minorant {lam : ℕ → ℝ}
    (hminor : ∀ n : ℕ, 2 ≤ n → lam n ≤ ArithmeticFunction.vonMangoldt n)
    (hstrict : ∃ q : ℕ, 2 ≤ q ∧ lam q < ArithmeticFunction.vonMangoldt q) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      (m : ℝ) ≤ Real.exp (2 * (k : ℝ)) ∧
        (weilFullFunctional lam (EF.weilTest
          (logShiftRiemannDifference k (Real.log m))
          (logShiftRiemannDifference k (Real.log m)))).re ≤ -η := by
  by_cases hs : Summable fun n => -weilDeviation lam n * riemannAutocorr (Real.log n)
  · exact exists_fixed_logShift_minorant_separation_of_summable_origin hminor hs hstrict
  let m : ℕ := ⌊Real.exp (4 : ℝ)⌋₊ + 1
  have hm : 2 ≤ m := (integer_log_probe_bounds 4).1
  have hmc : 4 ≤ Real.log m := (integer_log_probe_bounds 4).2.1
  have hlim := tendsto_logShift_probe_atBot_of_minorant_nonsummable_origin hminor hs hmc
  have hev := (hlim.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_le_atBot (-1)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨m, hm, 1, by norm_num, max N ⌈Real.log m / 2⌉₊, ?_⟩
  intro k hk
  constructor
  · have hlog : Real.log m / 2 ≤ (k : ℝ) := (Nat.le_ceil _).trans
      (by exact_mod_cast (show ⌈Real.log m / 2⌉₊ ≤ k from (le_max_right _ _).trans hk))
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    exact (Real.log_le_iff_le_exp hmpos).mp (by linarith only [hlog])
  · exact hN k ((le_max_left _ _).trans hk)

end RHTower
