import GaloisForLFunctions.RHTower.WeilLogShiftPositiveTailGain
import GaloisForLFunctions.RHTower.WeilLogShiftLocalDecayThreshold

/-!
# Exact convergence domain of every nontrivial integer-log probe

Every positive shift detects divergent origin deficit mass. With finite excess,
each probe at `log m`, `m ≥ 2`, therefore has an exact alternative: a finite
potential limit when its sampled potential is summable, or divergence to minus
infinity otherwise. One eventual lower bound characterizes this local domain.
-/

open Filter Topology Zeta23 Real

noncomputable section

namespace RHTower

open WeilExcess

/-- Every positive shift controls four times the truncated origin mass, up to
a finite head bound independent of the cutoff. -/
theorem exists_truncated_origin_gain_bound_of_pos (v : ℕ → ℝ) (hv : ∀ n, 0 ≤ v n)
    {c : ℝ} (hc : 0 < c) :
    ∃ H : ℝ, ∀ L : ℝ,
      4 * (∑' n, v n * truncatedRiemannAutocorr L (log n)) ≤
        (∑' n, v n * (truncatedRiemannAutocorr L (c + log n) +
          truncatedRiemannAutocorr L (c - log n))) + 4 * H := by
  obtain ⟨Y, hY⟩ := exists_truncatedRiemannAutocorr_tail_shift_gain_of_pos hc 4
  let F := Finset.range (⌊exp Y⌋₊ + 1)
  let head : ℕ → ℝ := fun n => if n ∈ F then v n * riemannAutocorr (log n) else 0
  have hshead : Summable head := summable_of_ne_finset_zero (s := F)
    (fun n hn => by simp only [head, if_neg hn])
  let H := ∑' n, head n
  let D := fun L : ℝ => ∑' n, v n * truncatedRiemannAutocorr L (log n)
  let T := fun L y : ℝ => ∑' n, v n *
    (truncatedRiemannAutocorr L (y + log n) + truncatedRiemannAutocorr L (y - log n))
  have hD (L : ℝ) := summable_truncated_origin_term v L
  have hT (L y : ℝ) := summable_truncated_potential_term v L y
  refine ⟨H, fun L => ?_⟩
  have hpoint (n : ℕ) :
      4 * (v n * truncatedRiemannAutocorr L (log n)) ≤
        v n * (truncatedRiemannAutocorr L (c + log n) +
          truncatedRiemannAutocorr L (c - log n)) + 4 * head n := by
    have hplus := mul_nonneg (hv n) (truncatedRiemannAutocorr_nonneg L (c + log n))
    have hminus := mul_nonneg (hv n) (truncatedRiemannAutocorr_nonneg L (c - log n))
    by_cases hn : n ∈ F
    · rw [show head n = v n * riemannAutocorr (log n) by simp only [head, if_pos hn]]
      have h := mul_le_mul_of_nonneg_left
        (truncatedRiemannAutocorr_le_riemannAutocorr L (log n)) (hv n)
      nlinarith only [h, hplus, hminus]
    · rw [show head n = 0 by simp only [head, if_neg hn], mul_zero, add_zero]
      have hnN : ⌊exp Y⌋₊ + 1 ≤ n := by
        simpa only [F, Finset.mem_range, not_lt] using hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hnR : (⌊exp Y⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast hnN
      have hlog : Y ≤ log n := ((lt_log_iff_exp_lt hnpos).mpr
        ((Nat.lt_floor_add_one _).trans_le hnR)).le
      have h := mul_le_mul_of_nonneg_left (hY (log n) hlog L) (hv n)
      rw [show log n - c = -(c - log n) by ring, truncatedRiemannAutocorr_neg] at h
      nlinarith only [h, hplus]
  have h := ((hD L).mul_left 4).tsum_le_tsum hpoint ((hT L c).add (hshead.mul_left 4))
  simpa only [(hT L c).tsum_add (hshead.mul_left 4), tsum_mul_left] using h

/-- Divergent origin deficit mass sends every nontrivial integer-log probe to
minus infinity, assuming only finite excess. -/
theorem tendsto_logShift_probe_atBot_of_nonsummable_deficit_origin_of_two_le
    {lam : ℕ → ℝ} (hexc : Summable (deviationExcess lam))
    (hbad : ¬ Summable fun n => deviationDeficit lam n * riemannAutocorr (log n))
    {m : ℕ} (hm : 2 ≤ m) :
    Tendsto (fun L : ℝ => (weilFullFunctional lam (EF.weilTest
      (logShiftRiemannDifference L (log m))
      (logShiftRiemannDifference L (log m)))).re) atTop atBot := by
  have hlog : 0 < log (m : ℝ) := log_pos (by exact_mod_cast (show 1 < m by omega))
  obtain ⟨H, hH⟩ := exists_truncated_origin_gain_bound_of_pos (deviationDeficit lam)
    (deviationDeficit_nonneg lam) hlog
  let C := 4 * riemannAutocorr 0 * (∑' n, deviationExcess lam n) + 8 * H
  have hdiv := tendsto_truncated_origin_atTop_of_not_summable (deviationDeficit_nonneg lam) hbad
  have hzero := (tendsto_order.mp (tendsto_logShift_zeroSide m)).2 1 (by norm_num)
  refine tendsto_atBot.mpr fun b => ?_
  filter_upwards [hzero, hdiv.eventually_ge_atTop ((1 + C - b) / 4)] with L hW hL
  have hu := logShift_probe_le_excess_deficit hexc L (log m)
  have hh := hH L
  dsimp only [C] at hL
  linarith only [hu, hh, hW, hL]

/-- A lower bound on any single nontrivial integer-log probe already forces
origin deficit summability in the finite-excess class. -/
theorem summable_deficit_origin_of_probe_bounded_below_of_two_le {lam : ℕ → ℝ}
    (hexc : Summable (deviationExcess lam)) {m : ℕ} (hm : 2 ≤ m)
    (hbounded : ∃ b : ℝ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      b ≤ (weilFullFunctional lam (EF.weilTest
        (logShiftRiemannDifference k (log m))
        (logShiftRiemannDifference k (log m)))).re) :
    Summable fun n => deviationDeficit lam n * riemannAutocorr (log n) := by
  by_contra hbad
  obtain ⟨b, N, hN⟩ := hbounded
  have ht := tendsto_logShift_probe_atBot_of_nonsummable_deficit_origin_of_two_le hexc hbad hm
  have hev := (ht.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_le_atBot (b - 1)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hev
  have hlo := hN (max N M) (le_max_left _ _)
  have hhi := hM (max N M) (le_max_right _ _)
  change (weilFullFunctional lam (EF.weilTest
    (logShiftRiemannDifference (max N M : ℕ) (log m))
    (logShiftRiemannDifference (max N M : ℕ) (log m)))).re ≤ b - 1 at hhi
  linarith only [hlo, hhi]

/-- Convergence transfers strictly inward for arbitrary signed weights.
There is no minimum separation between the two shifts. -/
theorem summable_kernelPotential_of_abs_lt {v : ℕ → ℝ} {y c : ℝ}
    (hyc : |y| < |c|)
    (hs : Summable fun n => v n *
      (riemannAutocorr (c + log n) + riemannAutocorr (c - log n))) :
    Summable fun n => v n *
      (riemannAutocorr (y + log n) + riemannAutocorr (y - log n)) := by
  have hr : logKernelCriticalRate c < logKernelCriticalRate y :=
    mul_lt_mul_of_pos_left (exp_lt_exp.mpr (neg_lt_neg hyc)) (by positivity)
  let b := (logKernelCriticalRate c + logKernelCriticalRate y) / 2
  have hcb : logKernelCriticalRate c < b := by dsimp only [b]; linarith only [hr]
  have hby : b < logKernelCriticalRate y := by dsimp only [b]; linarith only [hr]
  obtain ⟨C, _, hC⟩ := exponential_bound_of_summable_kernelPotential hcb hs
  exact summable_kernelPotential_of_exponential_growth hby hC

/-- Convergence at one nontrivial integer sample already gives its exact
finite probe limit, without an excess assumption or a separate origin premise. -/
theorem tendsto_logShift_probe_of_summable_sample {lam : ℕ → ℝ} {m : ℕ} (hm : 2 ≤ m)
    (hs : Summable fun n => weilDeviation lam n *
      (riemannAutocorr (log m + log n) + riemannAutocorr (log m - log n))) :
    Tendsto (fun L : ℝ => (weilFullFunctional lam (EF.weilTest
      (logShiftRiemannDifference L (log m))
      (logShiftRiemannDifference L (log m)))).re) atTop
        (𝓝 (2 * (deviationPotential lam (log m) - deviationPotential lam 0))) := by
  have hlog : 0 < log (m : ℝ) := log_pos (by exact_mod_cast (show 1 < m by omega))
  have horigin := summable_kernelPotential_of_abs_lt (y := 0)
    (by simpa only [abs_zero, abs_of_pos hlog] using hlog) hs
  exact tendsto_logShift_probe_of_summable_potential m horigin hs

/-- In the finite-excess class, one eventual lower bound is exactly the
convergence domain of that individual nontrivial integer-log probe. -/
theorem summable_potential_iff_logShift_probe_bounded_below {lam : ℕ → ℝ}
    (hexc : Summable (deviationExcess lam)) {m : ℕ} (hm : 2 ≤ m) :
    (Summable fun n => weilDeviation lam n *
      (riemannAutocorr (log m + log n) + riemannAutocorr (log m - log n))) ↔
    ∃ b : ℝ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      b ≤ (weilFullFunctional lam (EF.weilTest
        (logShiftRiemannDifference k (log m))
        (logShiftRiemannDifference k (log m)))).re := by
  constructor
  · intro hs
    have ht := (tendsto_logShift_probe_of_summable_sample hm hs).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    let b := 2 * (deviationPotential lam (log m) - deviationPotential lam 0) - 1
    have hev := (tendsto_order.mp ht).1 b (by dsimp only [b]; linarith)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    exact ⟨b, N, fun k hk => (hN k hk).le⟩
  · intro hbounded
    have horigin := summable_deficit_origin_of_probe_bounded_below_of_two_le hexc hm hbounded
    exact summable_potential_of_probe_bounded_below hexc horigin m hbounded

/-- Outside that local domain, the probe tends to minus infinity; oscillation
or positive divergence cannot occur under finite excess. -/
theorem tendsto_logShift_probe_atBot_of_nonsummable_sample {lam : ℕ → ℝ}
    (hexc : Summable (deviationExcess lam)) {m : ℕ} (hm : 2 ≤ m)
    (hbad : ¬ Summable fun n => weilDeviation lam n *
      (riemannAutocorr (log m + log n) + riemannAutocorr (log m - log n))) :
    Tendsto (fun L : ℝ => (weilFullFunctional lam (EF.weilTest
      (logShiftRiemannDifference L (log m))
      (logShiftRiemannDifference L (log m)))).re) atTop atBot := by
  by_cases horigin : Summable fun n => deviationDeficit lam n * riemannAutocorr (log n)
  · apply tendsto_logShift_probe_atBot_of_nonsummable_deficit_sample hexc horigin m
    intro hd
    exact hbad ((summable_potential_iff_summable_deficit hexc (log m)).mpr hd)
  · exact tendsto_logShift_probe_atBot_of_nonsummable_deficit_origin_of_two_le hexc horigin hm

/-- Every lower-bounded nontrivial integer probe bounds coefficient growth at
all rates above its inverse-location threshold `2π/m`. -/
theorem exponential_bound_of_logShift_probe_lower_bound_of_two_le {lam : ℕ → ℝ}
    (hexc : Summable (deviationExcess lam)) {m : ℕ} (hm : 2 ≤ m)
    (hbounded : ∃ d : ℝ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      d ≤ (weilFullFunctional lam (EF.weilTest
        (logShiftRiemannDifference k (log m))
        (logShiftRiemannDifference k (log m)))).re)
    {b : ℝ} (hb : 2 * π / m < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |weilDeviation lam n| ≤ C * exp (b * n) := by
  have hs := (summable_potential_iff_logShift_probe_bounded_below hexc hm).mpr hbounded
  apply exponential_bound_of_summable_kernelPotential (y := log m) _ hs
  rwa [logKernelCriticalRate_log_nat (show 1 ≤ m by omega)]

end RHTower
