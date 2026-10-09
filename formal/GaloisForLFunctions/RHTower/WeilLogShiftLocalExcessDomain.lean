import GaloisForLFunctions.RHTower.WeilLogShiftSingleProbeDomain

/-!
# Local excess moments and the exact probe domain

Global unweighted finite excess can be replaced by the positive-excess moment
at the individual probe. Together with one eventual lower bound, that local
moment characterizes signed potential summability. Cofinal probes similarly
compare subexponential growth of the full deviation and its positive part.
-/

open Filter Topology Zeta23 Real

noncomputable section

namespace RHTower

open WeilExcess

/-- Signed-potential convergence always controls the positive part at the same
shift, without any global coefficient assumption. -/
theorem summable_excess_potential_of_summable_potential {lam : ℕ → ℝ} {y : ℝ}
    (hs : Summable fun n => weilDeviation lam n *
      (riemannAutocorr (y + log n) + riemannAutocorr (y - log n))) :
    Summable fun n => deviationExcess lam n *
      (riemannAutocorr (y + log n) + riemannAutocorr (y - log n)) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (deviationExcess_nonneg _ _)
      (add_nonneg (riemannAutocorr_nonneg _) (riemannAutocorr_nonneg _))) _ hs.norm
  intro n
  simp only [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (add_nonneg (riemannAutocorr_nonneg (y + log n))
      (riemannAutocorr_nonneg (y - log n)))]
  exact mul_le_mul_of_nonneg_right
    (max_le (le_abs_self (weilDeviation lam n)) (abs_nonneg _))
    (add_nonneg (riemannAutocorr_nonneg _) (riemannAutocorr_nonneg _))

/-- Only the positive-excess moment at this shift is needed for the signed and
deficit convergence domains to agree. -/
theorem summable_potential_iff_deficit_of_local_excess {lam : ℕ → ℝ} {y : ℝ}
    (hexc : Summable fun n => deviationExcess lam n *
      (riemannAutocorr (y + log n) + riemannAutocorr (y - log n))) :
    (Summable fun n => weilDeviation lam n *
      (riemannAutocorr (y + log n) + riemannAutocorr (y - log n))) ↔
    Summable fun n => deviationDeficit lam n *
      (riemannAutocorr (y + log n) + riemannAutocorr (y - log n)) := by
  constructor <;> intro hs
  · refine (hexc.sub hs).congr fun n => ?_
    rw [weilDeviation_eq_sub]
    ring
  · refine (hexc.sub hs).congr fun n => ?_
    rw [weilDeviation_eq_sub]
    ring

/-- The positive contribution to a probe is bounded by its own full excess
moment. Unweighted excess and its origin moment are not required. -/
theorem logShift_probe_le_local_excess_deficit {lam : ℕ → ℝ} {c : ℝ}
    (hexc : Summable fun n => deviationExcess lam n *
      (riemannAutocorr (c + log n) + riemannAutocorr (c - log n))) (L : ℝ) :
    (weilFullFunctional lam (EF.weilTest (logShiftRiemannDifference L c)
      (logShiftRiemannDifference L c))).re ≤
      (zetaZeroConfig.W (logShiftRiemannDifference L c)
        (logShiftRiemannDifference L c)).re +
      2 * kernelPotential (deviationExcess lam) c +
      4 * (∑' n, deviationDeficit lam n * truncatedRiemannAutocorr L (log n)) -
      2 * (∑' n, deviationDeficit lam n *
        (truncatedRiemannAutocorr L (c + log n) +
          truncatedRiemannAutocorr L (c - log n))) := by
  let T := fun (w : ℕ → ℝ) (y : ℝ) => ∑' n, w n *
    (truncatedRiemannAutocorr L (y + log n) + truncatedRiemannAutocorr L (y - log n))
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
  have hEc : T (deviationExcess lam) c ≤ kernelPotential (deviationExcess lam) c := by
    apply (hT (deviationExcess lam) c).tsum_le_tsum _ hexc
    intro n
    exact mul_le_mul_of_nonneg_left
      (add_le_add (truncatedRiemannAutocorr_le_riemannAutocorr _ _)
        (truncatedRiemannAutocorr_le_riemannAutocorr _ _)) (deviationExcess_nonneg _ _)
  have hD0 : T (deviationDeficit lam) 0 =
      2 * (∑' n, deviationDeficit lam n * truncatedRiemannAutocorr L (log n)) := by
    dsimp only [T]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [zero_add, zero_sub, truncatedRiemannAutocorr_neg]
    ring
  rw [logShift_probe_potential_identity, hsplit c, hsplit 0, hD0]
  change _ ≤ _ + _ + _ - 2 * T (deviationDeficit lam) c
  linarith only [hE0, hEc]

/-- A finite local excess moment leaves only one nonsummable alternative:
the nontrivial integer-log probe tends to minus infinity. -/
theorem tendsto_logShift_probe_atBot_of_nonsummable_sample_of_local_excess
    {lam : ℕ → ℝ} {m : ℕ} (hm : 2 ≤ m)
    (hexc : Summable fun n => deviationExcess lam n *
      (riemannAutocorr (log m + log n) + riemannAutocorr (log m - log n)))
    (hbad : ¬ Summable fun n => weilDeviation lam n *
      (riemannAutocorr (log m + log n) + riemannAutocorr (log m - log n))) :
    Tendsto (fun L : ℝ => (weilFullFunctional lam (EF.weilTest
      (logShiftRiemannDifference L (log m))
      (logShiftRiemannDifference L (log m)))).re) atTop atBot := by
  have hdef : ¬ Summable fun n => deviationDeficit lam n *
      (riemannAutocorr (log m + log n) + riemannAutocorr (log m - log n)) :=
    fun hs => hbad ((summable_potential_iff_deficit_of_local_excess hexc).mpr hs)
  have hzero := (tendsto_order.mp (tendsto_logShift_zeroSide m)).2 1 (by norm_num)
  by_cases horigin : Summable fun n => deviationDeficit lam n * riemannAutocorr (log n)
  · let D := ∑' n, deviationDeficit lam n * riemannAutocorr (log n)
    let C := 2 * kernelPotential (deviationExcess lam) (log m) + 4 * D
    have hD (L : ℝ) :
        (∑' n, deviationDeficit lam n * truncatedRiemannAutocorr L (log n)) ≤ D :=
      (summable_truncated_origin_term (deviationDeficit lam) L).tsum_le_tsum
        (fun n => mul_le_mul_of_nonneg_left
          (truncatedRiemannAutocorr_le_riemannAutocorr _ _) (deviationDeficit_nonneg _ _)) horigin
    have hdiv := tendsto_truncated_kernelPotential_atTop_of_not_summable
      (deviationDeficit_nonneg lam) (log m) hdef
    refine tendsto_atBot.mpr fun b => ?_
    filter_upwards [hzero, hdiv.eventually_ge_atTop ((1 + C - b) / 2)] with L hW hL
    have hu := logShift_probe_le_local_excess_deficit hexc L
    have hd := hD L
    dsimp only [C] at hL
    linarith only [hu, hd, hW, hL]
  · have hlog : 0 < log (m : ℝ) := log_pos (by exact_mod_cast (show 1 < m by omega))
    obtain ⟨H, hH⟩ := exists_truncated_origin_gain_bound_of_pos (deviationDeficit lam)
      (deviationDeficit_nonneg lam) hlog
    let C := 2 * kernelPotential (deviationExcess lam) (log m) + 8 * H
    have hdiv := tendsto_truncated_origin_atTop_of_not_summable
      (deviationDeficit_nonneg lam) horigin
    refine tendsto_atBot.mpr fun b => ?_
    filter_upwards [hzero, hdiv.eventually_ge_atTop ((1 + C - b) / 4)] with L hW hL
    have hu := logShift_probe_le_local_excess_deficit hexc L
    have hh := hH L
    dsimp only [C] at hL
    linarith only [hu, hh, hW, hL]

private theorem probe_lower_bound_of_tendsto {f : ℝ → ℝ} {d : ℝ}
    (ht : Tendsto f atTop (𝓝 d)) :
    ∃ b : ℝ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k → b ≤ f k := by
  have hev := (tendsto_order.mp (ht.comp (tendsto_natCast_atTop_atTop (R := ℝ)))).1
    (d - 1) (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  exact ⟨d - 1, N, fun k hk => (hN k hk).le⟩

/-- Exact local domain criterion with no global coefficient assumption:
local excess summability and one eventual lower bound are jointly equivalent
to signed-potential summability. -/
theorem summable_potential_iff_local_excess_and_probe_lower_bound
    {lam : ℕ → ℝ} {m : ℕ} (hm : 2 ≤ m) :
    (Summable fun n => weilDeviation lam n *
      (riemannAutocorr (log m + log n) + riemannAutocorr (log m - log n))) ↔
    (Summable fun n => deviationExcess lam n *
      (riemannAutocorr (log m + log n) + riemannAutocorr (log m - log n))) ∧
    ∃ b : ℝ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      b ≤ (weilFullFunctional lam (EF.weilTest
        (logShiftRiemannDifference k (log m))
        (logShiftRiemannDifference k (log m)))).re := by
  constructor
  · intro hs
    exact ⟨summable_excess_potential_of_summable_potential hs,
      probe_lower_bound_of_tendsto (tendsto_logShift_probe_of_summable_sample hm hs)⟩
  · rintro ⟨hexc, b, N, hN⟩
    by_contra hbad
    have ht := tendsto_logShift_probe_atBot_of_nonsummable_sample_of_local_excess hm hexc hbad
    have hev := (ht.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_le_atBot (b - 1)
    obtain ⟨M, hM⟩ := eventually_atTop.mp hev
    have hlo := hN (max N M) (le_max_left _ _)
    have hhi := hM (max N M) (le_max_right _ _)
    change (weilFullFunctional lam (EF.weilTest
      (logShiftRiemannDifference (max N M : ℕ) (log m))
      (logShiftRiemannDifference (max N M : ℕ) (log m)))).re ≤ b - 1 at hhi
    linarith only [hlo, hhi]

/-- Local excess control and a lower-bounded probe give every coefficient
growth bound above the inverse-location rate, without unweighted finite excess. -/
theorem exponential_bound_of_local_excess_probe_lower_bound
    {lam : ℕ → ℝ} {m : ℕ} (hm : 2 ≤ m)
    (hexc : Summable fun n => deviationExcess lam n *
      (riemannAutocorr (log m + log n) + riemannAutocorr (log m - log n)))
    (hbounded : ∃ d : ℝ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      d ≤ (weilFullFunctional lam (EF.weilTest
        (logShiftRiemannDifference k (log m))
        (logShiftRiemannDifference k (log m)))).re)
    {b : ℝ} (hb : 2 * π / m < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |weilDeviation lam n| ≤ C * exp (b * n) := by
  have hs := (summable_potential_iff_local_excess_and_probe_lower_bound hm).mpr ⟨hexc, hbounded⟩
  apply exponential_bound_of_summable_kernelPotential (y := log m) _ hs
  rwa [logKernelCriticalRate_log_nat (show 1 ≤ m by omega)]

/-- On any cofinal family of integer-log probes, whole-line excess convergence
and individual probe lower bounds exactly characterize whole-line signed
convergence. Probe indices need not be monotone or all nontrivial. -/
theorem summable_potential_iff_cofinal_local_excess_and_probe_lower_bounds
    {lam : ℕ → ℝ} (m : ℕ → ℕ) (hcofinal : ∀ R : ℝ, ∃ j : ℕ, R ≤ log (m j)) :
    (∀ y : ℝ, Summable fun n => weilDeviation lam n *
      (riemannAutocorr (y + log n) + riemannAutocorr (y - log n))) ↔
    (∀ y : ℝ, Summable fun n => deviationExcess lam n *
      (riemannAutocorr (y + log n) + riemannAutocorr (y - log n))) ∧
    ∀ j : ℕ, ∃ b : ℝ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      b ≤ (weilFullFunctional lam (EF.weilTest
        (logShiftRiemannDifference k (log (m j)))
        (logShiftRiemannDifference k (log (m j))))).re := by
  constructor
  · intro hs
    refine ⟨fun y => summable_excess_potential_of_summable_potential (hs y), fun j => ?_⟩
    exact probe_lower_bound_of_tendsto
      (tendsto_logShift_probe_of_summable_potential (m j) (hs 0) (hs (log (m j))))
  · rintro ⟨hexc, hbounded⟩ y
    obtain ⟨j, hj⟩ := hcofinal (|y| + 1)
    have hlog : 0 < log (m j : ℝ) := by linarith only [hj, abs_nonneg y]
    have hm : 2 ≤ m j := by
      by_contra h
      have hz : m j = 0 ∨ m j = 1 := by omega
      rcases hz with hz | hz <;> rw [hz] at hlog <;> norm_num at hlog
    have hs := (summable_potential_iff_local_excess_and_probe_lower_bound hm).mpr
      ⟨hexc (log (m j)), hbounded j⟩
    apply summable_kernelPotential_of_abs_lt (c := log (m j)) _ hs
    rw [abs_of_pos hlog]
    linarith only [hj]

/-- Subexponential positive excess replaces summable excess in the cofinal
probe characterization of subexponential full normalized deviation. -/
theorem subexponential_deviation_iff_excess_growth_and_cofinal_probe_lower_bounds
    {lam : ℕ → ℝ} (m : ℕ → ℕ) (hcofinal : ∀ R : ℝ, ∃ j : ℕ, R ≤ log (m j)) :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      |weilDeviation lam n| ≤ C * exp (ε * n)) ↔
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      |deviationExcess lam n| ≤ C * exp (ε * n)) ∧
    ∀ j : ℕ, ∃ b : ℝ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      b ≤ (weilFullFunctional lam (EF.weilTest
        (logShiftRiemannDifference k (log (m j)))
        (logShiftRiemannDifference k (log (m j))))).re := by
  rw [← summable_kernelPotential_iff_subexponential (weilDeviation lam),
    ← summable_kernelPotential_iff_subexponential (deviationExcess lam)]
  exact summable_potential_iff_cofinal_local_excess_and_probe_lower_bounds m hcofinal

/-- The local-moment domain strictly exceeds unweighted finite excess:
`Λ(n)+sqrt(n)` has unit positive deviation for every `n ≥ 2`, yet all real-shift
potentials converge. -/
theorem exists_nonsummable_excess_with_summable_potentials :
    ∃ lam : ℕ → ℝ, ¬ Summable (deviationExcess lam) ∧
      ∀ y : ℝ, Summable fun n => weilDeviation lam n *
        (riemannAutocorr (y + log n) + riemannAutocorr (y - log n)) := by
  let lam (n : ℕ) : ℝ := (ArithmeticFunction.vonMangoldt n : ℝ) + sqrt n
  have hdev (n : ℕ) : weilDeviation lam n = if 2 ≤ n then 1 else 0 := by
    by_cases hn : 2 ≤ n
    · have hsqrt : sqrt (n : ℝ) ≠ 0 :=
        (sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))).ne'
      simp only [weilDeviation, if_pos hn]
      rw [show lam n - (ArithmeticFunction.vonMangoldt n : ℝ) = sqrt n by
        dsimp only [lam]; ring, div_self hsqrt]
    · simp only [weilDeviation, if_neg hn]
  have hexc (n : ℕ) : deviationExcess lam n = if 2 ≤ n then 1 else 0 := by
    rw [deviationExcess, hdev]
    split_ifs <;> norm_num
  refine ⟨lam, ?_, fun y => ?_⟩
  · intro hs
    have ht : Summable (fun _ : ℕ => (1 : ℝ)) :=
      ((summable_nat_add_iff 2).mpr hs).congr (fun n => by
        rw [hexc, if_pos (show 2 ≤ n + 2 by omega)])
    have hzero := (summable_const_iff (1 : ℝ)).mp ht
    norm_num at hzero
  · apply summable_kernelPotential_of_exponential_growth (ρ := 0) (C := 1)
      (logKernelCriticalRate_pos y)
    intro n
    rw [hdev]
    split_ifs <;> norm_num

end RHTower
