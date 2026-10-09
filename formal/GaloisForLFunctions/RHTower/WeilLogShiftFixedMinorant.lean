import GaloisForLFunctions.RHTower.WeilLogShiftNonnegativePotential

/-!
# Fixed minorant separation from the origin moment

The subcritical integer-log kernel budget selects a fixed deficit atom. A finite
origin deficit moment then gives a persistent negative probe, without convergence
at the selected shift. Nonnegative strict minorants need no summability premise.
-/

open Filter Topology Zeta23

noncomputable section

namespace RHTower

open WeilExcess

private theorem tsum_le_logKernel_budget {b : ℕ → ℝ} {C : ℝ}
    (hb : ∀ n, 0 ≤ b n) (hsmall : ∀ n, n < 2 → b n = 0) (hC : 0 ≤ C)
    (hbound : ∀ n, 2 ≤ n → b n ≤ C * riemannAutocorr (Real.log n)) :
    ∑' n, b n ≤ C * (23 / 50 * riemannAutocorr 0) := by
  apply Real.tsum_le_of_sum_range_le hb
  intro N
  let F := (Finset.range N).filter (fun n => 2 ≤ n)
  have hsum : ∑ n ∈ Finset.range N, b n = ∑ n ∈ F, b n := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnot
    have hn2 : ¬ 2 ≤ n := fun h => hnot (Finset.mem_filter.mpr ⟨hn, h⟩)
    exact hsmall n (by omega)
  have hsub : F ⊆ Finset.Icc 2 N := by
    intro n hn
    obtain ⟨hnN, hn2⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_Icc.mpr ⟨hn2, (Finset.mem_range.mp hnN).le⟩
  calc ∑ n ∈ Finset.range N, b n = ∑ n ∈ F, b n := hsum
    _ ≤ ∑ n ∈ F, C * riemannAutocorr (Real.log n) :=
      Finset.sum_le_sum (fun n hn => hbound n (Finset.mem_filter.mp hn).2)
    _ = C * ∑ n ∈ F, riemannAutocorr (Real.log n) := by rw [Finset.mul_sum]
    _ ≤ C * ∑ n ∈ Finset.Icc 2 N, riemannAutocorr (Real.log n) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => riemannAutocorr_nonneg _)) hC
    _ ≤ C * (23 / 50 * riemannAutocorr 0) :=
      mul_le_mul_of_nonneg_left (sum_riemannAutocorr_log_le N) hC

/-- The kernel-sum budget selects an atom exceeding twice the origin moment.
Even this atom-selection statement needs no summability hypothesis. -/
theorem exists_deficit_exceeds_twice_origin_moment {v : ℕ → ℝ}
    (hv : ∀ n, 0 ≤ v n) (hsmall : ∀ n, n < 2 → v n = 0)
    (hstrict : ∃ q : ℕ, 0 < v q) :
    ∃ m : ℕ, 2 ≤ m ∧
      2 * (∑' n, v n * riemannAutocorr (Real.log n)) < v m * riemannAutocorr 0 := by
  by_contra hnot
  push Not at hnot
  let D := ∑' n, v n * riemannAutocorr (Real.log n)
  have hD : 0 ≤ D := tsum_nonneg (fun n => mul_nonneg (hv n) (riemannAutocorr_nonneg _))
  obtain ⟨q, hq⟩ := hstrict
  have hq2 : 2 ≤ q := by
    by_contra h
    have hz := hsmall q (by omega)
    linarith only [hq, hz]
  have hDpos : 0 < D := by
    have h := hnot q hq2
    have hqK := mul_pos hq riemannAutocorr_zero_pos
    change v q * riemannAutocorr 0 ≤ 2 * D at h
    linarith only [h, hqK]
  have hbudget := tsum_le_logKernel_budget
    (b := fun n => (v n * riemannAutocorr 0) * riemannAutocorr (Real.log n))
    (C := 2 * D)
    (fun n => mul_nonneg (mul_nonneg (hv n) riemannAutocorr_zero_pos.le)
      (riemannAutocorr_nonneg _))
    (fun n hn => by rw [hsmall n hn, zero_mul, zero_mul])
    (by positivity)
    (fun n hn => mul_le_mul_of_nonneg_right (hnot n hn) (riemannAutocorr_nonneg _))
  have heq : (∑' n, (v n * riemannAutocorr 0) * riemannAutocorr (Real.log n)) =
      D * riemannAutocorr 0 := by
    rw [show D * riemannAutocorr 0 =
      ∑' n, (v n * riemannAutocorr (Real.log n)) * riemannAutocorr 0 from tsum_mul_right.symm]
    apply tsum_congr
    intro n
    ring
  rw [heq] at hbudget
  have hDK := mul_pos hDpos riemannAutocorr_zero_pos
  nlinarith only [hbudget, hDK]

/-- A strict minorant with finite origin deficit moment has one fixed negative
probe in every sufficiently late panel. No convergence at that probe is assumed. -/
theorem exists_fixed_logShift_minorant_separation_of_summable_origin {lam : ℕ → ℝ}
    (hminor : ∀ n : ℕ, 2 ≤ n → lam n ≤ ArithmeticFunction.vonMangoldt n)
    (hmoment : Summable fun n => -weilDeviation lam n * riemannAutocorr (Real.log n))
    (hstrict : ∃ q : ℕ, 2 ≤ q ∧ lam q < ArithmeticFunction.vonMangoldt q) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      (m : ℝ) ≤ Real.exp (2 * (k : ℝ)) ∧
        (weilFullFunctional lam (EF.weilTest
          (logShiftRiemannDifference k (Real.log m))
          (logShiftRiemannDifference k (Real.log m)))).re ≤ -η := by
  let v : ℕ → ℝ := fun n => -weilDeviation lam n
  have hv : ∀ n, 0 ≤ v n := by
    intro n
    dsimp only [v, weilDeviation]
    split_ifs with hn
    · exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (hminor n hn)) (Real.sqrt_nonneg _))
    · simp only [neg_zero, le_refl]
  have hsmall : ∀ n, n < 2 → v n = 0 := by
    intro n hn
    simp only [v, weilDeviation, if_neg (show ¬ 2 ≤ n by omega), neg_zero]
  have hvstrict : ∃ q : ℕ, 0 < v q := by
    obtain ⟨q, hq2, hq⟩ := hstrict
    refine ⟨q, ?_⟩
    dsimp only [v, weilDeviation]
    rw [if_pos hq2]
    have hsqrt : 0 < Real.sqrt (q : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < q by omega))
    have h := div_pos (sub_pos.mpr hq) hsqrt
    rw [show -((lam q - ArithmeticFunction.vonMangoldt q) / Real.sqrt (q : ℝ)) =
      (ArithmeticFunction.vonMangoldt q - lam q) / Real.sqrt (q : ℝ) by ring]
    exact h
  have hs : Summable fun n => v n * riemannAutocorr (Real.log n) := hmoment
  obtain ⟨m, hm, hgap⟩ := exists_deficit_exceeds_twice_origin_moment hv hsmall hvstrict
  let D := ∑' n, v n * riemannAutocorr (Real.log n)
  let g := v m * riemannAutocorr 0 - 2 * D
  have hg : 0 < g := sub_pos.mpr hgap
  let T := fun L y : ℝ => ∑' n, v n *
    (truncatedRiemannAutocorr L (y + Real.log n) +
      truncatedRiemannAutocorr L (y - Real.log n))
  have hT (L y : ℝ) := summable_truncated_potential_term v L y
  have hneg (L y : ℝ) : truncatedDeviationPotential lam L y = -T L y := by
    dsimp only [truncatedDeviationPotential, T]
    rw [← tsum_neg]
    apply tsum_congr
    intro n
    dsimp only [v]
    ring
  have hT0 (L : ℝ) : T L 0 ≤ 2 * D := by
    calc
      T L 0 ≤ ∑' n, 2 * (v n * riemannAutocorr (Real.log n)) := by
        apply (hT L 0).tsum_le_tsum _ (hs.mul_left 2)
        intro n
        rw [zero_add, zero_sub, truncatedRiemannAutocorr_neg]
        have h := mul_le_mul_of_nonneg_left
          (truncatedRiemannAutocorr_le_riemannAutocorr L (Real.log n)) (hv n)
        nlinarith only [h]
      _ = 2 * D := tsum_mul_left
  have hTm (L : ℝ) : v m * truncatedRiemannAutocorr L 0 ≤ T L (Real.log m) := by
    have h := (hT L (Real.log m)).le_tsum m (fun n _ => mul_nonneg (hv n)
      (add_nonneg (truncatedRiemannAutocorr_nonneg _ _) (truncatedRiemannAutocorr_nonneg _ _)))
    have hterm : v m * truncatedRiemannAutocorr L 0 ≤ v m *
        (truncatedRiemannAutocorr L (Real.log m + Real.log m) +
          truncatedRiemannAutocorr L (Real.log m - Real.log m)) := by
      rw [sub_self]
      nlinarith only [mul_nonneg (hv m)
        (truncatedRiemannAutocorr_nonneg L (Real.log m + Real.log m))]
    exact hterm.trans h
  have hupper (L : ℝ) :
      (weilFullFunctional lam (EF.weilTest
        (logShiftRiemannDifference L (Real.log m))
        (logShiftRiemannDifference L (Real.log m)))).re ≤
      (zetaZeroConfig.W (logShiftRiemannDifference L (Real.log m))
        (logShiftRiemannDifference L (Real.log m))).re + 4 * D -
          2 * v m * truncatedRiemannAutocorr L 0 := by
    rw [logShift_probe_potential_identity, hneg L (Real.log m), hneg L 0]
    linarith only [hT0 L, hTm L]
  have hlim : Tendsto (fun L : ℝ =>
      (zetaZeroConfig.W (logShiftRiemannDifference L (Real.log m))
        (logShiftRiemannDifference L (Real.log m))).re + 4 * D -
          2 * v m * truncatedRiemannAutocorr L 0) atTop (𝓝 (-2 * g)) := by
    have h := ((tendsto_logShift_zeroSide m).add_const (4 * D)).sub
      ((tendsto_truncatedRiemannAutocorr 0).const_mul (2 * v m))
    have heq : 0 + 4 * D - (2 * v m) * riemannAutocorr 0 = -2 * g := by
      dsimp only [g]
      ring
    rw [heq] at h
    exact h
  have hev := (tendsto_order.mp (hlim.comp (tendsto_natCast_atTop_atTop (R := ℝ)))).2
    (-g) (by linarith only [hg])
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨m, hm, g, hg, max N ⌈Real.log m / 2⌉₊, ?_⟩
  intro k hk
  constructor
  · have hlog : Real.log m / 2 ≤ (k : ℝ) := (Nat.le_ceil _).trans
      (by exact_mod_cast (show ⌈Real.log m / 2⌉₊ ≤ k from (le_max_right _ _).trans hk))
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    exact (Real.log_le_iff_le_exp hmpos).mp (by linarith only [hlog])
  · have h : (zetaZeroConfig.W (logShiftRiemannDifference k (Real.log m))
        (logShiftRiemannDifference k (Real.log m))).re + 4 * D -
          2 * v m * truncatedRiemannAutocorr k 0 < -g :=
      hN k ((le_max_left _ _).trans hk)
    exact (hupper k).trans h.le

/-- Every nonnegative strict minorant has a persistent fixed negative probe;
all moment and failed-positivity premises are discharged. -/
theorem exists_fixed_logShift_separation_of_nonneg_strict_minorant {lam : ℕ → ℝ}
    (hlam : ∀ n : ℕ, 2 ≤ n → 0 ≤ lam n)
    (hminor : ∀ n : ℕ, 2 ≤ n → lam n ≤ ArithmeticFunction.vonMangoldt n)
    (hstrict : ∃ q : ℕ, 2 ≤ q ∧ lam q < ArithmeticFunction.vonMangoldt q) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      (m : ℝ) ≤ Real.exp (2 * (k : ℝ)) ∧
        (weilFullFunctional lam (EF.weilTest
          (logShiftRiemannDifference k (Real.log m))
          (logShiftRiemannDifference k (Real.log m)))).re ≤ -η := by
  have hezero : ∀ n : ℕ, deviationExcess lam n = 0 := by
    intro n
    apply max_eq_right
    unfold weilDeviation
    split_ifs with hn
    · exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hminor n hn)) (Real.sqrt_nonneg _)
    · exact le_rfl
  have hexc : Summable (deviationExcess lam) :=
    summable_zero.congr (fun n => (hezero n).symm)
  have hp := summable_potential_of_nonneg_coefficients hlam hexc 0
  have hs : Summable fun n => -weilDeviation lam n * riemannAutocorr (Real.log n) := by
    refine (hp.mul_left (-1 / 2 : ℝ)).congr (fun n => ?_)
    rw [zero_add, zero_sub, riemannAutocorr_neg]
    ring
  exact exists_fixed_logShift_minorant_separation_of_summable_origin hminor hs hstrict

end RHTower
