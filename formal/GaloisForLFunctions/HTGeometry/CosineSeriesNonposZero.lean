import GaloisForLFunctions.HTGeometry.CosineSumNonposZero

/-!
# An absolutely convergent cosine series with distinct positive frequencies that is nonpositive
everywhere vanishes

Truncating the series after `N` terms changes it by at most the tail `∑_{n ≥ N} |c n|`, so the
finite Cesàro bounds give `± c j / 2 ≤ tail N` for every `N > j`, and the tail tends to `0`.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

theorem cosineSeries_coeff_eq_zero_of_nonpos (c a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (hinj : Function.Injective a) (hc : Summable fun n => |c n|)
    (hF : ∀ t : ℝ, ∑' n, c n * Real.cos (a n * t) ≤ 0) : ∀ j, c j = 0 := by
  intro j
  have hterm : ∀ t n, |c n * Real.cos (a n * t)| ≤ |c n| := fun t n => by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have hsum : ∀ t, Summable fun n => c n * Real.cos (a n * t) := fun t =>
    Summable.of_norm_bounded hc fun n => by rw [Real.norm_eq_abs]; exact hterm t n
  have htail : ∀ N t, ∑ n ∈ Finset.range N, c n * Real.cos (a n * t) ≤ ∑' n, |c (n + N)| := by
    intro N t
    have hsplit := (hsum t).sum_add_tsum_nat_add N
    have hcN : Summable fun n => |c (n + N)| := hc.comp_injective (add_left_injective N)
    have hsN' : Summable fun n => ‖c (n + N) * Real.cos (a (n + N) * t)‖ :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _)
        (fun n => by rw [Real.norm_eq_abs]; exact hterm t (n + N)) hcN
    have h1 : |∑' n, c (n + N) * Real.cos (a (n + N) * t)| ≤ ∑' n, |c (n + N)| := by
      calc |∑' n, c (n + N) * Real.cos (a (n + N) * t)|
          = ‖∑' n, c (n + N) * Real.cos (a (n + N) * t)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∑' n, ‖c (n + N) * Real.cos (a (n + N) * t)‖ := norm_tsum_le_tsum_norm hsN'
        _ ≤ ∑' n, |c (n + N)| :=
            Summable.tsum_le_tsum (fun n => by rw [Real.norm_eq_abs]; exact hterm t (n + N))
              hsN' hcN
    have h2 := neg_abs_le (∑' n, c (n + N) * Real.cos (a (n + N) * t))
    linarith [hF t, hsplit]
  have hε : Tendsto (fun N => ∑' n, |c (n + N)|) atTop (𝓝 0) :=
    tendsto_sum_nat_add (fun n => |c n|)
  have hjN : ∀ᶠ N in atTop, c j / 2 ≤ ∑' n, |c (n + N)| ∧ -(c j / 2) ≤ ∑' n, |c (n + N)| := by
    filter_upwards [eventually_gt_atTop j] with N hN
    exact cosineSum_coeff_le_of_le (Finset.range N) c a (fun n _ => ha n) hinj.injOn (htail N) j
      (Finset.mem_range.mpr hN)
  have h1 : c j / 2 ≤ 0 := ge_of_tendsto hε (hjN.mono fun N h => h.1)
  have h2 : -(c j / 2) ≤ 0 := ge_of_tendsto hε (hjN.mono fun N h => h.2)
  linarith

end GaloisForLFunctions.HTGeometry
