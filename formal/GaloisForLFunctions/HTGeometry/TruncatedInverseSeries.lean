import GaloisForLFunctions.HTGeometry.RayIntegralDecay

/-!
# Truncated series in `1/s`

The finite sums `∑_{n ≤ N} c_n s^{-n}` that approximate a balanced gamma monomial: their
derivatives, their analyticity away from the origin, and their limit along a horizontal ray.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- The truncation of a series in `1/s`. -/
def truncSeries (c : ℕ → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1), c n * s ^ (-(n : ℤ))

theorem truncSeries_eq_head_add (c : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    truncSeries c N s
      = (∑ i ∈ Finset.range N, c (i + 1) * s ^ (-((i : ℤ) + 1))) + c 0 := by
  rw [truncSeries, Finset.sum_range_succ']
  simp only [Nat.cast_zero, neg_zero, zpow_zero, mul_one]
  congr 1

theorem hasDerivAt_truncSeries (c : ℕ → ℂ) (N : ℕ) {s : ℂ} (hs : s ≠ 0) :
    HasDerivAt (truncSeries c N)
      (∑ n ∈ Finset.range (N + 1), c n * ((((-(n : ℤ)) : ℤ) : ℂ) * s ^ (-(n : ℤ) - 1))) s := by
  have hterm : ∀ n ∈ Finset.range (N + 1),
      HasDerivAt (fun z : ℂ => c n * z ^ (-(n : ℤ)))
        (c n * ((((-(n : ℤ)) : ℤ) : ℂ) * s ^ (-(n : ℤ) - 1))) s := by
    intro n _
    exact (hasDerivAt_zpow (-(n : ℤ)) s (Or.inl hs)).const_mul (c n)
  have hsum := HasDerivAt.sum hterm
  have hfun : (∑ n ∈ Finset.range (N + 1), fun z : ℂ => c n * z ^ (-(n : ℤ)))
      = truncSeries c N := by
    funext z
    rw [truncSeries, Finset.sum_apply]
  rwa [hfun] at hsum

theorem differentiableAt_truncSeries (c : ℕ → ℂ) (N : ℕ) {s : ℂ} (hs : s ≠ 0) :
    DifferentiableAt ℂ (truncSeries c N) s :=
  (hasDerivAt_truncSeries c N hs).differentiableAt

theorem analyticAt_truncSeries (c : ℕ → ℂ) (N : ℕ) {s : ℂ} (hs : s ≠ 0) :
    AnalyticAt ℂ (truncSeries c N) s := by
  have hopen : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne
  have hdiff : DifferentiableOn ℂ (truncSeries c N) {z : ℂ | z ≠ 0} := fun z hz =>
    (differentiableAt_truncSeries c N hz).differentiableWithinAt
  exact hdiff.analyticAt (hopen.mem_nhds hs)

theorem tendsto_norm_shift_ray {s : ℂ} (hs : 0 ≤ s.re) :
    Tendsto (fun x : ℝ => ‖s + (x : ℂ)‖) atTop atTop := by
  refine tendsto_atTop_mono (fun x => ?_) (tendsto_id (α := ℝ))
  have hre : (s + (x : ℂ)).re = s.re + x := by simp
  calc (id x : ℝ) = x := rfl
    _ ≤ s.re + x := by linarith
    _ = (s + (x : ℂ)).re := hre.symm
    _ ≤ |(s + (x : ℂ)).re| := le_abs_self _
    _ ≤ ‖s + (x : ℂ)‖ := Complex.abs_re_le_norm _

theorem tendsto_truncSeries_ray (c : ℕ → ℂ) (N : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun x : ℝ => truncSeries c N (s + (x : ℂ))) atTop (nhds (c 0)) := by
  have hnormtop : Tendsto (fun x : ℝ => ‖s + (x : ℂ)‖) atTop atTop :=
    tendsto_norm_shift_ray (le_of_lt hs)
  have hterm : ∀ i ∈ Finset.range N,
      Tendsto (fun x : ℝ => c (i + 1) * (s + (x : ℂ)) ^ (-((i : ℤ) + 1))) atTop (nhds 0) := by
    intro i _
    have hpow : Tendsto (fun x : ℝ => ‖s + (x : ℂ)‖ ^ (i + 1)) atTop atTop :=
      (tendsto_pow_atTop (by omega : i + 1 ≠ 0)).comp hnormtop
    have hinv : Tendsto (fun x : ℝ => (‖s + (x : ℂ)‖ ^ (i + 1))⁻¹) atTop (nhds 0) :=
      hpow.inv_tendsto_atTop
    have hz : Tendsto (fun x : ℝ => ‖(s + (x : ℂ)) ^ (-((i : ℤ) + 1))‖) atTop (nhds 0) := by
      refine hinv.congr fun x => ?_
      rw [norm_zpow]
      rw [show (-((i : ℤ) + 1)) = -(((i + 1 : ℕ) : ℤ)) by push_cast; ring]
      rw [zpow_neg, zpow_natCast]
    have hz0 : Tendsto (fun x : ℝ => (s + (x : ℂ)) ^ (-((i : ℤ) + 1))) atTop (nhds 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr hz
    have := hz0.const_mul (c (i + 1))
    simpa using this
  have hsum : Tendsto
      (fun x : ℝ => ∑ i ∈ Finset.range N, c (i + 1) * (s + (x : ℂ)) ^ (-((i : ℤ) + 1)))
      atTop (nhds 0) := by
    have := tendsto_finsetSum (Finset.range N)
      (f := fun i => fun x : ℝ => c (i + 1) * (s + (x : ℂ)) ^ (-((i : ℤ) + 1)))
      (a := fun _ => (0 : ℂ)) hterm
    simpa using this
  have hfin := hsum.add (tendsto_const_nhds (x := c 0) (f := atTop (α := ℝ)))
  rw [zero_add] at hfin
  refine hfin.congr fun x => ?_
  rw [truncSeries_eq_head_add]

end

end GaloisForLFunctions.HTGeometry
