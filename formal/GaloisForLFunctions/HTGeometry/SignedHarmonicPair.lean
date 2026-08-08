import GaloisForLFunctions.HTGeometry.AlternatingHarmonicPair

/-!
# The signed harmonic gap series

The alternating series of consecutive harmonic gaps

`∑_{k ≥ 1} (-1)^k (1/k - 1/(k+1)) = 1 - 2 log 2`.

Its terms are `(-1)^k / (k(k+1))`, so unlike the alternating harmonic series itself the sum is
absolutely convergent and is a genuine `HasSum`.  The value is obtained by grouping consecutive
terms in pairs: the odd-indexed group is the grouped alternating harmonic series `log 2`, and the
even-indexed group is its complement `1 - log 2`, the two of them adding up to the telescoping
series `∑ (1/(2j+1) - 1/(2j+3)) = 1`.  Absolute convergence lets the value of the grouped
subsequence be transferred back to the full series.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The `j`-th term of `∑_{k ≥ 1} (-1)^k (1/k - 1/(k+1))`, indexed by `k = j + 1`. -/
noncomputable def signedHarmonicPair (j : ℕ) : ℝ :=
  (-1) ^ (j + 1) * (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2))

/-- The even-indexed grouped term `1/(2j+2) - 1/(2j+3)`. -/
noncomputable def evenGapPair (j : ℕ) : ℝ := 1 / (2 * (j : ℝ) + 2) - 1 / (2 * (j : ℝ) + 3)

/-- The telescoping term `1/(2j+1) - 1/(2j+3)`. -/
noncomputable def oddGapPair (j : ℕ) : ℝ := 1 / (2 * (j : ℝ) + 1) - 1 / (2 * (j : ℝ) + 3)

theorem signedHarmonicPair_eq (j : ℕ) :
    signedHarmonicPair j = (-1) ^ (j + 1) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
  have h1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (j : ℝ) + 2 := by positivity
  rw [signedHarmonicPair]
  field_simp
  ring

theorem abs_signedHarmonicPair (j : ℕ) :
    |signedHarmonicPair j| = 1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
  rw [signedHarmonicPair_eq, abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos (by positivity : (0 : ℝ) < ((j : ℝ) + 1) * ((j : ℝ) + 2))]

/-- The signed gap series converges absolutely. -/
theorem summable_signedHarmonicPair : Summable signedHarmonicPair := by
  have hmaj : Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) := by
    have h := (Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two
    refine ((summable_nat_add_iff 1).2 h).congr fun k => ?_
    push_cast
    ring_nf
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) hmaj
  rw [Real.norm_eq_abs, abs_signedHarmonicPair,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [Nat.cast_nonneg (α := ℝ) j]

theorem signedHarmonicPair_two_mul (j : ℕ) :
    signedHarmonicPair (2 * j) = -alternatingHarmonicPair j := by
  have hsign : (-1 : ℝ) ^ (2 * j + 1) = -1 := by
    rw [pow_succ, pow_mul]
    norm_num
  rw [signedHarmonicPair, alternatingHarmonicPair, hsign]
  push_cast
  ring

theorem signedHarmonicPair_two_mul_add_one (j : ℕ) :
    signedHarmonicPair (2 * j + 1) = evenGapPair j := by
  have hsign : (-1 : ℝ) ^ (2 * j + 1 + 1) = 1 := by
    rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, pow_mul]
    norm_num
  rw [signedHarmonicPair, evenGapPair, hsign]
  push_cast
  ring

theorem oddGapPair_eq_add (j : ℕ) :
    oddGapPair j = alternatingHarmonicPair j + evenGapPair j := by
  rw [oddGapPair, alternatingHarmonicPair, evenGapPair]
  ring

theorem sum_oddGapPair (N : ℕ) :
    ∑ j ∈ Finset.range N, oddGapPair j = 1 - 1 / (2 * (N : ℝ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, oddGapPair]
      have h1 : (0 : ℝ) < 2 * (N : ℝ) + 1 := by positivity
      have h3 : (0 : ℝ) < 2 * (N : ℝ) + 3 := by positivity
      push_cast
      field_simp
      ring

/-- The telescoping series sums to `1`. -/
theorem hasSum_oddGapPair : HasSum oddGapPair 1 := by
  have hnn : ∀ j : ℕ, 0 ≤ oddGapPair j := by
    intro j
    rw [oddGapPair, sub_nonneg]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hsummable : Summable oddGapPair := by
    refine summable_of_sum_range_le (c := 1) hnn fun n => ?_
    rw [sum_oddGapPair]
    have : (0 : ℝ) ≤ 1 / (2 * (n : ℝ) + 1) := by positivity
    linarith
  refine hsummable.hasSum_iff_tendsto_nat.mpr ?_
  have hzero : Tendsto (fun N : ℕ => 1 / (2 * (N : ℝ) + 1)) atTop (𝓝 0) := by
    refine squeeze_zero (fun N => by positivity) (fun N => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact one_div_le_one_div_of_le (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) N])
  have hlim := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub hzero
  rw [sub_zero] at hlim
  exact hlim.congr fun N => (sum_oddGapPair N).symm

/-- The even-indexed grouped series is the complement of the grouped alternating harmonic series. -/
theorem hasSum_evenGapPair : HasSum evenGapPair (1 - Real.log 2) := by
  have h := hasSum_oddGapPair.sub hasSum_alternatingHarmonicPair
  have hfun : (fun j => oddGapPair j - alternatingHarmonicPair j) = evenGapPair := by
    funext j
    rw [oddGapPair_eq_add]
    ring
  rwa [hfun] at h

theorem sum_range_two_mul_signedHarmonicPair (N : ℕ) :
    ∑ i ∈ Finset.range (2 * N), signedHarmonicPair i
      = ∑ j ∈ Finset.range N, (-alternatingHarmonicPair j + evenGapPair j) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring]
      simp only [Finset.sum_range_succ]
      rw [ih, signedHarmonicPair_two_mul, signedHarmonicPair_two_mul_add_one]
      ring

/-- **The signed harmonic gap series.**  `∑_{k ≥ 1} (-1)^k (1/k - 1/(k+1)) = 1 - 2 log 2`. -/
theorem hasSum_signedHarmonicPair : HasSum signedHarmonicPair (1 - 2 * Real.log 2) := by
  have hS := summable_signedHarmonicPair.hasSum
  set S := ∑' j, signedHarmonicPair j with hSdef
  have h1 : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, signedHarmonicPair i) atTop (𝓝 S) :=
    summable_signedHarmonicPair.hasSum_iff_tendsto_nat.mp hS
  have hdil : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_mono (fun N => by simp only [id_eq]; omega) tendsto_id
  have h2 : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range (2 * N), signedHarmonicPair i) atTop (𝓝 S) :=
    h1.comp hdil
  have hgrp : HasSum (fun j => -alternatingHarmonicPair j + evenGapPair j)
      (-Real.log 2 + (1 - Real.log 2)) :=
    hasSum_alternatingHarmonicPair.neg.add hasSum_evenGapPair
  have h3 : Tendsto
      (fun N : ℕ => ∑ j ∈ Finset.range N, (-alternatingHarmonicPair j + evenGapPair j)) atTop
      (𝓝 (-Real.log 2 + (1 - Real.log 2))) :=
    hgrp.summable.hasSum_iff_tendsto_nat.mp hgrp
  have h4 : S = -Real.log 2 + (1 - Real.log 2) := by
    refine tendsto_nhds_unique h2 (h3.congr fun N => ?_)
    rw [← sum_range_two_mul_signedHarmonicPair N]
  have h5 : S = 1 - 2 * Real.log 2 := by rw [h4]; ring
  rw [← h5]
  exact hS

theorem tsum_signedHarmonicPair :
    ∑' j : ℕ, signedHarmonicPair j = 1 - 2 * Real.log 2 :=
  hasSum_signedHarmonicPair.tsum_eq

end GaloisForLFunctions.HTGeometry
