import GaloisForLFunctions.RHTower.Sieve.HarmonicDyadicBlock
import GaloisForLFunctions.HTGeometry.DiscreteAbelIcc

/-!
# From a counting function to its logarithmic mean

A weight whose partial sums satisfy `∑_{n ≤ m} f(n) = mc + O(√m)` has logarithmic mean `c` over
every dyadic block:

    ∑_{⌈u⌉ ≤ a ≤ ⌊2u⌋} f(a)/a  →  c · log 2.

Abel summation trades the weights `1/a` for the partial sums against the forward difference
`1/m − 1/(m+1)`, whose total mass over `(M, N]` is `1/(M+1) − 1/(N+1)`; the counting error is
therefore multiplied by something of size `1/M`, and `√N/M → 0` across a block of ratio two.

This is the shape both instances of the bilinear all-interval theorem need: the natural mean of the
weight over the block and its logarithmic mean have the same value, so the normalisation by
`h√x log 2` produces the square of the block mean.
-/

namespace RHTower.Sieve

open Finset Filter Topology

/-- The partial sum of a weight. -/
noncomputable def weightCount (f : ℕ → ℝ) (m : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 m, f n

/-- The logarithmically weighted sum. -/
noncomputable def weightLogSum (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, f m / (m : ℝ)

/-- The error of the counting function against its density. -/
noncomputable def weightErr (f : ℕ → ℝ) (c : ℝ) (m : ℕ) : ℝ :=
  weightCount f m - (m : ℝ) * c

/-- Splitting a sum over `Icc 1 N` at an interior point. -/
theorem sum_Icc_one_split {M N : ℕ} (hMN : M ≤ N) (f : ℕ → ℝ) :
    ∑ m ∈ Finset.Icc 1 N, f m
      = ∑ m ∈ Finset.Icc 1 M, f m + ∑ m ∈ Finset.Icc (M + 1) N, f m := by
  have h1 : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := rfl
  have h2 : Finset.Icc 1 M = Finset.Ico 1 (M + 1) := rfl
  have h3 : Finset.Icc (M + 1) N = Finset.Ico (M + 1) (N + 1) := rfl
  rw [h1, h2, h3]
  exact (Finset.sum_Ico_consecutive f (by omega) (by omega)).symm

/-- The telescoping identity for the Abel weights. -/
theorem sum_Icc_telescope_inv {M N : ℕ} (hMN : M ≤ N) :
    ∑ m ∈ Finset.Icc (M + 1) N, (1 / (m : ℝ) - 1 / ((m : ℝ) + 1))
      = 1 / ((M : ℝ) + 1) - 1 / ((N : ℝ) + 1) := by
  have h3 : Finset.Icc (M + 1) N = Finset.Ico (M + 1) (N + 1) := rfl
  have htel := sum_Ico_telescope (fun i : ℕ => -(1 / (i : ℝ))) (m := M + 1) (N := N + 1)
    (by omega)
  rw [h3]
  have hcongr : ∀ i ∈ Finset.Ico (M + 1) (N + 1),
      (1 / (i : ℝ) - 1 / ((i : ℝ) + 1))
        = (fun i : ℕ => -(1 / (i : ℝ))) (i + 1) - (fun i : ℕ => -(1 / (i : ℝ))) i := by
    intro i _
    simp only
    push_cast
    ring
  rw [Finset.sum_congr rfl hcongr, htel]
  push_cast
  ring

/-- **Abel summation for the logarithmic sum.** -/
theorem weightLogSum_abel (f : ℕ → ℝ) (N : ℕ) :
    weightLogSum f N
      = ∑ m ∈ Finset.Icc 1 N, weightCount f m * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1))
        + weightCount f N * (1 / ((N : ℝ) + 1)) := by
  have h := HTGeometry.sum_mul_eq_partial_mul_diff f (fun m => 1 / (m : ℝ)) N
  have hL : ∑ m ∈ Finset.Icc 1 N, f m * (1 / (m : ℝ)) = weightLogSum f N := by
    rw [weightLogSum]
    exact Finset.sum_congr rfl (fun m _ => mul_one_div _ _)
  rw [hL] at h
  rw [h]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro m _
    congr 2
    push_cast
    ring
  · congr 1
    push_cast
    ring

/-- **The main term and the error term.** -/
theorem weightLogSum_eq (f : ℕ → ℝ) (c : ℝ) (N : ℕ) :
    weightLogSum f N
      = c * (∑ m ∈ Finset.Icc 1 N, 1 / ((m : ℝ) + 1))
        + (∑ m ∈ Finset.Icc 1 N, weightErr f c m * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)))
        + c * ((N : ℝ) / ((N : ℝ) + 1))
        + weightErr f c N / ((N : ℝ) + 1) := by
  rw [weightLogSum_abel]
  have hsplit : ∀ m ∈ Finset.Icc 1 N,
      weightCount f m * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1))
        = c * (1 / ((m : ℝ) + 1)) + weightErr f c m * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm.1
    have hval : weightCount f m = (m : ℝ) * c + weightErr f c m := by
      rw [weightErr]
      ring
    have hmm : (m : ℝ) * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)) = 1 / ((m : ℝ) + 1) := by
      field_simp
      ring
    rw [hval, add_mul]
    congr 1
    calc ((m : ℝ) * c) * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1))
        = c * ((m : ℝ) * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1))) := by ring
      _ = c * (1 / ((m : ℝ) + 1)) := by rw [hmm]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hbdry : weightCount f N * (1 / ((N : ℝ) + 1))
      = c * ((N : ℝ) / ((N : ℝ) + 1)) + weightErr f c N / ((N : ℝ) + 1) := by
    have hval : weightCount f N = (N : ℝ) * c + weightErr f c N := by
      rw [weightErr]
      ring
    rw [hval]
    ring
  rw [hbdry]
  ring

/-- **The block difference of the logarithmic sum.**  Only `O(√N/M)` is lost. -/
theorem abs_weightLogSum_sub_le {f : ℕ → ℝ} {c C : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hcount : ∀ m : ℕ, |weightErr f c m| ≤ C * Real.sqrt m + C)
    {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) :
    |weightLogSum f N - weightLogSum f M
        - c * ∑ m ∈ Finset.Icc (M + 1) N, 1 / ((m : ℝ) + 1)|
      ≤ (3 * (C * Real.sqrt N + C) + c) / ((M : ℝ) + 1) := by
  have hM0 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hMN' : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
  have hsN : Real.sqrt M ≤ Real.sqrt N := Real.sqrt_le_sqrt hMN'
  have hsM0 : (0 : ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hmain := sum_Icc_one_split hMN (fun m => 1 / ((m : ℝ) + 1))
  have herr := sum_Icc_one_split hMN
    (fun m => weightErr f c m * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)))
  have htail : |∑ m ∈ Finset.Icc (M + 1) N, weightErr f c m * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1))|
      ≤ (C * Real.sqrt N + C) / ((M : ℝ) + 1) := by
    have hterm : ∀ m ∈ Finset.Icc (M + 1) N,
        |weightErr f c m * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1))|
          ≤ (C * Real.sqrt N + C) * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)) := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      have hm0 : (0 : ℝ) < (m : ℝ) := by
        have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
        linarith
      have hmN : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hm.2
      have hw : (0 : ℝ) ≤ 1 / (m : ℝ) - 1 / ((m : ℝ) + 1) := by
        have : 1 / ((m : ℝ) + 1) ≤ 1 / (m : ℝ) := by
          apply one_div_le_one_div_of_le hm0
          linarith
        linarith
      have hsm : Real.sqrt m ≤ Real.sqrt N := Real.sqrt_le_sqrt hmN
      rw [abs_mul, abs_of_nonneg hw]
      refine mul_le_mul_of_nonneg_right ?_ hw
      refine le_trans (hcount m) ?_
      nlinarith
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum, sum_Icc_telescope_inv hMN]
    have hpos : (0 : ℝ) ≤ C * Real.sqrt N + C := by nlinarith
    have hle : 1 / ((M : ℝ) + 1) - 1 / ((N : ℝ) + 1) ≤ 1 / ((M : ℝ) + 1) := by
      have : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
      linarith
    calc (C * Real.sqrt N + C) * (1 / ((M : ℝ) + 1) - 1 / ((N : ℝ) + 1))
        ≤ (C * Real.sqrt N + C) * (1 / ((M : ℝ) + 1)) := mul_le_mul_of_nonneg_left hle hpos
      _ = (C * Real.sqrt N + C) / ((M : ℝ) + 1) := by ring
  have hbN : |weightErr f c N / ((N : ℝ) + 1)| ≤ (C * Real.sqrt N + C) / ((M : ℝ) + 1) := by
    rw [abs_div, abs_of_pos hN0]
    refine le_trans (div_le_div_of_nonneg_right (hcount N) hN0.le) ?_
    refine div_le_div_of_nonneg_left ?_ hM0 (by linarith)
    nlinarith
  have hbM : |weightErr f c M / ((M : ℝ) + 1)| ≤ (C * Real.sqrt N + C) / ((M : ℝ) + 1) := by
    rw [abs_div, abs_of_pos hM0]
    refine div_le_div_of_nonneg_right ?_ hM0.le
    refine le_trans (hcount M) ?_
    nlinarith
  have hdrift : |c * ((N : ℝ) / ((N : ℝ) + 1)) - c * ((M : ℝ) / ((M : ℝ) + 1))|
      ≤ c / ((M : ℝ) + 1) := by
    have hval : (N : ℝ) / ((N : ℝ) + 1) - (M : ℝ) / ((M : ℝ) + 1)
        = 1 / ((M : ℝ) + 1) - 1 / ((N : ℝ) + 1) := by
      field_simp
      ring
    have hbound : |(N : ℝ) / ((N : ℝ) + 1) - (M : ℝ) / ((M : ℝ) + 1)| ≤ 1 / ((M : ℝ) + 1) := by
      rw [hval, abs_of_nonneg]
      · have : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
        linarith
      · have hle : 1 / ((N : ℝ) + 1) ≤ 1 / ((M : ℝ) + 1) := by
          apply one_div_le_one_div_of_le hM0
          linarith
        linarith
    rw [← mul_sub, abs_mul, abs_of_nonneg hc]
    calc c * |(N : ℝ) / ((N : ℝ) + 1) - (M : ℝ) / ((M : ℝ) + 1)|
        ≤ c * (1 / ((M : ℝ) + 1)) := mul_le_mul_of_nonneg_left hbound hc
      _ = c / ((M : ℝ) + 1) := by ring
  rw [weightLogSum_eq f c N, weightLogSum_eq f c M, hmain, herr]
  have hrw : c * ((∑ m ∈ Finset.Icc 1 M, 1 / ((m : ℝ) + 1))
        + ∑ m ∈ Finset.Icc (M + 1) N, 1 / ((m : ℝ) + 1))
      + ((∑ m ∈ Finset.Icc 1 M, weightErr f c m * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)))
        + ∑ m ∈ Finset.Icc (M + 1) N, weightErr f c m * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)))
      + c * ((N : ℝ) / ((N : ℝ) + 1))
      + weightErr f c N / ((N : ℝ) + 1)
      - (c * (∑ m ∈ Finset.Icc 1 M, 1 / ((m : ℝ) + 1))
        + (∑ m ∈ Finset.Icc 1 M, weightErr f c m * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)))
        + c * ((M : ℝ) / ((M : ℝ) + 1))
        + weightErr f c M / ((M : ℝ) + 1))
      - c * ∑ m ∈ Finset.Icc (M + 1) N, 1 / ((m : ℝ) + 1)
      = (∑ m ∈ Finset.Icc (M + 1) N, weightErr f c m * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)))
        + (c * ((N : ℝ) / ((N : ℝ) + 1)) - c * ((M : ℝ) / ((M : ℝ) + 1)))
        + (weightErr f c N / ((N : ℝ) + 1) - weightErr f c M / ((M : ℝ) + 1)) := by ring
  rw [hrw]
  refine le_trans (abs_add_three _ _ _) ?_
  have habs3 : |weightErr f c N / ((N : ℝ) + 1) - weightErr f c M / ((M : ℝ) + 1)|
      ≤ |weightErr f c N / ((N : ℝ) + 1)| + |weightErr f c M / ((M : ℝ) + 1)| :=
    abs_sub _ _
  have hsum : (3 * (C * Real.sqrt N + C) + c) / ((M : ℝ) + 1)
      = (C * Real.sqrt N + C) / ((M : ℝ) + 1) + c / ((M : ℝ) + 1)
        + ((C * Real.sqrt N + C) / ((M : ℝ) + 1) + (C * Real.sqrt N + C) / ((M : ℝ) + 1)) := by
    field_simp
    ring
  rw [hsum]
  linarith [habs3, htail, hdrift, hbN, hbM]

/-- Shifting an integer interval by one. -/
theorem sum_Icc_shift_one (p q : ℕ) (f : ℕ → ℝ) :
    ∑ b ∈ Finset.Icc (p + 1) (q + 1), f b = ∑ m ∈ Finset.Icc p q, f (m + 1) := by
  rw [← Finset.map_add_right_Icc p q 1, Finset.sum_map]
  rfl

/-- The shifted harmonic sum over the block. -/
theorem sum_block_one_div_succ (p q : ℕ) :
    ∑ m ∈ Finset.Icc p q, 1 / ((m : ℝ) + 1) = ∑ b ∈ Finset.Icc (p + 1) (q + 1), 1 / (b : ℝ) := by
  rw [sum_Icc_shift_one p q (fun b => 1 / (b : ℝ))]
  refine Finset.sum_congr rfl ?_
  intro m _
  push_cast
  ring

/-- The shifted endpoints still have the right normalised growth. -/
theorem tendsto_ceil_succ_div :
    Tendsto (fun u : ℝ => ((⌈u⌉₊ + 1 : ℕ) : ℝ) / u) atTop (𝓝 1) := by
  have hbase : Tendsto (fun u : ℝ => ((⌈u⌉₊ : ℝ)) / u + 1 / u) atTop (𝓝 1) := by
    have := tendsto_ceil_div.add tendsto_one_div_atTop
    rwa [add_zero] at this
  refine Tendsto.congr' ?_ hbase
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  push_cast
  field_simp

theorem tendsto_floor_two_mul_succ_div :
    Tendsto (fun u : ℝ => ((⌊2 * u⌋₊ + 1 : ℕ) : ℝ) / u) atTop (𝓝 2) := by
  have hbase : Tendsto (fun u : ℝ => ((⌊2 * u⌋₊ : ℝ)) / u + 1 / u) atTop (𝓝 2) := by
    have := tendsto_floor_two_mul_div.add tendsto_one_div_atTop
    rwa [add_zero] at this
  refine Tendsto.congr' ?_ hbase
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  push_cast
  field_simp

/-- The harmonic main term of the block, after the shift. -/
theorem tendsto_sum_block_one_div_succ :
    Tendsto (fun u : ℝ => ∑ m ∈ Finset.Icc ⌈u⌉₊ ⌊2 * u⌋₊, 1 / ((m : ℝ) + 1))
      atTop (𝓝 (Real.log 2)) := by
  have hgen := tendsto_sum_Icc_one_div_of_ratio
    (p := fun u : ℝ => ⌈u⌉₊ + 1) (q := fun u : ℝ => ⌊2 * u⌋₊ + 1)
    tendsto_ceil_succ_div tendsto_floor_two_mul_succ_div ?_ ?_
  · refine Tendsto.congr' ?_ hgen
    filter_upwards with u
    exact (sum_block_one_div_succ ⌈u⌉₊ ⌊2 * u⌋₊).symm
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
    have : 1 ≤ ⌈u⌉₊ := Nat.one_le_ceil_iff.2 (by linarith)
    omega
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
    have hce : ((⌈u⌉₊ : ℝ)) ≤ u + 1 := (Nat.ceil_lt_add_one (by linarith)).le
    have hfl : 2 * u - 1 ≤ ((⌊2 * u⌋₊ : ℝ)) := by
      have := Nat.lt_floor_add_one (2 * u)
      linarith
    have : ((⌈u⌉₊ : ℝ)) ≤ ((⌊2 * u⌋₊ : ℝ)) + 1 := by linarith
    have hnat : ⌈u⌉₊ ≤ ⌊2 * u⌋₊ + 1 := by exact_mod_cast this
    omega

/-- **The logarithmic mean over a dyadic block, from a square-root-accurate count.** -/
theorem tendsto_block_log_mean_of_count {f : ℕ → ℝ} {c C : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hcount : ∀ m : ℕ, |weightErr f c m| ≤ C * Real.sqrt m + C) :
    Tendsto (fun u : ℝ => ∑ a ∈ Finset.Icc ⌈u⌉₊ ⌊2 * u⌋₊, f a / (a : ℝ))
      atTop (𝓝 (c * Real.log 2)) := by
  have hmainlim : Tendsto
      (fun u : ℝ => c * ∑ m ∈ Finset.Icc ⌈u⌉₊ ⌊2 * u⌋₊, 1 / ((m : ℝ) + 1))
      atTop (𝓝 (c * Real.log 2)) :=
    tendsto_sum_block_one_div_succ.const_mul c
  have hsqrtinv : Tendsto (fun u : ℝ => 1 / Real.sqrt u) atTop (𝓝 0) :=
    tendsto_one_div_atTop.comp Real.tendsto_sqrt_atTop
  have hmaj : Tendsto
      (fun u : ℝ => 3 * C * Real.sqrt 2 * (1 / Real.sqrt u) + (3 * C + c) * (1 / u))
      atTop (𝓝 0) := by
    have h1 := hsqrtinv.const_mul (3 * C * Real.sqrt 2)
    have h2 := tendsto_one_div_atTop.const_mul (3 * C + c)
    have := h1.add h2
    simpa using this
  have hdiff : Tendsto
      (fun u : ℝ => (∑ a ∈ Finset.Icc ⌈u⌉₊ ⌊2 * u⌋₊, f a / (a : ℝ))
        - c * ∑ m ∈ Finset.Icc ⌈u⌉₊ ⌊2 * u⌋₊, 1 / ((m : ℝ) + 1)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with u hu
    have hu0 : (0 : ℝ) < u := by linarith
    have hce2 : 2 ≤ ⌈u⌉₊ := by
      have hle : u ≤ ((⌈u⌉₊ : ℝ)) := Nat.le_ceil u
      have : (2 : ℝ) ≤ ((⌈u⌉₊ : ℝ)) := by linarith
      exact_mod_cast this
    have hcefl : ⌈u⌉₊ ≤ ⌊2 * u⌋₊ + 1 := by
      have hce : ((⌈u⌉₊ : ℝ)) ≤ u + 1 := (Nat.ceil_lt_add_one hu0.le).le
      have hfl : 2 * u - 1 ≤ ((⌊2 * u⌋₊ : ℝ)) := by
        have := Nat.lt_floor_add_one (2 * u)
        linarith
      have : ((⌈u⌉₊ : ℝ)) ≤ ((⌊2 * u⌋₊ : ℝ)) + 1 := by linarith
      exact_mod_cast this
    set M : ℕ := ⌈u⌉₊ - 1 with hMdef
    set N : ℕ := ⌊2 * u⌋₊ with hNdef
    have hM1 : M + 1 = ⌈u⌉₊ := by omega
    have hM : 1 ≤ M := by omega
    have hMN : M ≤ N := by omega
    have hsplit := sum_Icc_one_split (M := M) (N := N) hMN (fun m => f m / (m : ℝ))
    have hbase := abs_weightLogSum_sub_le hc hC hcount hM hMN
    rw [hM1] at hbase hsplit
    have hval : (∑ a ∈ Finset.Icc ⌈u⌉₊ N, f a / (a : ℝ))
        - c * ∑ m ∈ Finset.Icc ⌈u⌉₊ N, 1 / ((m : ℝ) + 1)
        = weightLogSum f N - weightLogSum f M
          - c * ∑ m ∈ Finset.Icc ⌈u⌉₊ N, 1 / ((m : ℝ) + 1) := by
      rw [weightLogSum, weightLogSum, hsplit]
      ring
    rw [Real.norm_eq_abs, hval]
    refine le_trans hbase ?_
    have hMR : (M : ℝ) + 1 = ((⌈u⌉₊ : ℕ) : ℝ) := by
      rw [← hM1]
      push_cast
      ring
    have hcelow : u ≤ ((⌈u⌉₊ : ℝ)) := Nat.le_ceil u
    have hNle : ((N : ℝ)) ≤ 2 * u := Nat.floor_le (by linarith)
    have hsqN : Real.sqrt N ≤ Real.sqrt 2 * Real.sqrt u := by
      have h2u : Real.sqrt ((N : ℝ)) ≤ Real.sqrt (2 * u) := Real.sqrt_le_sqrt hNle
      rwa [Real.sqrt_mul (by norm_num)] at h2u
    have hden : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have hnum : 3 * (C * Real.sqrt N + C) + c
        ≤ 3 * C * (Real.sqrt 2 * Real.sqrt u) + (3 * C + c) := by nlinarith
    have hstep : (3 * (C * Real.sqrt N + C) + c) / ((M : ℝ) + 1)
        ≤ (3 * C * (Real.sqrt 2 * Real.sqrt u) + (3 * C + c)) / u := by
      have hu' : u ≤ (M : ℝ) + 1 := by rw [hMR]; exact hcelow
      have hnn : (0 : ℝ) ≤ 3 * C * (Real.sqrt 2 * Real.sqrt u) + (3 * C + c) := by
        have h2 : (0 : ℝ) ≤ Real.sqrt 2 * Real.sqrt u := by positivity
        nlinarith
      calc (3 * (C * Real.sqrt N + C) + c) / ((M : ℝ) + 1)
          ≤ (3 * C * (Real.sqrt 2 * Real.sqrt u) + (3 * C + c)) / ((M : ℝ) + 1) :=
            div_le_div_of_nonneg_right hnum hden.le
        _ ≤ (3 * C * (Real.sqrt 2 * Real.sqrt u) + (3 * C + c)) / u :=
            div_le_div_of_nonneg_left hnn hu0 hu'
    refine le_trans hstep (le_of_eq ?_)
    have hsu : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.2 hu0
    have husq : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu0.le
    have hinv : Real.sqrt u / u = 1 / Real.sqrt u := by
      rw [div_eq_div_iff (ne_of_gt hu0) (ne_of_gt hsu), one_mul]
      exact husq
    have hexp : (3 * C * (Real.sqrt 2 * Real.sqrt u) + (3 * C + c)) / u
        = 3 * C * Real.sqrt 2 * (Real.sqrt u / u) + (3 * C + c) * (1 / u) := by ring
    rw [hexp, hinv]
  have hres := hdiff.add hmainlim
  rw [zero_add] at hres
  refine hres.congr fun u => ?_
  ring

end RHTower.Sieve
