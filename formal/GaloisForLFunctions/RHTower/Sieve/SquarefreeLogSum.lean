import GaloisForLFunctions.RHTower.Sieve.SquarefreeGlobalCount
import GaloisForLFunctions.RHTower.Sieve.HarmonicDyadicBlock
import GaloisForLFunctions.HTGeometry.DiscreteAbelIcc

/-!
# The logarithmic mean of the squarefree indicator

The fibre decomposition weights each outer factor by `1/a`, so the `μ²` instance of the bilinear
all-interval theorem needs the *logarithmic* block mean

    ∑_{√x < a ≤ 2√x} μ²(a)/a  →  D log 2,      D = 6/π².

Abel summation against the count `A(m) = #{n ≤ m : n squarefree} = mD + E(m)`, `|E(m)| ≤ 2√m + 1`,
turns the weighted sum into a harmonic sum plus an error controlled by `E`:

    ∑_{m ≤ N} μ²(m)/m  =  D ∑_{m ≤ N} 1/(m+1)  +  ∑_{m ≤ N} E(m)/(m(m+1))  +  D·N/(N+1)
                          +  E(N)/(N+1),

and the error terms telescope against `∑ (1/m − 1/(m+1)) = 1/(M+1) − 1/(N+1)`, so a difference of
two such sums over a block of ratio two loses only `O(√N/M)`.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction Filter Topology

/-- The squarefree count up to `m`. -/
noncomputable def squarefreeCount (m : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 m, ((moebius n : ℤ) : ℝ) ^ 2

/-- The logarithmically weighted squarefree sum. -/
noncomputable def squarefreeLogSum (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ((moebius m : ℤ) : ℝ) ^ 2 / (m : ℝ)

/-- The error in the squarefree count. -/
noncomputable def sqfErr (m : ℕ) : ℝ := squarefreeCount m - (m : ℝ) * squarefreeDensity

theorem abs_sqfErr_le (m : ℕ) : |sqfErr m| ≤ 2 * Real.sqrt m + 1 :=
  abs_sum_moebius_sq_Icc_sub_le m

theorem squarefreeDensity_nonneg' : 0 ≤ squarefreeDensity := by
  rw [squarefreeDensity_eq]
  positivity

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

/-- **Abel summation for the logarithmic squarefree sum.** -/
theorem squarefreeLogSum_abel (N : ℕ) :
    squarefreeLogSum N
      = ∑ m ∈ Finset.Icc 1 N, squarefreeCount m * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1))
        + squarefreeCount N * (1 / ((N : ℝ) + 1)) := by
  have h := HTGeometry.sum_mul_eq_partial_mul_diff
    (fun m => ((moebius m : ℤ) : ℝ) ^ 2) (fun m => 1 / (m : ℝ)) N
  have hL : ∑ m ∈ Finset.Icc 1 N, ((moebius m : ℤ) : ℝ) ^ 2 * (1 / (m : ℝ))
      = squarefreeLogSum N := by
    rw [squarefreeLogSum]
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
theorem squarefreeLogSum_eq (N : ℕ) :
    squarefreeLogSum N
      = squarefreeDensity * (∑ m ∈ Finset.Icc 1 N, 1 / ((m : ℝ) + 1))
        + (∑ m ∈ Finset.Icc 1 N, sqfErr m * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)))
        + squarefreeDensity * ((N : ℝ) / ((N : ℝ) + 1))
        + sqfErr N / ((N : ℝ) + 1) := by
  rw [squarefreeLogSum_abel]
  have hsplit : ∀ m ∈ Finset.Icc 1 N,
      squarefreeCount m * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1))
        = squarefreeDensity * (1 / ((m : ℝ) + 1))
          + sqfErr m * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm.1
    have hval : squarefreeCount m = (m : ℝ) * squarefreeDensity + sqfErr m := by
      rw [sqfErr]
      ring
    have hmm : (m : ℝ) * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)) = 1 / ((m : ℝ) + 1) := by
      field_simp
      ring
    rw [hval, add_mul]
    congr 1
    calc ((m : ℝ) * squarefreeDensity) * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1))
        = squarefreeDensity * ((m : ℝ) * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1))) := by ring
      _ = squarefreeDensity * (1 / ((m : ℝ) + 1)) := by rw [hmm]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hbdry : squarefreeCount N * (1 / ((N : ℝ) + 1))
      = squarefreeDensity * ((N : ℝ) / ((N : ℝ) + 1)) + sqfErr N / ((N : ℝ) + 1) := by
    have hval : squarefreeCount N = (N : ℝ) * squarefreeDensity + sqfErr N := by
      rw [sqfErr]
      ring
    rw [hval]
    ring
  rw [hbdry]
  ring

/-- **The block difference of the logarithmic sum.**  Only `O(√N/M)` is lost. -/
theorem abs_squarefreeLogSum_sub_le {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) :
    |squarefreeLogSum N - squarefreeLogSum M
        - squarefreeDensity * ∑ m ∈ Finset.Icc (M + 1) N, 1 / ((m : ℝ) + 1)|
      ≤ (3 * (2 * Real.sqrt N + 1) + squarefreeDensity) / ((M : ℝ) + 1) := by
  have hD := squarefreeDensity_nonneg'
  have hM0 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hMN' : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
  have hsN : Real.sqrt M ≤ Real.sqrt N := Real.sqrt_le_sqrt hMN'
  have hsM0 : (0 : ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg _
  -- the harmonic main terms
  have hmain := sum_Icc_one_split hMN (fun m => 1 / ((m : ℝ) + 1))
  -- the error sums
  have herr := sum_Icc_one_split hMN (fun m => sqfErr m * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)))
  -- the tail error is small
  have htail : |∑ m ∈ Finset.Icc (M + 1) N, sqfErr m * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1))|
      ≤ (2 * Real.sqrt N + 1) / ((M : ℝ) + 1) := by
    have hterm : ∀ m ∈ Finset.Icc (M + 1) N,
        |sqfErr m * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1))|
          ≤ (2 * Real.sqrt N + 1) * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)) := by
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
      exact le_trans (abs_sqfErr_le m) (by linarith)
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum, sum_Icc_telescope_inv hMN]
    have hpos : (0 : ℝ) ≤ 2 * Real.sqrt N + 1 := by linarith
    have hle : 1 / ((M : ℝ) + 1) - 1 / ((N : ℝ) + 1) ≤ 1 / ((M : ℝ) + 1) := by
      have : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
      linarith
    calc (2 * Real.sqrt N + 1) * (1 / ((M : ℝ) + 1) - 1 / ((N : ℝ) + 1))
        ≤ (2 * Real.sqrt N + 1) * (1 / ((M : ℝ) + 1)) := by
          exact mul_le_mul_of_nonneg_left hle hpos
      _ = (2 * Real.sqrt N + 1) / ((M : ℝ) + 1) := by ring
  -- the two boundary terms
  have hbN : |sqfErr N / ((N : ℝ) + 1)| ≤ (2 * Real.sqrt N + 1) / ((M : ℝ) + 1) := by
    rw [abs_div, abs_of_pos hN0]
    refine le_trans (div_le_div_of_nonneg_right (abs_sqfErr_le N) hN0.le) ?_
    refine div_le_div_of_nonneg_left (by linarith) hM0 ?_
    have : (M : ℝ) ≤ (N : ℝ) := hMN'
    linarith
  have hbM : |sqfErr M / ((M : ℝ) + 1)| ≤ (2 * Real.sqrt N + 1) / ((M : ℝ) + 1) := by
    rw [abs_div, abs_of_pos hM0]
    refine div_le_div_of_nonneg_right ?_ hM0.le
    exact le_trans (abs_sqfErr_le M) (by linarith)
  -- the density drift
  have hdrift : |squarefreeDensity * ((N : ℝ) / ((N : ℝ) + 1))
      - squarefreeDensity * ((M : ℝ) / ((M : ℝ) + 1))|
      ≤ squarefreeDensity / ((M : ℝ) + 1) := by
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
    rw [← mul_sub, abs_mul, abs_of_nonneg hD]
    calc squarefreeDensity * |(N : ℝ) / ((N : ℝ) + 1) - (M : ℝ) / ((M : ℝ) + 1)|
        ≤ squarefreeDensity * (1 / ((M : ℝ) + 1)) := mul_le_mul_of_nonneg_left hbound hD
      _ = squarefreeDensity / ((M : ℝ) + 1) := by ring
  rw [squarefreeLogSum_eq N, squarefreeLogSum_eq M, hmain, herr]
  have hrw : squarefreeDensity * ((∑ m ∈ Finset.Icc 1 M, 1 / ((m : ℝ) + 1))
        + ∑ m ∈ Finset.Icc (M + 1) N, 1 / ((m : ℝ) + 1))
      + ((∑ m ∈ Finset.Icc 1 M, sqfErr m * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)))
        + ∑ m ∈ Finset.Icc (M + 1) N, sqfErr m * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)))
      + squarefreeDensity * ((N : ℝ) / ((N : ℝ) + 1))
      + sqfErr N / ((N : ℝ) + 1)
      - (squarefreeDensity * (∑ m ∈ Finset.Icc 1 M, 1 / ((m : ℝ) + 1))
        + (∑ m ∈ Finset.Icc 1 M, sqfErr m * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)))
        + squarefreeDensity * ((M : ℝ) / ((M : ℝ) + 1))
        + sqfErr M / ((M : ℝ) + 1))
      - squarefreeDensity * ∑ m ∈ Finset.Icc (M + 1) N, 1 / ((m : ℝ) + 1)
      = (∑ m ∈ Finset.Icc (M + 1) N, sqfErr m * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)))
        + (squarefreeDensity * ((N : ℝ) / ((N : ℝ) + 1))
          - squarefreeDensity * ((M : ℝ) / ((M : ℝ) + 1)))
        + (sqfErr N / ((N : ℝ) + 1) - sqfErr M / ((M : ℝ) + 1)) := by ring
  rw [hrw]
  refine le_trans (abs_add_three _ _ _) ?_
  have habs3 : |sqfErr N / ((N : ℝ) + 1) - sqfErr M / ((M : ℝ) + 1)|
      ≤ |sqfErr N / ((N : ℝ) + 1)| + |sqfErr M / ((M : ℝ) + 1)| :=
    abs_sub _ _
  have hsum : (3 * (2 * Real.sqrt N + 1) + squarefreeDensity) / ((M : ℝ) + 1)
      = (2 * Real.sqrt N + 1) / ((M : ℝ) + 1) + squarefreeDensity / ((M : ℝ) + 1)
        + ((2 * Real.sqrt N + 1) / ((M : ℝ) + 1) + (2 * Real.sqrt N + 1) / ((M : ℝ) + 1)) := by
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

/-- **The logarithmic mean of the squarefree indicator over a dyadic block.** -/
theorem tendsto_squarefree_block_log_mean :
    Tendsto (fun u : ℝ => ∑ a ∈ Finset.Icc ⌈u⌉₊ ⌊2 * u⌋₊, ((moebius a : ℤ) : ℝ) ^ 2 / (a : ℝ))
      atTop (𝓝 (squarefreeDensity * Real.log 2)) := by
  have hD := squarefreeDensity_nonneg'
  have hmainlim : Tendsto
      (fun u : ℝ => squarefreeDensity * ∑ m ∈ Finset.Icc ⌈u⌉₊ ⌊2 * u⌋₊, 1 / ((m : ℝ) + 1))
      atTop (𝓝 (squarefreeDensity * Real.log 2)) :=
    tendsto_sum_block_one_div_succ.const_mul squarefreeDensity
  -- the majorant of the error
  have hsqrtinv : Tendsto (fun u : ℝ => 1 / Real.sqrt u) atTop (𝓝 0) :=
    tendsto_one_div_atTop.comp Real.tendsto_sqrt_atTop
  have hmaj : Tendsto
      (fun u : ℝ => 6 * Real.sqrt 2 * (1 / Real.sqrt u) + (3 + squarefreeDensity) * (1 / u))
      atTop (𝓝 0) := by
    have h1 := hsqrtinv.const_mul (6 * Real.sqrt 2)
    have h2 := tendsto_one_div_atTop.const_mul (3 + squarefreeDensity)
    have := h1.add h2
    simpa using this
  have hdiff : Tendsto
      (fun u : ℝ => (∑ a ∈ Finset.Icc ⌈u⌉₊ ⌊2 * u⌋₊, ((moebius a : ℤ) : ℝ) ^ 2 / (a : ℝ))
        - squarefreeDensity * ∑ m ∈ Finset.Icc ⌈u⌉₊ ⌊2 * u⌋₊, 1 / ((m : ℝ) + 1))
      atTop (𝓝 0) := by
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
    have hsplit := sum_Icc_one_split (M := M) (N := N) hMN
      (fun m => ((moebius m : ℤ) : ℝ) ^ 2 / (m : ℝ))
    have hsplit2 := sum_Icc_one_split (M := M) (N := N) hMN (fun m => 1 / ((m : ℝ) + 1))
    have hbase := abs_squarefreeLogSum_sub_le hM hMN
    rw [hM1] at hbase hsplit hsplit2
    have hval : (∑ a ∈ Finset.Icc ⌈u⌉₊ N, ((moebius a : ℤ) : ℝ) ^ 2 / (a : ℝ))
        - squarefreeDensity * ∑ m ∈ Finset.Icc ⌈u⌉₊ N, 1 / ((m : ℝ) + 1)
        = squarefreeLogSum N - squarefreeLogSum M
          - squarefreeDensity * ∑ m ∈ Finset.Icc ⌈u⌉₊ N, 1 / ((m : ℝ) + 1) := by
      rw [squarefreeLogSum, squarefreeLogSum, hsplit]
      ring
    rw [Real.norm_eq_abs, hval]
    refine le_trans hbase ?_
    -- the error is below the majorant
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
    have hnum : 3 * (2 * Real.sqrt N + 1) + squarefreeDensity
        ≤ 6 * (Real.sqrt 2 * Real.sqrt u) + (3 + squarefreeDensity) := by linarith
    have hstep : (3 * (2 * Real.sqrt N + 1) + squarefreeDensity) / ((M : ℝ) + 1)
        ≤ (6 * (Real.sqrt 2 * Real.sqrt u) + (3 + squarefreeDensity)) / u := by
      have hu' : u ≤ (M : ℝ) + 1 := by rw [hMR]; exact hcelow
      have hnn : (0 : ℝ) ≤ 6 * (Real.sqrt 2 * Real.sqrt u) + (3 + squarefreeDensity) := by
        have : (0 : ℝ) ≤ Real.sqrt 2 * Real.sqrt u := by positivity
        linarith
      calc (3 * (2 * Real.sqrt N + 1) + squarefreeDensity) / ((M : ℝ) + 1)
          ≤ (6 * (Real.sqrt 2 * Real.sqrt u) + (3 + squarefreeDensity)) / ((M : ℝ) + 1) :=
            div_le_div_of_nonneg_right hnum hden.le
        _ ≤ (6 * (Real.sqrt 2 * Real.sqrt u) + (3 + squarefreeDensity)) / u :=
            div_le_div_of_nonneg_left hnn hu0 hu'
    refine le_trans hstep (le_of_eq ?_)
    have hsu : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.2 hu0
    have husq : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu0.le
    have hinv : Real.sqrt u / u = 1 / Real.sqrt u := by
      rw [div_eq_div_iff (ne_of_gt hu0) (ne_of_gt hsu), one_mul]
      exact husq
    have hexp : (6 * (Real.sqrt 2 * Real.sqrt u) + (3 + squarefreeDensity)) / u
        = 6 * Real.sqrt 2 * (Real.sqrt u / u) + (3 + squarefreeDensity) * (1 / u) := by ring
    rw [hexp, hinv]
  have hres := hdiff.add hmainlim
  rw [zero_add] at hres
  refine hres.congr fun u => ?_
  ring

end RHTower.Sieve
