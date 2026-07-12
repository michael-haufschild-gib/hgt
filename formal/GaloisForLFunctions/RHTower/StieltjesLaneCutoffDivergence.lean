import GaloisForLFunctions.RHTower.PrimeBarycentricCoefficientDivergence

/-!
# Cutoff divergence of the two lanes of the first Stieltjes constant

The per-prime lane of the first generalized Stieltjes constant splits into a `γ`-coefficient
`log p/(p-1)` and a prime-log coefficient `p·(log p)²/(p-1)²`.  This module proves two
unconditional cutoff facts:

* the `γ`-lane cutoff `B(x) = Σ_{p ≤ x} log p/(p-1)` tends to infinity, and
* the log-lane cutoff `C(x) = Σ_{p ≤ x} p·(log p)²/(p-1)²` escapes every affine expression
  `r·B(x) + s` in the `γ`-lane cutoff.

Consequently the first Stieltjes constant admits no splitting into a finite `γ`-multiple plus a
finite prime-log combination obtained as ordinary cutoff limits: both lane coefficients diverge,
and their divergence orders are separated — no affine renormalization by the `γ`-lane absorbs the
log lane.  The finite Stieltjes value is created by the joint regularization of the two lanes.
-/

namespace RHTower

open Filter Finset
open scoped BigOperators

noncomputable section

/-- Reciprocal prime mass of the window `(1, x]`. -/
def primeReciprocalWindowSum (x : ℝ) : ℝ :=
  ∑ p ∈ windowPrimes 1 x, 1 / (p : ℝ)

/-- The window prime reciprocal sum inherits the divergence of the prime harmonic series. -/
theorem tendsto_primeReciprocalWindowSum_atTop :
    Tendsto primeReciprocalWindowSum atTop atTop := by
  classical
  have hnn : ∀ n : ℕ, 0 ≤ ({p | Nat.Prime p}.indicator (fun k : ℕ => 1 / (k : ℝ))) n := by
    intro n
    by_cases h : n ∈ {p | Nat.Prime p}
    · rw [Set.indicator_of_mem h]
      positivity
    · rw [Set.indicator_of_notMem h]
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg hnn).mp
    not_summable_one_div_on_primes
  rw [tendsto_atTop_atTop]
  intro M
  obtain ⟨n, hn⟩ := (Filter.tendsto_atTop.mp hdiv M).exists
  refine ⟨(n : ℝ), fun x hx => ?_⟩
  have hx0 : (0 : ℝ) ≤ x := le_trans (Nat.cast_nonneg n) hx
  calc M ≤ ∑ i ∈ Finset.range n,
        ({p | Nat.Prime p}.indicator (fun k : ℕ => 1 / (k : ℝ))) i := hn
    _ = ∑ i ∈ (Finset.range n).filter (fun i => i ∈ {p | Nat.Prime p}), 1 / (i : ℝ) :=
        Finset.sum_indicator_eq_sum_filter _ _ _ _
    _ ≤ primeReciprocalWindowSum x := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rw [Finset.mem_filter, Finset.mem_range] at hp
          obtain ⟨hpn, hpprime⟩ := hp
          rw [mem_windowPrimes (by norm_num) hx0]
          refine ⟨hpprime, by exact_mod_cast hpprime.one_lt, ?_⟩
          calc (p : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpn.le
            _ ≤ x := hx
        · intro p _ _
          positivity

/-- `γ`-lane prime cutoff coefficient of the first Stieltjes constant. -/
def stieltjesGammaLaneCutoff (x : ℝ) : ℝ :=
  ∑ p ∈ windowPrimes 1 x, Real.log p / ((p : ℝ) - 1)

/-- Prime-log-lane cutoff coefficient of the first Stieltjes constant. -/
def stieltjesLogLaneCutoff (x : ℝ) : ℝ :=
  ∑ p ∈ windowPrimes 1 x, (p : ℝ) * Real.log p ^ 2 / ((p : ℝ) - 1) ^ 2

/-- Each `γ`-lane term dominates a fixed multiple of the reciprocal prime. -/
theorem gammaLane_term_ge {p : ℕ} (hp : Nat.Prime p) :
    Real.log 2 * (1 / (p : ℝ)) ≤ Real.log p / ((p : ℝ) - 1) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hden : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hlog : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
  have hlogp0 : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by linarith)
  rw [mul_one_div, div_le_div_iff₀ hp0 hden]
  have h1 : Real.log 2 * ((p : ℝ) - 1) ≤ Real.log p * ((p : ℝ) - 1) :=
    mul_le_mul_of_nonneg_right hlog hden.le
  have h2 : Real.log p * ((p : ℝ) - 1) ≤ Real.log p * (p : ℝ) :=
    mul_le_mul_of_nonneg_left (by linarith) hlogp0
  linarith

/-- Every `γ`-lane term is nonnegative. -/
theorem gammaLane_term_nonneg {p : ℕ} (hp : Nat.Prime p) :
    0 ≤ Real.log p / ((p : ℝ) - 1) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by linarith)
  have hden : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  positivity

/-- **The `γ`-lane cutoff diverges.**  The `γ`-coefficient of the naive two-lane splitting of the
first Stieltjes constant has no finite ordinary cutoff limit. -/
theorem tendsto_stieltjesGammaLaneCutoff_atTop :
    Tendsto stieltjesGammaLaneCutoff atTop atTop := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hmul := tendsto_primeReciprocalWindowSum_atTop.const_mul_atTop hlog2
  refine tendsto_atTop_mono' atTop ?_ hmul
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [primeReciprocalWindowSum, stieltjesGammaLaneCutoff, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hpprime, _, _⟩ := (mem_windowPrimes (by norm_num) hx).mp hp
  exact gammaLane_term_ge hpprime

/-- `γ`-lane tail over the window `(q, x]`. -/
def stieltjesGammaLaneTail (q : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ windowPrimes q x, Real.log p / ((p : ℝ) - 1)

/-- Log-lane tail over the window `(q, x]`. -/
def stieltjesLogLaneTail (q : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ windowPrimes q x, (p : ℝ) * Real.log p ^ 2 / ((p : ℝ) - 1) ^ 2

theorem stieltjesGammaLaneCutoff_eq_head_add_tail (q : ℕ) (hq : 1 ≤ q)
    {x : ℝ} (hx : (q : ℝ) ≤ x) :
    stieltjesGammaLaneCutoff x =
      stieltjesGammaLaneCutoff q + stieltjesGammaLaneTail q x := by
  have hx0 : 0 ≤ x := le_trans (by exact_mod_cast Nat.zero_le q) hx
  rw [stieltjesGammaLaneCutoff, stieltjesGammaLaneCutoff, stieltjesGammaLaneTail,
    windowPrimes_one_union_tail q hq hx,
    Finset.sum_union (windowPrimes_one_disjoint_tail q hx0)]

theorem stieltjesLogLaneCutoff_eq_head_add_tail (q : ℕ) (hq : 1 ≤ q)
    {x : ℝ} (hx : (q : ℝ) ≤ x) :
    stieltjesLogLaneCutoff x =
      stieltjesLogLaneCutoff q + stieltjesLogLaneTail q x := by
  have hx0 : 0 ≤ x := le_trans (by exact_mod_cast Nat.zero_le q) hx
  rw [stieltjesLogLaneCutoff, stieltjesLogLaneCutoff, stieltjesLogLaneTail,
    windowPrimes_one_union_tail q hq hx,
    Finset.sum_union (windowPrimes_one_disjoint_tail q hx0)]

/-- The `γ`-lane tail beyond any fixed threshold still diverges. -/
theorem tendsto_stieltjesGammaLaneTail_atTop (q : ℕ) (hq : 1 ≤ q) :
    Tendsto (stieltjesGammaLaneTail q) atTop atTop := by
  have hdiff := tendsto_atTop_add_const_right atTop
    (-stieltjesGammaLaneCutoff q) tendsto_stieltjesGammaLaneCutoff_atTop
  apply hdiff.congr'
  filter_upwards [eventually_ge_atTop (q : ℝ)] with x hx
  rw [stieltjesGammaLaneCutoff_eq_head_add_tail q hq hx]
  ring

/-- Beyond a threshold, each log-lane term dominates the `log`-threshold-weighted `γ`-lane
term. -/
theorem logLane_term_ge_weighted_gammaLane {q p : ℕ} (hq : 1 < q) (hqp : (q : ℝ) < p)
    (hp : Nat.Prime p) :
    Real.log q * (Real.log p / ((p : ℝ) - 1)) ≤
      (p : ℝ) * Real.log p ^ 2 / ((p : ℝ) - 1) ^ 2 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hden : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hq
  have hlogq : Real.log q ≤ Real.log p := Real.log_le_log hq0 hqp.le
  have hlogp0 : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by linarith)
  have h1 : Real.log q * Real.log p * ((p : ℝ) - 1) ≤
      Real.log p * Real.log p * ((p : ℝ) - 1) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlogq hlogp0) hden.le
  rw [mul_div_assoc', div_le_div_iff₀ hden (by positivity)]
  calc Real.log q * Real.log p * ((p : ℝ) - 1) ^ 2
      = (Real.log q * Real.log p * ((p : ℝ) - 1)) * ((p : ℝ) - 1) := by ring
    _ ≤ (Real.log p * Real.log p * ((p : ℝ) - 1)) * ((p : ℝ) - 1) :=
        mul_le_mul_of_nonneg_right h1 hden.le
    _ = (Real.log p ^ 2 * ((p : ℝ) - 1)) * ((p : ℝ) - 1) := by ring
    _ ≤ (Real.log p ^ 2 * ((p : ℝ) - 1)) * (p : ℝ) :=
        mul_le_mul_of_nonneg_left (by linarith)
          (mul_nonneg (sq_nonneg _) hden.le)
    _ = (p : ℝ) * Real.log p ^ 2 * ((p : ℝ) - 1) := by ring

/-- **Affine escape of the log lane.**  For every pair of real weights, the log-lane cutoff
escapes the affine expression `r·B(x) + s` in the `γ`-lane cutoff: the two divergent lane
coefficients have separated orders, so no finite affine renormalization by the `γ`-lane absorbs
the prime-log lane. -/
theorem tendsto_stieltjesLogLane_sub_affineGammaLane_atTop (r s : ℝ) :
    Tendsto (fun x => stieltjesLogLaneCutoff x -
      (r * stieltjesGammaLaneCutoff x + s)) atTop atTop := by
  obtain ⟨q, hq_ge, hq_prime⟩ := Nat.exists_infinite_primes (max 2 ⌈Real.exp (r + 1)⌉₊)
  have hq2 : 2 ≤ q := le_trans (le_max_left _ _) hq_ge
  have hq1 : 1 < q := hq2
  have hlogq : r + 1 ≤ Real.log q := by
    have h1 : Real.exp (r + 1) ≤ (⌈Real.exp (r + 1)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈Real.exp (r + 1)⌉₊ : ℕ) : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast le_trans (le_max_right _ _) hq_ge
    calc r + 1 = Real.log (Real.exp (r + 1)) := (Real.log_exp (r + 1)).symm
      _ ≤ Real.log q := Real.log_le_log (Real.exp_pos (r + 1)) (le_trans h1 h2)
  have hconst := tendsto_atTop_add_const_left atTop
    (stieltjesLogLaneCutoff q - (r * stieltjesGammaLaneCutoff q + s))
    (tendsto_stieltjesGammaLaneTail_atTop q (by omega))
  refine tendsto_atTop_mono' atTop ?_ hconst
  filter_upwards [eventually_ge_atTop (q : ℝ)] with x hx
  have hx0 : 0 ≤ x := le_trans (by exact_mod_cast Nat.zero_le q) hx
  rw [stieltjesLogLaneCutoff_eq_head_add_tail q (by omega) hx,
    stieltjesGammaLaneCutoff_eq_head_add_tail q (by omega) hx]
  have htail : stieltjesGammaLaneTail q x + r * stieltjesGammaLaneTail q x ≤
      stieltjesLogLaneTail q x := by
    rw [stieltjesGammaLaneTail, stieltjesLogLaneTail, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hpprime, hqp, _⟩ := (mem_windowPrimes
      (by exact_mod_cast Nat.zero_le q : (0 : ℝ) ≤ (q : ℝ)) hx0).mp hp
    have hbase := logLane_term_ge_weighted_gammaLane hq1 hqp hpprime
    have hterm0 := gammaLane_term_nonneg hpprime
    have hweight : (1 + r) * (Real.log p / ((p : ℝ) - 1)) ≤
        Real.log q * (Real.log p / ((p : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_right (by linarith) hterm0
    calc Real.log p / ((p : ℝ) - 1) + r * (Real.log p / ((p : ℝ) - 1))
        = (1 + r) * (Real.log p / ((p : ℝ) - 1)) := by ring
      _ ≤ Real.log q * (Real.log p / ((p : ℝ) - 1)) := hweight
      _ ≤ (p : ℝ) * Real.log p ^ 2 / ((p : ℝ) - 1) ^ 2 := hbase
  linarith [htail]

end

end RHTower
