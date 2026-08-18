import GaloisForLFunctions.HTGeometry.EulerBinaryProduct

/-!
# The exact dyadic Fisher decomposition

`prime-valuation-dyadic-fermion-normal-cone-law`, equation `(20)`.

The Hellinger/Fisher curvature of a geometric law splits exactly over its independent binary
digits: the geometric variance `q/(1-q)²` is the sum of the digit variances
`4^j q^{2^j}/(1+q^{2^j})²`.  The identity is a telescoping consequence of

`r/(1-r)² = r/(1+r)² + 4 r²/(1-r²)²`,

which is `(1+r)² - (1-r)² = 4r` after clearing denominators.  The `j = 0` term is the squarefree
(parity) Fisher capacity `q/(1+q)²`; every `j ≥ 1` term is summable over the ordinary primes.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology
open scoped BigOperators

/-- The one-step split of the dyadic variance. -/
theorem dyadicVariance_step {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    r / (1 - r) ^ 2 = r / (1 + r) ^ 2 + 4 * r ^ 2 / (1 - r ^ 2) ^ 2 := by
  have h1 : (1 : ℝ) - r ≠ 0 := by linarith
  have h2 : (1 : ℝ) + r ≠ 0 := by linarith
  have h3 : (1 : ℝ) - r ^ 2 ≠ 0 := by
    have : (1 : ℝ) - r ^ 2 = (1 - r) * (1 + r) := by ring
    rw [this]
    exact mul_ne_zero h1 h2
  field_simp
  ring

/-- The partial sums of the dyadic Fisher series, with the exact remainder. -/
theorem dyadicFisher_sum_range {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (J : ℕ) :
    ∑ j ∈ Finset.range J, 4 ^ j * q ^ 2 ^ j / (1 + q ^ 2 ^ j) ^ 2
      = q / (1 - q) ^ 2 - 4 ^ J * q ^ 2 ^ J / (1 - q ^ 2 ^ J) ^ 2 := by
  induction J with
  | zero => simp
  | succ J ih =>
      have hr0 : (0 : ℝ) ≤ q ^ 2 ^ J := pow_nonneg hq0 _
      have hr1 : q ^ 2 ^ J < 1 := pow_lt_one₀ hq0 hq1 (Nat.two_pow_pos J).ne'
      have hstep := dyadicVariance_step hr0 hr1
      have hsq : q ^ 2 ^ (J + 1) = (q ^ 2 ^ J) ^ 2 := by
        rw [← pow_mul, ← pow_succ]
      rw [Finset.sum_range_succ, ih, hsq, pow_succ (4 : ℝ) J]
      have hfour : (4 : ℝ) ^ J * (q ^ 2 ^ J) / (1 - q ^ 2 ^ J) ^ 2
          = 4 ^ J * (q ^ 2 ^ J / (1 + q ^ 2 ^ J) ^ 2)
            + 4 ^ J * 4 * ((q ^ 2 ^ J) ^ 2 / (1 - (q ^ 2 ^ J) ^ 2) ^ 2) := by
        rw [mul_div_assoc, hstep]
        ring
      rw [hfour]
      ring

/-- The doubly exponential majorant is summable. -/
theorem summable_dyadicMajorant {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun j : ℕ => (4 : ℝ) ^ j * q ^ 2 ^ j) := by
  have hpow : Tendsto (fun j : ℕ => q ^ 2 ^ j) atTop (nhds 0) := by
    have h1 : Tendsto (fun j : ℕ => (2 : ℕ) ^ j) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt one_lt_two
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp h1
  have hsmall : ∀ᶠ j : ℕ in atTop, q ^ 2 ^ j ≤ 1 / 8 :=
    hpow.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 8))
  refine summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num) ?_
  filter_upwards [hsmall] with j hj
  have hnn : ∀ k : ℕ, (0 : ℝ) ≤ (4 : ℝ) ^ k * q ^ 2 ^ k := fun k => by positivity
  rw [Real.norm_of_nonneg (hnn (j + 1)), Real.norm_of_nonneg (hnn j)]
  have hsq : q ^ 2 ^ (j + 1) = q ^ 2 ^ j * q ^ 2 ^ j := by
    rw [← pow_add]
    congr 1
    rw [pow_succ]
    ring
  rw [hsq, pow_succ (4 : ℝ) j]
  have hbase : (0 : ℝ) ≤ (4 : ℝ) ^ j := by positivity
  have hqj : (0 : ℝ) ≤ q ^ 2 ^ j := pow_nonneg hq0 _
  have hx : q ^ 2 ^ j * q ^ 2 ^ j ≤ 1 / 8 * q ^ 2 ^ j := mul_le_mul_of_nonneg_right hj hqj
  nlinarith [hbase, hx]

theorem tendsto_dyadicRemainder_zero {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (fun J : ℕ => (4 : ℝ) ^ J * q ^ 2 ^ J / (1 - q ^ 2 ^ J) ^ 2) atTop (nhds 0) := by
  have hnum : Tendsto (fun J : ℕ => (4 : ℝ) ^ J * q ^ 2 ^ J) atTop (nhds 0) :=
    (summable_dyadicMajorant hq0 hq1).tendsto_atTop_zero
  have hpow : Tendsto (fun j : ℕ => q ^ 2 ^ j) atTop (nhds 0) := by
    have h1 : Tendsto (fun j : ℕ => (2 : ℕ) ^ j) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt one_lt_two
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp h1
  have hden : Tendsto (fun J : ℕ => (1 - q ^ 2 ^ J) ^ 2) atTop (nhds 1) := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub hpow).pow 2
    simpa using h
  have h := hnum.div hden one_ne_zero
  simpa [Pi.div_def] using h

/-- **`(20)`: the exact dyadic Fisher decomposition.**  The geometric Fisher curvature is the sum
of the binary-digit curvatures, the `j = 0` term being the squarefree capacity. -/
theorem hasSum_dyadicFisher {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun j : ℕ => 4 ^ j * q ^ 2 ^ j / (1 + q ^ 2 ^ j) ^ 2) (q / (1 - q) ^ 2) := by
  have hsummable : Summable (fun j : ℕ => (4 : ℝ) ^ j * q ^ 2 ^ j / (1 + q ^ 2 ^ j) ^ 2) := by
    refine (summable_dyadicMajorant hq0 hq1).of_nonneg_of_le (fun j => by positivity) ?_
    intro j
    have hqj : (0 : ℝ) ≤ q ^ 2 ^ j := pow_nonneg hq0 _
    have hone : (1 : ℝ) ≤ (1 + q ^ 2 ^ j) ^ 2 := by nlinarith
    have hnum : (0 : ℝ) ≤ (4 : ℝ) ^ j * q ^ 2 ^ j := by positivity
    calc (4 : ℝ) ^ j * q ^ 2 ^ j / (1 + q ^ 2 ^ j) ^ 2
        ≤ (4 : ℝ) ^ j * q ^ 2 ^ j / 1 := by
          refine div_le_div_of_nonneg_left hnum (by norm_num) hone
      _ = (4 : ℝ) ^ j * q ^ 2 ^ j := by ring
  rw [hsummable.hasSum_iff_tendsto_nat]
  have hpartial : ∀ J : ℕ, ∑ j ∈ Finset.range J, (4 : ℝ) ^ j * q ^ 2 ^ j / (1 + q ^ 2 ^ j) ^ 2
      = q / (1 - q) ^ 2 - 4 ^ J * q ^ 2 ^ J / (1 - q ^ 2 ^ J) ^ 2 :=
    dyadicFisher_sum_range hq0 hq1
  have hlim := tendsto_const_nhds (x := q / (1 - q) ^ 2) (f := atTop (α := ℕ))
    |>.sub (tendsto_dyadicRemainder_zero hq0 hq1)
  rw [sub_zero] at hlim
  exact hlim.congr fun J => (hpartial J).symm

end GaloisForLFunctions.HTGeometry
