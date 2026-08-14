import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Row sums of the radial off-diagonal majorant

The radial Gram matrix of a fixed-mode prolate combination obeys an off-diagonal bound of the
shape `|G j k| ≤ B / (j * k * |j - k|)` for `j, k ≥ 2`, together with a first-row bound
`|G 1 k| ≤ B' / k ^ 2`.  Whether the von Mangoldt-weighted double sum of those bounds converges is
decided by one elementary quantity: the row sum

`R K = ∑_{j ≥ 1, j ≠ K} 1 / (j * |j - K|)`.

A Cauchy--Schwarz or arithmetic-geometric-mean estimate bounds `R K` by an absolute constant, and
that is not enough: the weighted assembly then meets the divergent series `∑ log K / K`.  The exact
partial fraction `1/(a b) = (1/(a+b)) (1/a + 1/b)` supplies the missing factor `1/K` and turns the
assembly into `∑ (log K) ^ 2 / K ^ 2`, which converges.

This module proves that row bound, in the exact split form

* below the diagonal, a finite sum evaluated exactly as `2 * H (K-1) / K`;
* above the diagonal, an infinite sum bounded by `H K / K` through the telescoped partial fraction;

where `H n = ∑_{i < n} 1 / (i + 1)`, and concludes `R K ≤ 3 * (1 + log K) / K`.

Nothing here refers to prolate functions, primes, or the Riemann hypothesis: this is the
combinatorial layer that decides convergence of the weighted radial charge.
-/

open Finset

namespace RHTower

noncomputable section

/-! ## The real harmonic sum -/

/-- `harmonicSum n = ∑_{i < n} 1 / (i + 1)`. -/
def harmonicSum (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1)

@[simp] theorem harmonicSum_zero : harmonicSum 0 = 0 := by simp [harmonicSum]

theorem harmonicSum_succ (n : ℕ) :
    harmonicSum (n + 1) = harmonicSum n + 1 / ((n : ℝ) + 1) := by
  simp [harmonicSum, Finset.sum_range_succ]

theorem harmonicSum_nonneg (n : ℕ) : 0 ≤ harmonicSum n := by
  apply Finset.sum_nonneg
  intro i _
  positivity

theorem harmonicSum_mono {m n : ℕ} (h : m ≤ n) : harmonicSum m ≤ harmonicSum n := by
  have hsub : Finset.range m ⊆ Finset.range n := fun x hx =>
    Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) h)
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro i _ _
  positivity

/-- Splitting the harmonic sum: `H (m + n) = H m + ∑_{i < n} 1/(m + i + 1)`. -/
theorem harmonicSum_add (m n : ℕ) :
    harmonicSum (m + n) = harmonicSum m + ∑ i ∈ Finset.range n, 1 / (((m : ℝ) + (i : ℝ)) + 1) := by
  unfold harmonicSum
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring_nf

/-- One step of the standard logarithmic comparison: `1/(i+2) ≤ log (i+2) - log (i+1)`. -/
theorem one_div_succ_le_log_sub (i : ℕ) :
    1 / ((i : ℝ) + 1 + 1) ≤ Real.log ((i : ℝ) + 1 + 1) - Real.log ((i : ℝ) + 1) := by
  have h1 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (i : ℝ) + 1 + 1 := by positivity
  have hx : (0 : ℝ) < ((i : ℝ) + 1) / ((i : ℝ) + 1 + 1) := by positivity
  have hlog := Real.log_le_sub_one_of_pos hx
  rw [Real.log_div (by positivity) (by positivity)] at hlog
  have hsub : ((i : ℝ) + 1) / ((i : ℝ) + 1 + 1) - 1 = -(1 / ((i : ℝ) + 1 + 1)) := by
    field_simp
    ring
  rw [hsub] at hlog
  linarith

/-- The harmonic sum is at most `1 + log n` for `n ≥ 1`. -/
theorem harmonicSum_le_one_add_log {n : ℕ} (hn : 1 ≤ n) :
    harmonicSum n ≤ 1 + Real.log n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hstep : ∑ i ∈ Finset.range m, 1 / (((i : ℝ) + 1) + 1) ≤ Real.log ((m : ℝ) + 1) := by
    have hle : ∀ i ∈ Finset.range m,
        1 / (((i : ℝ) + 1) + 1) ≤ Real.log ((i : ℝ) + 1 + 1) - Real.log ((i : ℝ) + 1) := by
      intro i _
      exact one_div_succ_le_log_sub i
    calc
      ∑ i ∈ Finset.range m, 1 / (((i : ℝ) + 1) + 1)
          ≤ ∑ i ∈ Finset.range m,
              (Real.log ((i : ℝ) + 1 + 1) - Real.log ((i : ℝ) + 1)) :=
            Finset.sum_le_sum hle
      _ = Real.log ((m : ℝ) + 1) - Real.log ((0 : ℝ) + 1) := by
            have := Finset.sum_range_sub (fun i : ℕ => Real.log ((i : ℝ) + 1)) m
            simpa using this
      _ = Real.log ((m : ℝ) + 1) := by simp
  have hsplit : harmonicSum (m + 1) = 1 + ∑ i ∈ Finset.range m, 1 / (((i : ℝ) + 1) + 1) := by
    have := harmonicSum_add 1 m
    rw [add_comm 1 m] at this
    rw [this]
    have h1 : harmonicSum 1 = 1 := by simp [harmonicSum]
    rw [h1]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring_nf
  rw [hsplit]
  have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  linarith

/-! ## The below-diagonal row sum -/

/-- The below-diagonal summand `1 / (j (K - j))` written with `j = i + 1`. -/
def belowDiagTerm (K : ℕ) (i : ℕ) : ℝ := 1 / (((i : ℝ) + 1) * ((K : ℝ) - (i : ℝ) - 1))

/-- Exact partial fraction below the diagonal. -/
theorem belowDiagTerm_eq {K i : ℕ} (hi : i + 1 < K) :
    belowDiagTerm K i =
      (1 / (K : ℝ)) * (1 / ((i : ℝ) + 1) + 1 / ((K : ℝ) - (i : ℝ) - 1)) := by
  have hK : (0 : ℝ) < (K : ℝ) := by
    have : 0 < K := by omega
    exact_mod_cast this
  have ha : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hb : (0 : ℝ) < (K : ℝ) - (i : ℝ) - 1 := by
    have : (i : ℝ) + 1 < (K : ℝ) := by exact_mod_cast hi
    linarith
  unfold belowDiagTerm
  field_simp
  ring

/-- The below-diagonal row sum equals `2 * H (K - 1) / K`. -/
theorem sum_belowDiagTerm {K : ℕ} (hK : 2 ≤ K) :
    ∑ i ∈ Finset.range (K - 1), belowDiagTerm K i
      = 2 * harmonicSum (K - 1) / (K : ℝ) := by
  have hK0 : (0 : ℝ) < (K : ℝ) := by
    have : 0 < K := by omega
    exact_mod_cast this
  have hrewrite : ∀ i ∈ Finset.range (K - 1),
      belowDiagTerm K i
        = (1 / (K : ℝ)) * (1 / ((i : ℝ) + 1) + 1 / ((K : ℝ) - (i : ℝ) - 1)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    exact belowDiagTerm_eq (by omega)
  rw [Finset.sum_congr rfl hrewrite, ← Finset.mul_sum, Finset.sum_add_distrib]
  have hrefl :
      ∑ i ∈ Finset.range (K - 1), 1 / ((K : ℝ) - (i : ℝ) - 1)
        = ∑ i ∈ Finset.range (K - 1), 1 / ((i : ℝ) + 1) := by
    have h := Finset.sum_range_reflect (fun i : ℕ => 1 / ((i : ℝ) + 1)) (K - 1)
    rw [← h]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    congr 1
    have hle2 : 2 + i ≤ K := by omega
    have hcast : ((K - 1 - 1 - i : ℕ) : ℝ) = (K : ℝ) - (i : ℝ) - 2 := by
      have hnat : (K - 1 - 1 - i : ℕ) = K - (2 + i) := by omega
      rw [hnat, Nat.cast_sub hle2]
      push_cast
      ring
    rw [hcast]
    ring
  rw [hrefl]
  have : ∑ i ∈ Finset.range (K - 1), 1 / ((i : ℝ) + 1) = harmonicSum (K - 1) := rfl
  rw [this]
  field_simp
  ring

/-! ## The above-diagonal row sum -/

/-- The above-diagonal summand `1 / (j (j - K))` written with `j = K + i + 1`. -/
def aboveDiagTerm (K : ℕ) (i : ℕ) : ℝ := 1 / (((i : ℝ) + 1) * ((i : ℝ) + 1 + (K : ℝ)))

theorem aboveDiagTerm_nonneg (K i : ℕ) : 0 ≤ aboveDiagTerm K i := by
  unfold aboveDiagTerm
  positivity

/-- Exact partial fraction above the diagonal. -/
theorem aboveDiagTerm_eq {K : ℕ} (hK : 1 ≤ K) (i : ℕ) :
    aboveDiagTerm K i
      = (1 / (K : ℝ)) * (1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 1 + (K : ℝ))) := by
  have hK0 : (0 : ℝ) < (K : ℝ) := by
    have : 0 < K := by omega
    exact_mod_cast this
  have ha : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hb : (0 : ℝ) < (i : ℝ) + 1 + (K : ℝ) := by positivity
  unfold aboveDiagTerm
  field_simp
  ring

/-- Every partial sum above the diagonal is at most `H K / K`. -/
theorem sum_range_aboveDiagTerm_le {K : ℕ} (hK : 1 ≤ K) (N : ℕ) :
    ∑ i ∈ Finset.range N, aboveDiagTerm K i ≤ harmonicSum K / (K : ℝ) := by
  have hK0 : (0 : ℝ) < (K : ℝ) := by
    have : 0 < K := by omega
    exact_mod_cast this
  have hrewrite : ∀ i ∈ Finset.range N,
      aboveDiagTerm K i
        = (1 / (K : ℝ)) * (1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 1 + (K : ℝ))) := by
    intro i _
    exact aboveDiagTerm_eq hK i
  rw [Finset.sum_congr rfl hrewrite, ← Finset.mul_sum, Finset.sum_sub_distrib]
  have hfirst : ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1) = harmonicSum N := rfl
  have hsecond :
      ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1 + (K : ℝ))
        = harmonicSum (K + N) - harmonicSum K := by
    have h := harmonicSum_add K N
    have : ∑ i ∈ Finset.range N, 1 / (((K : ℝ) + (i : ℝ)) + 1)
        = ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1 + (K : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      ring
    rw [this] at h
    linarith
  rw [hfirst, hsecond]
  have hmono : harmonicSum N ≤ harmonicSum (K + N) := harmonicSum_mono (by omega)
  have hbound : harmonicSum N - (harmonicSum (K + N) - harmonicSum K) ≤ harmonicSum K := by
    linarith
  calc
    (1 / (K : ℝ)) * (harmonicSum N - (harmonicSum (K + N) - harmonicSum K))
        ≤ (1 / (K : ℝ)) * harmonicSum K := by
          apply mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = harmonicSum K / (K : ℝ) := by ring

/-- The above-diagonal row sum is at most `H K / K`. -/
theorem tsum_aboveDiagTerm_le {K : ℕ} (hK : 1 ≤ K) :
    ∑' i : ℕ, aboveDiagTerm K i ≤ harmonicSum K / (K : ℝ) :=
  Real.tsum_le_of_sum_range_le (fun i => aboveDiagTerm_nonneg K i)
    (fun N => sum_range_aboveDiagTerm_le hK N)

theorem summable_aboveDiagTerm {K : ℕ} (hK : 1 ≤ K) : Summable (aboveDiagTerm K) :=
  summable_of_sum_range_le (fun i => aboveDiagTerm_nonneg K i)
    (fun N => sum_range_aboveDiagTerm_le hK N)

/-! ## The full row bound -/

/-- The complete off-diagonal row sum of the radial majorant. -/
def radialRowSum (K : ℕ) : ℝ :=
  (∑ i ∈ Finset.range (K - 1), belowDiagTerm K i) + ∑' i : ℕ, aboveDiagTerm K i

/-- **Row bound.**  The exact partial fractions supply the factor `1 / K` that a
Cauchy--Schwarz estimate of the same row cannot see. -/
theorem radialRowSum_le {K : ℕ} (hK : 2 ≤ K) :
    radialRowSum K ≤ 3 * (1 + Real.log K) / (K : ℝ) := by
  have hK0 : (0 : ℝ) < (K : ℝ) := by
    have : 0 < K := by omega
    exact_mod_cast this
  have hK1 : (1 : ℕ) ≤ K := by omega
  have hbelow := sum_belowDiagTerm hK
  have habove := tsum_aboveDiagTerm_le hK1
  have hH1 : harmonicSum (K - 1) ≤ 1 + Real.log K := by
    refine le_trans (harmonicSum_mono (by omega : K - 1 ≤ K)) ?_
    exact harmonicSum_le_one_add_log hK1
  have hH2 : harmonicSum K ≤ 1 + Real.log K := harmonicSum_le_one_add_log hK1
  unfold radialRowSum
  rw [hbelow]
  have hstep : 2 * harmonicSum (K - 1) / (K : ℝ) + ∑' i : ℕ, aboveDiagTerm K i
      ≤ 2 * (1 + Real.log K) / (K : ℝ) + (1 + Real.log K) / (K : ℝ) := by
    have hA : 2 * harmonicSum (K - 1) / (K : ℝ) ≤ 2 * (1 + Real.log K) / (K : ℝ) := by
      gcongr
    have hB : ∑' i : ℕ, aboveDiagTerm K i ≤ (1 + Real.log K) / (K : ℝ) := by
      refine habove.trans ?_
      gcongr
    linarith
  refine hstep.trans ?_
  have hcollect : 2 * (1 + Real.log K) / (K : ℝ) + (1 + Real.log K) / (K : ℝ)
      = 3 * (1 + Real.log K) / (K : ℝ) := by ring
  linarith [hcollect]

/-! ## The divisor-weighted assembly

The von Mangoldt weight collapses, by `∑_{m ∣ K, m ≥ 2} Λ m = log K`, to a single factor
`log K` on each row.  Convergence of the weighted total is therefore exactly summability of
`log K * (1 + log K) / K ^ 2`, which the row bound produces.  This is the step at which a row
bound of size `O(1)` — all that Cauchy--Schwarz gives — would fail, since it leaves `∑ log K / K`.
-/

/-- Logarithm against a quarter power: `log x ≤ 4 * x ^ (1/4)` for `x ≥ 1`. -/
theorem log_le_four_mul_rpow_quarter {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ 4 * x ^ ((1 : ℝ) / 4) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hq : (0 : ℝ) < x ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hx0 _
  have hlog : Real.log (x ^ ((1 : ℝ) / 4)) ≤ x ^ ((1 : ℝ) / 4) - 1 :=
    Real.log_le_sub_one_of_pos hq
  rw [Real.log_rpow hx0] at hlog
  linarith

/-- Squared logarithm against a half power. -/
theorem log_sq_le_sixteen_mul_rpow_half {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ 2 ≤ 16 * x ^ ((1 : ℝ) / 2) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hlognn : 0 ≤ Real.log x := Real.log_nonneg hx
  have hL := log_le_four_mul_rpow_quarter hx
  have hsq : Real.log x ^ 2 ≤ (4 * x ^ ((1 : ℝ) / 4)) ^ 2 := by
    exact pow_le_pow_left₀ hlognn hL 2
  have hpow : (4 * x ^ ((1 : ℝ) / 4)) ^ 2 = 16 * x ^ ((1 : ℝ) / 2) := by
    rw [mul_pow, ← Real.rpow_natCast (x ^ ((1 : ℝ) / 4)) 2, ← Real.rpow_mul hx0.le]
    norm_num
  linarith [hsq, hpow.le, hpow.ge]

/-- The weighted row majorant, `log K (1 + log K) / K ^ 2`, is summable.
This is the exact convergence the divisor-weighted assembly needs, and the reason the
`1 / K` produced by the partial fractions is indispensable. -/
theorem summable_weighted_rowMajorant :
    Summable (fun n : ℕ =>
      Real.log ((n : ℝ) + 2) * (1 + Real.log ((n : ℝ) + 2)) / ((n : ℝ) + 2) ^ 2) := by
  have hdom : Summable (fun n : ℕ => (20 : ℝ) / ((n : ℝ) + 2) ^ ((3 : ℝ) / 2)) := by
    have hbase : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ ((3 : ℝ) / 2))) :=
      Real.summable_one_div_nat_rpow.2 (by norm_num)
    have hshift : Summable (fun n : ℕ => (1 : ℝ) / (((n + 2 : ℕ) : ℝ) ^ ((3 : ℝ) / 2))) :=
      (summable_nat_add_iff 2).2 hbase
    have hmul := hshift.mul_left (20 : ℝ)
    refine hmul.congr fun n => ?_
    have hcast : (((n + 2 : ℕ) : ℝ)) = (n : ℝ) + 2 := by push_cast; ring
    rw [hcast]
    ring
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hdom
  · have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hx : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith
    have hlog : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg hx
    positivity
  · have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hx : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith
    have hx0 : (0 : ℝ) < (n : ℝ) + 2 := by linarith
    have hlognn : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg hx
    have hL := log_le_four_mul_rpow_quarter hx
    have hlog2 := log_sq_le_sixteen_mul_rpow_half hx
    have hq1 : ((n : ℝ) + 2) ^ ((1 : ℝ) / 4) ≤ ((n : ℝ) + 2) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
    have hnum : Real.log ((n : ℝ) + 2) * (1 + Real.log ((n : ℝ) + 2))
        ≤ 20 * ((n : ℝ) + 2) ^ ((1 : ℝ) / 2) := by
      have hexpand : Real.log ((n : ℝ) + 2) * (1 + Real.log ((n : ℝ) + 2))
          = Real.log ((n : ℝ) + 2) + Real.log ((n : ℝ) + 2) ^ 2 := by ring
      rw [hexpand]
      linarith [hL, hlog2, hq1]
    have hden : (0 : ℝ) < ((n : ℝ) + 2) ^ 2 := by positivity
    have hsplit : ((n : ℝ) + 2) ^ 2
        = ((n : ℝ) + 2) ^ ((1 : ℝ) / 2) * ((n : ℝ) + 2) ^ ((3 : ℝ) / 2) := by
      rw [← Real.rpow_add hx0, ← Real.rpow_natCast ((n : ℝ) + 2) 2]
      norm_num
    have hp : (0 : ℝ) < ((n : ℝ) + 2) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hx0 _
    have hq : (0 : ℝ) < ((n : ℝ) + 2) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hx0 _
    calc
      Real.log ((n : ℝ) + 2) * (1 + Real.log ((n : ℝ) + 2)) / ((n : ℝ) + 2) ^ 2
          ≤ (20 * ((n : ℝ) + 2) ^ ((1 : ℝ) / 2)) / ((n : ℝ) + 2) ^ 2 := by
            gcongr
      _ = 20 / ((n : ℝ) + 2) ^ ((3 : ℝ) / 2) := by
            rw [hsplit]
            field_simp

/-! ## Row assembly against the abstract Gram bounds

`rowBound B B' K` is the majorant produced by the two analytic inputs on row `K`:
the first-row bound `B' / K ^ 2` and, for `j ≥ 2`, `B / (j K |j - K|)`.  The theorem below
converts the row bound into the shape the weighted assembly consumes. -/

/-- The row majorant assembled from an off-diagonal constant `B` and a first-row constant `B'`. -/
def rowBound (B B' : ℝ) (K : ℕ) : ℝ := B' / (K : ℝ) ^ 2 + B * radialRowSum K / (K : ℝ)

/-- **Row assembly.**  Both analytic inputs land on the same `1 / K ^ 2` scale, with the
off-diagonal block paying an extra `1 + log K`. -/
theorem rowBound_le {B B' : ℝ} (hB : 0 ≤ B) {K : ℕ} (hK : 2 ≤ K) :
    rowBound B B' K ≤ B' / (K : ℝ) ^ 2 + 3 * B * (1 + Real.log K) / (K : ℝ) ^ 2 := by
  have hK0 : (0 : ℝ) < (K : ℝ) := by
    have : 0 < K := by omega
    exact_mod_cast this
  have hrow := radialRowSum_le hK
  unfold rowBound
  have hmul : B * radialRowSum K ≤ B * (3 * (1 + Real.log K) / (K : ℝ)) :=
    mul_le_mul_of_nonneg_left hrow hB
  have hstep : B * radialRowSum K / (K : ℝ)
      ≤ 3 * B * (1 + Real.log K) / (K : ℝ) ^ 2 := by
    have h1 : B * radialRowSum K / (K : ℝ)
        ≤ B * (3 * (1 + Real.log K) / (K : ℝ)) / (K : ℝ) := by
      apply div_le_div_of_nonneg_right hmul hK0.le
    have h2 : B * (3 * (1 + Real.log K) / (K : ℝ)) / (K : ℝ)
        = 3 * B * (1 + Real.log K) / (K : ℝ) ^ 2 := by
      field_simp
    linarith
  linarith

/-- The assembled von Mangoldt-weighted row majorant is summable over all rows `K ≥ 2`. -/
theorem summable_weighted_rowBound (B B' : ℝ) (hB : 0 ≤ B) (hB' : 0 ≤ B') :
    Summable (fun n : ℕ =>
      Real.log ((n : ℝ) + 2) * (B' / ((n : ℝ) + 2) ^ 2 + 3 * B * (1 + Real.log ((n : ℝ) + 2)) / ((n : ℝ) + 2) ^ 2)) := by
  have hdom : Summable (fun n : ℕ =>
      (B' + 3 * B) * (Real.log ((n : ℝ) + 2) * (1 + Real.log ((n : ℝ) + 2)) / ((n : ℝ) + 2) ^ 2)) :=
    summable_weighted_rowMajorant.mul_left (B' + 3 * B)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hdom
  · have hx : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith [show (0 : ℝ) ≤ n by positivity]
    have hlog : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg hx
    have hterm1 : 0 ≤ B' / ((n : ℝ) + 2) ^ 2 := by positivity
    have hterm2 : 0 ≤ 3 * B * (1 + Real.log ((n : ℝ) + 2)) / ((n : ℝ) + 2) ^ 2 := by positivity
    exact mul_nonneg hlog (add_nonneg hterm1 hterm2)
  · have hx : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith [show (0 : ℝ) ≤ n by positivity]
    have hlog : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg hx
    have h1le : 1 ≤ 1 + Real.log ((n : ℝ) + 2) := by linarith
    have hB'le : Real.log ((n : ℝ) + 2) * (B' / ((n : ℝ) + 2) ^ 2)
        ≤ B' * (Real.log ((n : ℝ) + 2) * (1 + Real.log ((n : ℝ) + 2)) / ((n : ℝ) + 2) ^ 2) := by
      have : Real.log ((n : ℝ) + 2) * (B' / ((n : ℝ) + 2) ^ 2) =
          B' * (Real.log ((n : ℝ) + 2) / ((n : ℝ) + 2) ^ 2) := by ring
      rw [this]
      have hstep : Real.log ((n : ℝ) + 2) / ((n : ℝ) + 2) ^ 2
          ≤ Real.log ((n : ℝ) + 2) * (1 + Real.log ((n : ℝ) + 2)) / ((n : ℝ) + 2) ^ 2 := by
        rw [div_le_div_iff_of_pos_right (by positivity)]
        nlinarith
      exact mul_le_mul_of_nonneg_left hstep hB'
    have hBle : Real.log ((n : ℝ) + 2) * (3 * B * (1 + Real.log ((n : ℝ) + 2)) / ((n : ℝ) + 2) ^ 2)
        = (3 * B) * (Real.log ((n : ℝ) + 2) * (1 + Real.log ((n : ℝ) + 2)) / ((n : ℝ) + 2) ^ 2) := by
      ring
    calc
      Real.log ((n : ℝ) + 2) * (B' / ((n : ℝ) + 2) ^ 2 + 3 * B * (1 + Real.log ((n : ℝ) + 2)) / ((n : ℝ) + 2) ^ 2)
          = Real.log ((n : ℝ) + 2) * (B' / ((n : ℝ) + 2) ^ 2) +
            Real.log ((n : ℝ) + 2) * (3 * B * (1 + Real.log ((n : ℝ) + 2)) / ((n : ℝ) + 2) ^ 2) := by ring
      _ ≤ B' * (Real.log ((n : ℝ) + 2) * (1 + Real.log ((n : ℝ) + 2)) / ((n : ℝ) + 2) ^ 2) +
          (3 * B) * (Real.log ((n : ℝ) + 2) * (1 + Real.log ((n : ℝ) + 2)) / ((n : ℝ) + 2) ^ 2) := by linarith [hB'le, hBle]
      _ = (B' + 3 * B) * (Real.log ((n : ℝ) + 2) * (1 + Real.log ((n : ℝ) + 2)) / ((n : ℝ) + 2) ^ 2) := by ring

end

end RHTower

