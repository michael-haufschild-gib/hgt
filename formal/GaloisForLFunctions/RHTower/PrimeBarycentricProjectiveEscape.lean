import GaloisForLFunctions.RHTower.PrimeBarycentricCoefficientDivergence

/-!
# Projective escape of canonical prime barycentric packets

Individual exact barycentric coefficients diverge under canonical prime exhaustion.  A possible
repair would be to divide the whole packet by one support-dependent scalar.  This file rules out
that projective rescue.

For fixed labels `p<q`, appending a prime `r>q` multiplies the magnitude ratio of the
coefficients at `q` and `p` by

`((log r)^(2 : ℕ)-(log p)^(2 : ℕ)) / ((log r)^(2 : ℕ)-(log q)^(2 : ℕ))`.

This factor is larger than
`1 + ((log q)^(2 : ℕ)-(log p)^(2 : ℕ))/(log r)^(2 : ℕ)`.  The reciprocal squared-log prime sum already diverges,
so the product of relative factors diverges.  Consequently

`|a_q(x)| / |a_p(x)| → +∞`.

No common scalar normalization of the exact finite packets can retain finite nonzero local
coefficients at two fixed primes.  The finite interpolation flow therefore has neither an ordinary
coefficientwise limit nor a projective coefficientwise limit.
-/

namespace RHTower

open Filter Finset Set Topology
open scoped BigOperators Topology

noncomputable section

/-- Relative extension product for the coefficients at fixed labels `p<q`. -/
def primeBarycentricRelativeTailGrowth (p q : ℕ) (x : ℝ) : ℝ :=
  ∏ r ∈ windowPrimes q x,
    (Real.log r ^ (2 : ℕ) - Real.log p ^ (2 : ℕ)) /
      (Real.log r ^ (2 : ℕ) - Real.log q ^ (2 : ℕ))

theorem one_add_logSqDiff_mul_tailSum_le_primeBarycentricRelativeTailGrowth
    (p q : ℕ) (hp : 1 < p) (hpq : p < q) {x : ℝ} (hx : (q : ℝ) ≤ x) :
    1 + (Real.log q ^ (2 : ℕ) - Real.log p ^ (2 : ℕ)) *
        primeReciprocalLogSqTailSum q x ≤
      primeBarycentricRelativeTailGrowth p q x := by
  have hplog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp)
  have hqlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast lt_trans hp hpq)
  have hlogpq : Real.log p < Real.log q :=
    Real.strictMonoOn_log
      (by change (0 : ℝ) < p
          exact_mod_cast Nat.zero_lt_one.trans hp)
      (by change (0 : ℝ) < q
          exact_mod_cast Nat.zero_lt_one.trans (lt_trans hp hpq))
      (by exact_mod_cast hpq)
  have hdiff : 0 < Real.log q ^ (2 : ℕ) - Real.log p ^ (2 : ℕ) := by nlinarith
  let u : ℕ → ℝ := fun r =>
    (Real.log q ^ (2 : ℕ) - Real.log p ^ (2 : ℕ)) / Real.log r ^ (2 : ℕ)
  have hu : ∀ r ∈ windowPrimes q x, 0 ≤ u r := by
    intro r hr
    exact div_nonneg hdiff.le (sq_nonneg _)
  have hfirst := one_add_sum_le_prod_one_add (windowPrimes q x) u hu
  calc
    1 + (Real.log q ^ (2 : ℕ) - Real.log p ^ (2 : ℕ)) *
        primeReciprocalLogSqTailSum q x =
        1 + ∑ r ∈ windowPrimes q x, u r := by
      rw [primeReciprocalLogSqTailSum, Finset.mul_sum]
      simp [u, div_eq_mul_inv]
    _ ≤ ∏ r ∈ windowPrimes q x, (1 + u r) := hfirst
    _ ≤ ∏ r ∈ windowPrimes q x,
        (Real.log r ^ (2 : ℕ) - Real.log p ^ (2 : ℕ)) /
          (Real.log r ^ (2 : ℕ) - Real.log q ^ (2 : ℕ)) := by
      apply Finset.prod_le_prod
      · intro r hr
        linarith [hu r hr]
      · intro r hr
        obtain ⟨hrprime, hqr, hrx⟩ :=
          (mem_windowPrimes
            (by exact_mod_cast Nat.zero_le q : (0 : ℝ) ≤ (q : ℝ))
            (by linarith)).mp hr
        have hrlog : 0 < Real.log r :=
          Real.log_pos (lt_trans (by exact_mod_cast lt_trans hp hpq) hqr)
        have hlogqr : Real.log q < Real.log r :=
          Real.strictMonoOn_log
            (by change (0 : ℝ) < q
                exact_mod_cast Nat.zero_lt_one.trans (lt_trans hp hpq))
            (by change (0 : ℝ) < r
                exact_mod_cast hrprime.pos)
            hqr
        have hsq : Real.log q ^ (2 : ℕ) < Real.log r ^ (2 : ℕ) := by nlinarith
        have hden : 0 < Real.log r ^ (2 : ℕ) - Real.log q ^ (2 : ℕ) := sub_pos.mpr hsq
        have hcomp : u r ≤
            (Real.log q ^ (2 : ℕ) - Real.log p ^ (2 : ℕ)) /
              (Real.log r ^ (2 : ℕ) - Real.log q ^ (2 : ℕ)) := by
          dsimp [u]
          rw [div_le_div_iff₀ (sq_pos_of_pos hrlog) hden]
          nlinarith
        have hfactor :
            (Real.log r ^ (2 : ℕ) - Real.log p ^ (2 : ℕ)) /
                (Real.log r ^ (2 : ℕ) - Real.log q ^ (2 : ℕ)) =
              1 + (Real.log q ^ (2 : ℕ) - Real.log p ^ (2 : ℕ)) /
                (Real.log r ^ (2 : ℕ) - Real.log q ^ (2 : ℕ)) := by
          field_simp [hden.ne']
          ring
        rw [hfactor]
        linarith
    _ = primeBarycentricRelativeTailGrowth p q x := rfl

/-- Relative tail growth diverges for every fixed pair of labels `1<p<q`. -/
theorem tendsto_primeBarycentricRelativeTailGrowth_atTop
    (p q : ℕ) (hp : 1 < p) (hpq : p < q) :
    Tendsto (primeBarycentricRelativeTailGrowth p q) atTop atTop := by
  have hplog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp)
  have hqlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast lt_trans hp hpq)
  have hlogpq : Real.log p < Real.log q :=
    Real.strictMonoOn_log
      (by change (0 : ℝ) < p
          exact_mod_cast Nat.zero_lt_one.trans hp)
      (by change (0 : ℝ) < q
          exact_mod_cast Nat.zero_lt_one.trans (lt_trans hp hpq))
      (by exact_mod_cast hpq)
  have hc : 0 < Real.log q ^ (2 : ℕ) - Real.log p ^ (2 : ℕ) := by nlinarith
  have hmul := tendsto_const_nhds.pos_mul_atTop hc
    (tendsto_primeReciprocalLogSqTailSum_atTop q (by omega))
  have hadd := tendsto_atTop_add_const_left atTop (1 : ℝ) hmul
  refine tendsto_atTop_mono' atTop ?_ hadd
  filter_upwards [eventually_ge_atTop (q : ℝ)] with x hx
  exact one_add_logSqDiff_mul_tailSum_le_primeBarycentricRelativeTailGrowth
    p q hp hpq hx

/-- Growth of the coefficient at `p` contributed only by primes above a later split point `q`. -/
def primeBarycentricUpperGrowth (p q : ℕ) (x : ℝ) : ℝ :=
  ∏ r ∈ windowPrimes q x,
    Real.log r ^ (2 : ℕ) / (Real.log r ^ (2 : ℕ) - Real.log p ^ (2 : ℕ))

theorem primeBarycentricUpperGrowth_pos (p q : ℕ) (hp : 1 < p) (hpq : p ≤ q)
    {x : ℝ} (hx : (q : ℝ) ≤ x) :
    0 < primeBarycentricUpperGrowth p q x := by
  apply Finset.prod_pos
  intro r hr
  obtain ⟨hrprime, hqr, hrx⟩ :=
    (mem_windowPrimes
      (by exact_mod_cast Nat.zero_le q : (0 : ℝ) ≤ (q : ℝ))
      (by linarith)).mp hr
  have hpr : (p : ℝ) < r := lt_of_le_of_lt (by exact_mod_cast hpq) hqr
  have hplog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp)
  have hrlog : 0 < Real.log r :=
    Real.log_pos (lt_trans (by exact_mod_cast hp) hpr)
  have hlogpr : Real.log p < Real.log r :=
    Real.strictMonoOn_log
      (by change (0 : ℝ) < p
          exact_mod_cast Nat.zero_lt_one.trans hp)
      (by change (0 : ℝ) < r
          exact_mod_cast hrprime.pos)
      hpr
  exact div_pos (sq_pos_of_pos hrlog) (by nlinarith)

/-- Splitting the canonical support at `q` factors the coefficient magnitude at `p` into its value
at `q` and the upper-prime growth. -/
theorem primeBarycentricCoefficientMagnitude_eq_at_mul_upperGrowth
    (p : ℕ) (hp : p.Prime) (q : ℕ) (hpq : p ≤ q) {x : ℝ} (hx : (q : ℝ) ≤ x) :
    primeBarycentricCoefficientMagnitude p x =
      primeBarycentricCoefficientMagnitude p q *
        primeBarycentricUpperGrowth p q x := by
  have hx0 : 0 ≤ x := le_trans (by exact_mod_cast Nat.zero_le q) hx
  have hq1 : 1 ≤ q := le_trans hp.one_le hpq
  have hpnotTail : p ∉ windowPrimes q x := by
    intro hmem
    have h := (mem_windowPrimes
      (by exact_mod_cast Nat.zero_le q : (0 : ℝ) ≤ (q : ℝ)) hx0).mp hmem
    exact (not_lt_of_ge (by exact_mod_cast hpq : (p : ℝ) ≤ q)) h.2.1
  have herase : (windowPrimes 1 x).erase p =
      (windowPrimes 1 q).erase p ∪ windowPrimes q x := by
    rw [windowPrimes_one_union_tail q hq1 hx,
      Finset.erase_union_distrib, Finset.erase_eq_of_notMem hpnotTail]
  have hdisj : Disjoint ((windowPrimes 1 q).erase p) (windowPrimes q x) :=
    (windowPrimes_one_disjoint_tail q hx0).mono_left (Finset.erase_subset _ _)
  rw [primeBarycentricCoefficientMagnitude, primeBarycentricCoefficientMagnitude,
    primeBarycentricUpperGrowth, herase, Finset.prod_union hdisj]
  have htail :
      (∏ r ∈ windowPrimes q x,
          Real.log r ^ (2 : ℕ) / |Real.log p ^ (2 : ℕ) - Real.log r ^ (2 : ℕ)|) =
        ∏ r ∈ windowPrimes q x,
          Real.log r ^ (2 : ℕ) / (Real.log r ^ (2 : ℕ) - Real.log p ^ (2 : ℕ)) := by
    apply Finset.prod_congr rfl
    intro r hr
    obtain ⟨hrprime, hqr, hrx⟩ :=
      (mem_windowPrimes
        (by exact_mod_cast Nat.zero_le q : (0 : ℝ) ≤ (q : ℝ)) hx0).mp hr
    have hpr : (p : ℝ) < r := lt_of_le_of_lt (by exact_mod_cast hpq) hqr
    have hplog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
    have hrlog : 0 < Real.log r :=
      Real.log_pos (lt_trans (by exact_mod_cast hp.one_lt) hpr)
    have hlogpr : Real.log p < Real.log r :=
      Real.strictMonoOn_log
        (by change (0 : ℝ) < p
            exact_mod_cast hp.pos)
        (by change (0 : ℝ) < r
            exact_mod_cast hrprime.pos)
        hpr
    have hneg : Real.log p ^ (2 : ℕ) - Real.log r ^ (2 : ℕ) < 0 := by nlinarith
    rw [abs_of_neg hneg]
    ring_nf
  rw [htail]
  ring

theorem primeBarycentricUpperGrowth_div_eq_relativeTailGrowth
    (p q : ℕ) (hp : 1 < p) (hpq : p < q) {x : ℝ} (hx : (q : ℝ) ≤ x) :
    primeBarycentricUpperGrowth q q x /
        primeBarycentricUpperGrowth p q x =
      primeBarycentricRelativeTailGrowth p q x := by
  rw [primeBarycentricUpperGrowth, primeBarycentricUpperGrowth,
    primeBarycentricRelativeTailGrowth, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro r hr
  obtain ⟨hrprime, hqr, hrx⟩ :=
    (mem_windowPrimes
      (by exact_mod_cast Nat.zero_le q : (0 : ℝ) ≤ (q : ℝ))
      (by linarith)).mp hr
  have hpr : (p : ℝ) < r := lt_trans (by exact_mod_cast hpq) hqr
  have hrlog : 0 < Real.log r :=
    Real.log_pos (lt_trans (by exact_mod_cast hp) hpr)
  have hplog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp)
  have hqlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast lt_trans hp hpq)
  have hlogqr : Real.log q < Real.log r :=
    Real.strictMonoOn_log
      (by change (0 : ℝ) < q
          exact_mod_cast Nat.zero_lt_one.trans (lt_trans hp hpq))
      (by change (0 : ℝ) < r
          exact_mod_cast hrprime.pos)
      hqr
  have hlogpr : Real.log p < Real.log r :=
    Real.strictMonoOn_log
      (by change (0 : ℝ) < p
          exact_mod_cast Nat.zero_lt_one.trans hp)
      (by change (0 : ℝ) < r
          exact_mod_cast hrprime.pos)
      hpr
  have hdenq : Real.log r ^ (2 : ℕ) - Real.log q ^ (2 : ℕ) ≠ 0 := by nlinarith
  have hdenp : Real.log r ^ (2 : ℕ) - Real.log p ^ (2 : ℕ) ≠ 0 := by nlinarith
  have hr0 : Real.log r ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hrlog.ne'
  field_simp

/-- Ratio of canonical exact coefficient magnitudes at two fixed labels. -/
def primeBarycentricProjectiveRatio (p q : ℕ) (x : ℝ) : ℝ :=
  primeBarycentricCoefficientMagnitude q x /
    primeBarycentricCoefficientMagnitude p x

theorem primeBarycentricProjectiveRatio_eq_base_mul_relativeTail
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    {x : ℝ} (hx : (q : ℝ) ≤ x) :
    primeBarycentricProjectiveRatio p q x =
      primeBarycentricProjectiveRatio p q q *
        primeBarycentricRelativeTailGrowth p q x := by
  have hqx := primeBarycentricCoefficientMagnitude_eq_at_mul_upperGrowth
    q hq q le_rfl hx
  have hpx := primeBarycentricCoefficientMagnitude_eq_at_mul_upperGrowth
    p hp q hpq.le hx
  have hMq : 0 < primeBarycentricCoefficientMagnitude q q :=
    primeBarycentricCoefficientMagnitude_head_pos q hq
  have hMp : 0 < primeBarycentricCoefficientMagnitude p q := by
    rw [primeBarycentricCoefficientMagnitude_eq_at_mul_upperGrowth
      p hp p le_rfl (by exact_mod_cast hpq.le : (p : ℝ) ≤ q)]
    exact mul_pos (primeBarycentricCoefficientMagnitude_head_pos p hp)
      (primeBarycentricUpperGrowth_pos p p hp.one_lt le_rfl
        (by exact_mod_cast hpq.le : (p : ℝ) ≤ q))
  have hUp : 0 < primeBarycentricUpperGrowth p q x :=
    primeBarycentricUpperGrowth_pos p q hp.one_lt hpq.le hx
  rw [primeBarycentricProjectiveRatio, primeBarycentricProjectiveRatio, hqx, hpx]
  calc
    primeBarycentricCoefficientMagnitude q q * primeBarycentricUpperGrowth q q x /
        (primeBarycentricCoefficientMagnitude p q *
          primeBarycentricUpperGrowth p q x) =
        primeBarycentricCoefficientMagnitude q q /
          primeBarycentricCoefficientMagnitude p q *
            (primeBarycentricUpperGrowth q q x /
    primeBarycentricUpperGrowth p q x) := by
      field_simp [hMp.ne', hUp.ne']
    _ = primeBarycentricCoefficientMagnitude q q /
          primeBarycentricCoefficientMagnitude p q *
            primeBarycentricRelativeTailGrowth p q x := by
      rw [primeBarycentricUpperGrowth_div_eq_relativeTailGrowth
        p q hp.one_lt hpq hx]

/-- **Projective escape.** For fixed primes `p<q`, the ratio of their exact canonical coefficient
magnitudes tends to infinity. -/
theorem tendsto_primeBarycentricProjectiveRatio_atTop
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    Tendsto (primeBarycentricProjectiveRatio p q) atTop atTop := by
  have hbase : 0 < primeBarycentricProjectiveRatio p q q := by
    exact div_pos (primeBarycentricCoefficientMagnitude_head_pos q hq)
      (by
        rw [primeBarycentricCoefficientMagnitude_eq_at_mul_upperGrowth
          p hp p le_rfl (by exact_mod_cast hpq.le : (p : ℝ) ≤ q)]
        exact mul_pos (primeBarycentricCoefficientMagnitude_head_pos p hp)
          (primeBarycentricUpperGrowth_pos p p hp.one_lt le_rfl
            (by exact_mod_cast hpq.le : (p : ℝ) ≤ q)))
  have hprod := tendsto_const_nhds.pos_mul_atTop hbase
    (tendsto_primeBarycentricRelativeTailGrowth_atTop p q hp.one_lt hpq)
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop (q : ℝ)] with x hx
  exact (primeBarycentricProjectiveRatio_eq_base_mul_relativeTail
    p q hp hq hpq hx).symm

end

end RHTower

