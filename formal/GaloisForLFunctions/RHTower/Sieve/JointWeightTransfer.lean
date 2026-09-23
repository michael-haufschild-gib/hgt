import GaloisForLFunctions.RHTower.Sieve.JointTuranKubilius

/-!
# Transferring a window mean square to a weighted one

Soundararajan's exposé §4 replaces `∑_{x<n≤x+h}λ(n)` by `(1/W(P)W(Q))∑_{x<n≤x+h}λ(n)ω_P(n)ω_Q(n)`,
at the cost of the Turán–Kubilius variance of `ω_Pω_Q`.  The atom is a single window; the windows of
a dyadic family are disjoint, so the variance is paid once over the whole range.
-/

namespace RHTower.Sieve

open Finset

/-- **The transfer on one window.**  A unit-bounded sequence may be weighted by any function `ω` at
the cost of twice the window length times the variance of `ω` about `W`. -/
theorem sq_window_sum_le_weighted {f ω : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) (W : ℝ) (t h : ℕ) :
    W ^ (2 : ℕ) * (∑ n ∈ Finset.Ioc t (t + h), f n) ^ (2 : ℕ)
      ≤ 2 * (∑ n ∈ Finset.Ioc t (t + h), f n * ω n) ^ (2 : ℕ)
        + 2 * (h : ℝ) * ∑ n ∈ Finset.Ioc t (t + h), (ω n - W) ^ (2 : ℕ) := by
  classical
  set I : Finset ℕ := Finset.Ioc t (t + h) with hI
  have hcard : I.card = h := by rw [hI, Nat.card_Ioc]; omega
  -- the algebraic identity
  have hsplit : W * ∑ n ∈ I, f n
      = (∑ n ∈ I, f n * ω n) - ∑ n ∈ I, f n * (ω n - W) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  -- Cauchy–Schwarz on the defect
  have hdefect : (∑ n ∈ I, f n * (ω n - W)) ^ (2 : ℕ) ≤ (h : ℝ) * ∑ n ∈ I, (ω n - W) ^ (2 : ℕ) := by
    have hbase : (∑ n ∈ I, f n * (ω n - W)) ^ (2 : ℕ)
        ≤ (I.card : ℝ) * ∑ n ∈ I, (f n * (ω n - W)) ^ (2 : ℕ) :=
      sq_sum_le_card_mul_sum_sq
    refine hbase.trans ?_
    rw [hcard]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => ?_) (Nat.cast_nonneg _)
    have h1 : |f n| ≤ 1 := hf n
    have h2 : (f n * (ω n - W)) ^ (2 : ℕ) = (f n) ^ (2 : ℕ) * (ω n - W) ^ (2 : ℕ) := by ring
    have h3 : (f n) ^ (2 : ℕ) ≤ 1 := by
      have := abs_le.1 h1
      nlinarith [this.1, this.2]
    rw [h2]
    nlinarith [h3, sq_nonneg (ω n - W)]
  have hsq : (W * ∑ n ∈ I, f n) ^ (2 : ℕ)
      ≤ 2 * (∑ n ∈ I, f n * ω n) ^ (2 : ℕ) + 2 * (∑ n ∈ I, f n * (ω n - W)) ^ (2 : ℕ) := by
    rw [hsplit]
    nlinarith [sq_nonneg ((∑ n ∈ I, f n * ω n) + ∑ n ∈ I, f n * (ω n - W))]
  have hval : (W * ∑ n ∈ I, f n) ^ (2 : ℕ) = W ^ (2 : ℕ) * (∑ n ∈ I, f n) ^ (2 : ℕ) := by ring
  rw [hval] at hsq
  have hmul : 2 * (∑ n ∈ I, f n * (ω n - W)) ^ (2 : ℕ)
      ≤ 2 * ((h : ℝ) * ∑ n ∈ I, (ω n - W) ^ (2 : ℕ)) := by linarith [hdefect]
  linarith [hsq, hmul]

/-- The `j`-th window of a dyadic family of disjoint windows. -/
def windowStart (A h j : ℕ) : ℕ := A + j * h

theorem windows_pairwise_disjoint (A h : ℕ) {j k : ℕ} (hjk : j ≠ k) :
    Disjoint (Finset.Ioc (windowStart A h j) (windowStart A h j + h))
      (Finset.Ioc (windowStart A h k) (windowStart A h k + h)) := by
  refine Finset.disjoint_left.2 fun n hn hm => ?_
  rw [Finset.mem_Ioc] at hn hm
  rw [windowStart] at hn hm
  rcases Nat.lt_or_ge j k with hlt | hge
  · have : j * h + h ≤ k * h := by
      have : (j + 1) * h ≤ k * h := Nat.mul_le_mul_right h (by omega)
      have hexp : (j + 1) * h = j * h + h := by ring
      omega
    omega
  · have hkj : k < j := by omega
    have : k * h + h ≤ j * h := by
      have : (k + 1) * h ≤ j * h := Nat.mul_le_mul_right h (by omega)
      have hexp : (k + 1) * h = k * h + h := by ring
      omega
    omega

/-- **The transfer over a dyadic family of windows.**  The windows are disjoint, so the
Turán–Kubilius variance is paid once. -/
theorem sum_sq_windows_le_weighted {f ω : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) (W : ℝ) (A h K M : ℕ)
    (hin : ∀ j < K, ∀ n ∈ Finset.Ioc (windowStart A h j) (windowStart A h j + h),
      n ∈ Finset.Icc 1 M) :
    W ^ (2 : ℕ) * ∑ j ∈ Finset.range K,
        (∑ n ∈ Finset.Ioc (windowStart A h j) (windowStart A h j + h), f n) ^ (2 : ℕ)
      ≤ 2 * ∑ j ∈ Finset.range K,
          (∑ n ∈ Finset.Ioc (windowStart A h j) (windowStart A h j + h), f n * ω n) ^ (2 : ℕ)
        + 2 * (h : ℝ) * ∑ n ∈ Finset.Icc 1 M, (ω n - W) ^ (2 : ℕ) := by
  classical
  have hterm : ∀ j ∈ Finset.range K,
      W ^ (2 : ℕ) * (∑ n ∈ Finset.Ioc (windowStart A h j) (windowStart A h j + h), f n) ^ (2 : ℕ)
        ≤ 2 * (∑ n ∈ Finset.Ioc (windowStart A h j) (windowStart A h j + h), f n * ω n) ^ (2 : ℕ)
          + 2 * (h : ℝ)
            * ∑ n ∈ Finset.Ioc (windowStart A h j) (windowStart A h j + h), (ω n - W) ^ (2 : ℕ) :=
    fun j _ => sq_window_sum_le_weighted hf W _ _
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  -- the disjoint windows fit inside `[1, M]`
  have hvar : ∑ j ∈ Finset.range K,
        ∑ n ∈ Finset.Ioc (windowStart A h j) (windowStart A h j + h), (ω n - W) ^ (2 : ℕ)
      ≤ ∑ n ∈ Finset.Icc 1 M, (ω n - W) ^ (2 : ℕ) := by
    rw [← Finset.sum_biUnion]
    · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => sq_nonneg _)
      intro n hn
      rw [Finset.mem_biUnion] at hn
      obtain ⟨j, hj, hnj⟩ := hn
      exact hin j (Finset.mem_range.1 hj) n hnj
    · intro j hj k hk hjk
      exact windows_pairwise_disjoint A h hjk
  have hsplit : ∑ j ∈ Finset.range K,
        (2 * (∑ n ∈ Finset.Ioc (windowStart A h j) (windowStart A h j + h), f n * ω n) ^ (2 : ℕ)
          + 2 * (h : ℝ)
            * ∑ n ∈ Finset.Ioc (windowStart A h j) (windowStart A h j + h), (ω n - W) ^ (2 : ℕ))
      = 2 * ∑ j ∈ Finset.range K,
          (∑ n ∈ Finset.Ioc (windowStart A h j) (windowStart A h j + h), f n * ω n) ^ (2 : ℕ)
        + 2 * (h : ℝ) * ∑ j ∈ Finset.range K,
            ∑ n ∈ Finset.Ioc (windowStart A h j) (windowStart A h j + h), (ω n - W) ^ (2 : ℕ) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hsplit] at hsum
  have hh0 : (0 : ℝ) ≤ 2 * (h : ℝ) := by positivity
  nlinarith [hsum, mul_le_mul_of_nonneg_left hvar hh0]

/-- **The reduction `(34)` of Soundararajan's exposé §4, in discrete form.**  A unit-bounded
sequence on a dyadic family of disjoint windows may be replaced by its `ω_P·ω_Q`-weighted version,
at a cost that is `h` times the joint Turán–Kubilius variance. -/
theorem sum_sq_windows_le_joint {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hQ : ∀ q ∈ Q, q.Prime) (hPQ : Disjoint P Q) {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1)
    (A h K M : ℕ)
    (hin : ∀ j < K, ∀ n ∈ Finset.Ioc (windowStart A h j) (windowStart A h j + h),
      n ∈ Finset.Icc 1 M) :
    ((∑ p ∈ P, (1 : ℝ) / (p : ℝ)) * (∑ q ∈ Q, (1 : ℝ) / (q : ℝ))) ^ (2 : ℕ)
        * ∑ j ∈ Finset.range K,
          (∑ n ∈ Finset.Ioc (windowStart A h j) (windowStart A h j + h), f n) ^ (2 : ℕ)
      ≤ 2 * ∑ j ∈ Finset.range K,
          (∑ n ∈ Finset.Ioc (windowStart A h j) (windowStart A h j + h),
            f n * (((primeFactorsIn P n).card : ℝ) * ((primeFactorsIn Q n).card : ℝ))) ^ (2 : ℕ)
        + 2 * (h : ℝ)
          * ((M : ℝ) * ((∑ p ∈ P, (1 : ℝ) / (p : ℝ)) * (∑ q ∈ Q, (1 : ℝ) / (q : ℝ)))
              * ((∑ p ∈ P, (1 : ℝ) / (p : ℝ)) + (∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) + 1)
            + 2 * ((∑ p ∈ P, (1 : ℝ) / (p : ℝ)) * (∑ q ∈ Q, (1 : ℝ) / (q : ℝ)))
                * (P.card : ℝ) * (Q.card : ℝ)) := by
  have hbase := sum_sq_windows_le_weighted (f := f)
    (ω := fun n => ((primeFactorsIn P n).card : ℝ) * ((primeFactorsIn Q n).card : ℝ)) hf
    ((∑ p ∈ P, (1 : ℝ) / (p : ℝ)) * (∑ q ∈ Q, (1 : ℝ) / (q : ℝ))) A h K M hin
  have hvar := sum_sq_joint_deviation_le hP hQ hPQ M
  have hh0 : (0 : ℝ) ≤ 2 * (h : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hvar hh0
  linarith [hbase, hmul]

end RHTower.Sieve
