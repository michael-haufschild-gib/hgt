import GaloisForLFunctions.RHTower.Sieve.FactorAwarePerronError

/-!
# The factor-aware Perron error summed over the prime pairs

Adding the near and far halves at one modulus gives an absolute constant plus a harmonic main
term divided by that modulus.  Summed over a pair of prime sets the two halves therefore produce
`8·(total weight) + (34x/T)(1 + log M)·(reciprocally weighted total)`: the two prime weights are
never merged into a single coefficient sequence, which is what keeps the height requirement at
`T = (log x)²`.
-/

namespace RHTower.Sieve

open Real

noncomputable section

theorem inv_log_two_lt : 1 / Real.log 2 < 2 := by
  have h := Real.log_two_gt_d9
  rw [div_lt_iff₀ (by linarith)]
  linarith

/-- **(E4)–(E6): the factor-aware truncated Perron error at one modulus.**  Summing the truncated
Perron weight over the multiples of `d` costs an absolute constant plus the harmonic main term,
with `d` retained in the denominator. -/
theorem perron_pair_total_le {x T d : ℝ} (hx : 0 < x) (hT : 0 < T) (hd : 0 < d) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M,
        (x / (d * (n : ℝ))) * truncPerronWeight T (x / (d * (n : ℝ)))
      ≤ 8 + (34 * x / (T * d)) * (1 + Real.log M) := by
  classical
  have hsplit : ∑ n ∈ Finset.Icc 1 M,
      (x / (d * (n : ℝ))) * truncPerronWeight T (x / (d * (n : ℝ)))
      = (∑ n ∈ Finset.Icc 1 M,
          (if x / 2 ≤ d * (n : ℝ) ∧ d * (n : ℝ) ≤ 2 * x then
              (x / (d * (n : ℝ))) * truncPerronWeight T (x / (d * (n : ℝ))) else 0))
        + ∑ n ∈ Finset.Icc 1 M,
            (if x / 2 ≤ d * (n : ℝ) ∧ d * (n : ℝ) ≤ 2 * x then 0
              else (x / (d * (n : ℝ))) * truncPerronWeight T (x / (d * (n : ℝ)))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs <;> ring
  rw [hsplit]
  have hnear := perron_near_pair_le (x := x) (T := T) (d := d) hx hT hd M
  have hfar := perron_far_pair_le (x := x) (T := T) (d := d) hx hT hd M
  have hlogM : (0 : ℝ) ≤ 1 + Real.log M := by
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simp
    · have : (0 : ℝ) ≤ Real.log M := Real.log_natCast_nonneg M
      linarith
  have hxTd : (0 : ℝ) < x / (T * d) := by positivity
  have hcoef : x / (T * Real.log 2 * d) ≤ 2 * (x / (T * d)) := by
    have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    rw [div_le_iff₀ (by positivity)]
    have hid : 2 * (x / (T * d)) * (T * Real.log 2 * d) = 2 * Real.log 2 * x := by
      field_simp
    rw [hid]
    nlinarith [Real.log_two_gt_d9, hx.le]
  have hfar' : ∑ n ∈ Finset.Icc 1 M,
      (if x / 2 ≤ d * (n : ℝ) ∧ d * (n : ℝ) ≤ 2 * x then 0
        else (x / (d * (n : ℝ))) * truncPerronWeight T (x / (d * (n : ℝ))))
      ≤ (2 * (x / (T * d))) * (1 + Real.log M) :=
    hfar.trans (mul_le_mul_of_nonneg_right hcoef hlogM)
  have hrw : (16 * x / (T * d)) = 16 * (x / (T * d)) := by ring
  rw [hrw] at hnear
  have hfin : (34 * x / (T * d)) * (1 + Real.log M)
      = 32 * (x / (T * d)) * (1 + Real.log M) + 2 * (x / (T * d)) * (1 + Real.log M) := by
    ring
  rw [hfin]
  linarith

/-- **(E1): the factor-aware Perron error over the full triple range.**  The two prime weights are
never collapsed into a single coefficient sequence, so the harmonic main term is divided by `p·q`
and can be summed against the arithmetic weights of the shell. -/
theorem perron_triple_error_le {x T : ℝ} (hx : 0 < x) (hT : 0 < T) (M : ℕ)
    (P Q : Finset ℕ) (w : ℕ → ℕ → ℝ) (hw : ∀ p ∈ P, ∀ q ∈ Q, 0 ≤ w p q)
    (hP : ∀ p ∈ P, 1 ≤ p) (hQ : ∀ q ∈ Q, 1 ≤ q) :
    ∑ p ∈ P, ∑ q ∈ Q, w p q * ∑ n ∈ Finset.Icc 1 M,
        (x / (((p : ℝ) * (q : ℝ)) * (n : ℝ)))
          * truncPerronWeight T (x / (((p : ℝ) * (q : ℝ)) * (n : ℝ)))
      ≤ 8 * (∑ p ∈ P, ∑ q ∈ Q, w p q)
        + (34 * x / T) * (1 + Real.log M)
            * (∑ p ∈ P, ∑ q ∈ Q, w p q / ((p : ℝ) * (q : ℝ))) := by
  have hlogM : (0 : ℝ) ≤ 1 + Real.log M := by
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simp
    · have : (0 : ℝ) ≤ Real.log M := Real.log_natCast_nonneg M
      linarith
  have hpoint : ∀ p ∈ P, ∀ q ∈ Q,
      w p q * ∑ n ∈ Finset.Icc 1 M,
          (x / (((p : ℝ) * (q : ℝ)) * (n : ℝ)))
            * truncPerronWeight T (x / (((p : ℝ) * (q : ℝ)) * (n : ℝ)))
        ≤ 8 * w p q
          + (34 * x / T) * (1 + Real.log M) * (w p q / ((p : ℝ) * (q : ℝ))) := by
    intro p hp q hq
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hP p hp
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hQ q hq
    have hd : (0 : ℝ) < (p : ℝ) * (q : ℝ) := by nlinarith
    have hbase := perron_pair_total_le (x := x) (T := T) (d := (p : ℝ) * (q : ℝ)) hx hT hd M
    have hmul := mul_le_mul_of_nonneg_left hbase (hw p hp q hq)
    refine hmul.trans (le_of_eq ?_)
    field_simp
  refine (Finset.sum_le_sum fun p hp =>
    Finset.sum_le_sum fun q hq => hpoint p hp q hq).trans (le_of_eq ?_)
  have hinner : ∀ p ∈ P,
      ∑ q ∈ Q, (8 * w p q
          + (34 * x / T) * (1 + Real.log M) * (w p q / ((p : ℝ) * (q : ℝ))))
        = 8 * (∑ q ∈ Q, w p q)
          + (34 * x / T) * (1 + Real.log M) * (∑ q ∈ Q, w p q / ((p : ℝ) * (q : ℝ))) := by
    intro p _
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

end

end RHTower.Sieve
