import GaloisForLFunctions.RHTower.Sieve.SquarefreeTotientDivisorIdentity
import GaloisForLFunctions.RHTower.Sieve.DivisorSwap
import GaloisForLFunctions.RHTower.Sieve.SquarefreeHarmonic
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
# The reciprocal totient sum is logarithmic

The divisor identity `∑_{d ∣ n} μ²(d)/φ(d) = n/φ(n)` converts a `1/φ` weight into a `1/n` weight.
Applied twice it gives two elementary bounds:

* `∑_{d ≤ N} μ²(d)/(d φ(d)) ≤ 4`, because after the divisor swap the inner sum is a partial sum of
  reciprocal squares and the outer weight is again dominated by one;
* `∑_{e ≤ N} 1/φ(e) ≤ 4 (1 + log N)`, because after the divisor swap the inner sum is a harmonic
  partial sum and the outer weight is the previous bound.

The second is the estimate that makes the Selberg diagonal of a Möbius quadratic form logarithmic
rather than a power of a logarithm: the diagonal weight is `φ(e)/e²` and the inner sums are of size
`e/φ(e)`, so the diagonal is `∑_{e ≤ N} 1/φ(e)`.
-/

open Finset ArithmeticFunction

namespace RHTower.Sieve

theorem sqfreeTotientInv_nonneg (d : ℕ) : 0 ≤ sqfreeTotientInv d := by
  rw [sqfreeTotientInv_apply]
  split
  · positivity
  · exact le_rfl

theorem sqfreeTotientInv_le_one (d : ℕ) : sqfreeTotientInv d ≤ 1 := by
  rw [sqfreeTotientInv_apply]
  split
  · rename_i h
    have hd0 : d ≠ 0 := fun h0 => not_squarefree_zero (h0 ▸ h)
    have hpos : (1 : ℝ) ≤ (Nat.totient d : ℝ) := by
      have := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hd0)
      exact_mod_cast this
    rw [div_le_one (by linarith)]
    exact hpos
  · norm_num

/-- The divisor identity, in the arithmetic-function notation. -/
theorem sum_divisors_sqfreeTotientInv' (n : ℕ) :
    ∑ d ∈ n.divisors, sqfreeTotientInv d = (n : ℝ) / (Nat.totient n : ℝ) := by
  rw [← sum_divisors_sqfreeTotientInv n]
  exact Finset.sum_congr rfl fun d _ => rfl

/-- **The reciprocal `d φ(d)` sum is bounded by an absolute constant.** -/
theorem sum_sqfreeTotientInv_div_le (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, sqfreeTotientInv d / (d : ℝ) ≤ 4 := by
  classical
  have hbound : ∀ d ∈ Finset.Icc 1 N, sqfreeTotientInv d / (d : ℝ)
      ≤ ∑ k ∈ d.divisors, sqfreeTotientInv k / (d : ℝ) ^ 2 := by
    intro d hd
    obtain ⟨hd1, -⟩ := Finset.mem_Icc.mp hd
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    have hφ : (1 : ℝ) ≤ (Nat.totient d : ℝ) := by
      have := Nat.totient_pos.mpr (by omega : 0 < d)
      exact_mod_cast this
    rw [← Finset.sum_div, sum_divisors_sqfreeTotientInv']
    have hrhs : (d : ℝ) / (Nat.totient d : ℝ) / (d : ℝ) ^ 2
        = 1 / ((d : ℝ) * (Nat.totient d : ℝ)) := by
      field_simp
    rw [hrhs, sqfreeTotientInv_apply]
    split
    · rw [div_div]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      ring_nf
      exact le_rfl
    · simp only [zero_div]
      positivity
  refine le_trans (Finset.sum_le_sum hbound) ?_
  have hrw : ∀ d ∈ Finset.Icc 1 N, ∑ k ∈ d.divisors, sqfreeTotientInv k / (d : ℝ) ^ 2
      = ∑ k ∈ d.divisors,
          sqfreeTotientInv k / ((k : ℝ) * ((d / k : ℕ) : ℝ)) ^ 2 := by
    intro d hd
    obtain ⟨hd1, -⟩ := Finset.mem_Icc.mp hd
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hkd, -⟩ := Nat.mem_divisors.mp hk
    have : (k : ℝ) * ((d / k : ℕ) : ℝ) = (d : ℝ) := by
      have hnat : k * (d / k) = d := Nat.mul_div_cancel' hkd
      exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) hnat
    rw [this]
  rw [Finset.sum_congr rfl hrw]
  rw [sum_divisors_swap N (fun k j => sqfreeTotientInv k / ((k : ℝ) * (j : ℝ)) ^ 2)]
  have hinner : ∀ k ∈ Finset.Icc 1 N,
      ∑ j ∈ Finset.Icc 1 (N / k), sqfreeTotientInv k / ((k : ℝ) * (j : ℝ)) ^ 2
        ≤ 2 * (1 / (k : ℝ) ^ 2) := by
    intro k hk
    obtain ⟨hk1, -⟩ := Finset.mem_Icc.mp hk
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hfac : ∀ j : ℕ, sqfreeTotientInv k / ((k : ℝ) * (j : ℝ)) ^ 2
        = (sqfreeTotientInv k / (k : ℝ) ^ 2) * (1 / (j : ℝ) ^ 2) := by
      intro j
      rw [mul_pow]
      ring
    rw [Finset.sum_congr rfl (fun j _ => hfac j), ← Finset.mul_sum]
    have hsq := sum_inv_sq_le_two (N / k)
    have hnn : (0 : ℝ) ≤ sqfreeTotientInv k / (k : ℝ) ^ 2 :=
      div_nonneg (sqfreeTotientInv_nonneg k) (by positivity)
    calc sqfreeTotientInv k / (k : ℝ) ^ 2 * ∑ j ∈ Finset.Icc 1 (N / k), 1 / (j : ℝ) ^ 2
        ≤ sqfreeTotientInv k / (k : ℝ) ^ 2 * 2 := mul_le_mul_of_nonneg_left hsq hnn
      _ ≤ (1 / (k : ℝ) ^ 2) * 2 := by
          have := sqfreeTotientInv_le_one k
          have hpos : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
          have hle : sqfreeTotientInv k / (k : ℝ) ^ 2 ≤ 1 / (k : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right this hpos.le
          linarith
      _ = 2 * (1 / (k : ℝ) ^ 2) := by ring
  refine le_trans (Finset.sum_le_sum hinner) ?_
  rw [← Finset.mul_sum]
  have := sum_inv_sq_le_two N
  linarith

/-- **The reciprocal totient sum is logarithmic.** -/
theorem sum_inv_totient_le (N : ℕ) :
    ∑ e ∈ Finset.Icc 1 N, 1 / (Nat.totient e : ℝ) ≤ 4 * (1 + Real.log N) := by
  classical
  have hlogN : (0 : ℝ) ≤ Real.log N := Real.log_natCast_nonneg N
  have hrw : ∀ e ∈ Finset.Icc 1 N, 1 / (Nat.totient e : ℝ)
      = ∑ k ∈ e.divisors, sqfreeTotientInv k / ((k : ℝ) * ((e / k : ℕ) : ℝ)) := by
    intro e he
    obtain ⟨he1, -⟩ := Finset.mem_Icc.mp he
    have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast (by omega : 0 < e)
    have hstep : ∀ k ∈ e.divisors, sqfreeTotientInv k / ((k : ℝ) * ((e / k : ℕ) : ℝ))
        = sqfreeTotientInv k / (e : ℝ) := by
      intro k hk
      obtain ⟨hkd, -⟩ := Nat.mem_divisors.mp hk
      have : (k : ℝ) * ((e / k : ℕ) : ℝ) = (e : ℝ) := by
        have hnat : k * (e / k) = e := Nat.mul_div_cancel' hkd
        exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) hnat
      rw [this]
    rw [Finset.sum_congr rfl hstep, ← Finset.sum_div, sum_divisors_sqfreeTotientInv']
    have hφ : (0 : ℝ) < (Nat.totient e : ℝ) := by
      have := Nat.totient_pos.mpr (by omega : 0 < e)
      exact_mod_cast this
    field_simp
  rw [Finset.sum_congr rfl hrw]
  rw [sum_divisors_swap N (fun k j => sqfreeTotientInv k / ((k : ℝ) * (j : ℝ)))]
  have hinner : ∀ k ∈ Finset.Icc 1 N,
      ∑ j ∈ Finset.Icc 1 (N / k), sqfreeTotientInv k / ((k : ℝ) * (j : ℝ))
        ≤ (1 + Real.log N) * (sqfreeTotientInv k / (k : ℝ)) := by
    intro k hk
    obtain ⟨hk1, -⟩ := Finset.mem_Icc.mp hk
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hfac : ∀ j : ℕ, sqfreeTotientInv k / ((k : ℝ) * (j : ℝ))
        = (sqfreeTotientInv k / (k : ℝ)) * (1 / (j : ℝ)) := by
      intro j
      ring
    rw [Finset.sum_congr rfl (fun j _ => hfac j), ← Finset.mul_sum]
    have hharm := sum_Icc_one_div_le_one_add_log (N / k)
    have hmono : Real.log ((N / k : ℕ) : ℝ) ≤ Real.log N := by
      rcases Nat.eq_zero_or_pos (N / k) with h0 | hpos
      · rw [h0]
        simpa using hlogN
      · refine Real.log_le_log (by exact_mod_cast hpos) ?_
        have : (N / k : ℕ) ≤ N := Nat.div_le_self N k
        exact_mod_cast this
    have hnn : (0 : ℝ) ≤ sqfreeTotientInv k / (k : ℝ) :=
      div_nonneg (sqfreeTotientInv_nonneg k) hkR.le
    have hbound : ∑ j ∈ Finset.Icc 1 (N / k), 1 / (j : ℝ) ≤ 1 + Real.log N := by
      linarith
    calc sqfreeTotientInv k / (k : ℝ) * ∑ j ∈ Finset.Icc 1 (N / k), 1 / (j : ℝ)
        ≤ sqfreeTotientInv k / (k : ℝ) * (1 + Real.log N) :=
          mul_le_mul_of_nonneg_left hbound hnn
      _ = (1 + Real.log N) * (sqfreeTotientInv k / (k : ℝ)) := by ring
  refine le_trans (Finset.sum_le_sum hinner) ?_
  rw [← Finset.mul_sum]
  have hsum := sum_sqfreeTotientInv_div_le N
  have hpos : (0 : ℝ) ≤ 1 + Real.log N := by linarith
  calc (1 + Real.log N) * ∑ k ∈ Finset.Icc 1 N, sqfreeTotientInv k / (k : ℝ)
      ≤ (1 + Real.log N) * 4 := mul_le_mul_of_nonneg_left hsum hpos
    _ = 4 * (1 + Real.log N) := by ring

end RHTower.Sieve
