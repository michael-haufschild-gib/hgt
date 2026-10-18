import GaloisForLFunctions.RHTower.Sieve.LevinsonGcdFormBound

/-!
# A uniform cubic mean for the reciprocal totient ratio

The positive divisor identity for `n / φ(n)` and squarefree multiplicativity
give `Σ_{n≤N} (n / φ(n))³ ≤ 16384 N`. The constant is independent of the
cutoff. No prime number theorem or cancellation estimate is used.
-/

open Finset ArithmeticFunction

namespace RHTower.Sieve

noncomputable section

private def massTotientRatio (n : ℕ) : ℝ := (n : ℝ) / (Nat.totient n : ℝ)

private theorem ratio_nonneg (n : ℕ) : 0 ≤ massTotientRatio n := by
  unfold massTotientRatio
  positivity

private theorem ratio_mul_le (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    massTotientRatio (a * b) ≤ massTotientRatio a * massTotientRatio b := by
  have hφa : (0 : ℝ) < Nat.totient a := by exact_mod_cast Nat.totient_pos.mpr ha
  have hφb : (0 : ℝ) < Nat.totient b := by exact_mod_cast Nat.totient_pos.mpr hb
  have hφ : (Nat.totient a : ℝ) * Nat.totient b ≤ Nat.totient (a * b) := by
    exact_mod_cast Nat.totient_super_multiplicative a b
  simp only [massTotientRatio, Nat.cast_mul, div_mul_div_comm]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hφ

private theorem squarefree_ratio_weight_mul_le (a b : ℕ) :
    sqfreeTotientInv (a * b) / (Nat.totient (a * b) : ℝ) ≤
      (sqfreeTotientInv a / (Nat.totient a : ℝ)) *
        (sqfreeTotientInv b / (Nat.totient b : ℝ)) := by
  by_cases hsq : Squarefree (a * b)
  · obtain ⟨hcop, hsa, hsb⟩ := Nat.squarefree_mul_iff.mp hsq
    rw [sqfreeTotientInv_apply, if_pos hsq, sqfreeTotientInv_apply, if_pos hsa,
      sqfreeTotientInv_apply, if_pos hsb, Nat.totient_mul hcop]
    push_cast
    exact le_of_eq (by ring)
  · rw [sqfreeTotientInv_apply, if_neg hsq, zero_div]
    exact mul_nonneg
      (div_nonneg (sqfreeTotientInv_nonneg a) (Nat.cast_nonneg _))
      (div_nonneg (sqfreeTotientInv_nonneg b) (Nat.cast_nonneg _))

/-- A second reciprocal-totient factor still has a uniformly bounded squarefree mass. -/
theorem sum_sqfreeTotientInv_mul_div_totient_sq_le (N : ℕ) :
    ∑ n ∈ Icc 1 N, sqfreeTotientInv n * (n : ℝ) / (Nat.totient n : ℝ)^2 ≤ 256 := by
  let b : ℕ → ℝ := fun n => sqfreeTotientInv n / (Nat.totient n : ℝ)
  have hb (n : ℕ) : 0 ≤ b n :=
    div_nonneg (sqfreeTotientInv_nonneg n) (Nat.cast_nonneg _)
  have hterm (n : ℕ) :
      sqfreeTotientInv n * (n : ℝ) / (Nat.totient n : ℝ)^2 =
        ∑ d ∈ n.divisors, b (d * (n / d)) * sqfreeTotientInv d := by
    calc
      _ = b n * ((n : ℝ) / (Nat.totient n : ℝ)) := by dsimp [b]; ring
      _ = ∑ d ∈ n.divisors, b n * sqfreeTotientInv d := by
        rw [← sum_divisors_sqfreeTotientInv', Finset.mul_sum]
      _ = _ := Finset.sum_congr rfl fun d hd => by
        rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
  rw [Finset.sum_congr rfl (fun n _ => hterm n),
    sum_divisors_swap N (fun d k => b (d * k) * sqfreeTotientInv d)]
  have hinner (d : ℕ) :
      ∑ k ∈ Icc 1 (N / d), b (d * k) * sqfreeTotientInv d ≤ 16 * b d := by
    calc
      _ ≤ ∑ k ∈ Icc 1 (N / d), b d * b k := by
        apply Finset.sum_le_sum
        intro k hk
        calc
          _ ≤ (b d * b k) * sqfreeTotientInv d :=
            mul_le_mul_of_nonneg_right (squarefree_ratio_weight_mul_le d k)
              (sqfreeTotientInv_nonneg d)
          _ ≤ (b d * b k) * 1 :=
            mul_le_mul_of_nonneg_left (sqfreeTotientInv_le_one d) (mul_nonneg (hb d) (hb k))
          _ = _ := mul_one _
      _ = b d * ∑ k ∈ Icc 1 (N / d), b k := (Finset.mul_sum ..).symm
      _ ≤ b d * 16 :=
        mul_le_mul_of_nonneg_left (sum_sqfreeTotientInv_div_totient_le (N / d)) (hb d)
      _ = _ := mul_comm _ _
  calc
    _ ≤ ∑ d ∈ Icc 1 N, 16 * b d := Finset.sum_le_sum fun d _ => hinner d
    _ = 16 * ∑ d ∈ Icc 1 N, b d := (Finset.mul_sum ..).symm
    _ ≤ 16 * 16 :=
      mul_le_mul_of_nonneg_left (sum_sqfreeTotientInv_div_totient_le N) (by norm_num)
    _ = 256 := by norm_num

private theorem ratio_mean_step (k : ℕ) {C B : ℝ} (hC : 0 ≤ C)
    (hmean : ∀ X : ℕ, ∑ n ∈ Icc 1 X, massTotientRatio n ^ k ≤ C * (X : ℝ))
    (hweight : ∀ X : ℕ,
      ∑ n ∈ Icc 1 X, sqfreeTotientInv n * massTotientRatio n ^ k / (n : ℝ) ≤ B)
    (N : ℕ) :
    ∑ n ∈ Icc 1 N, massTotientRatio n ^ (k + 1) ≤ (C * B) * (N : ℝ) := by
  have hterm (n : ℕ) :
      massTotientRatio n ^ (k + 1) =
        ∑ d ∈ n.divisors, sqfreeTotientInv d * massTotientRatio (d * (n / d)) ^ k := by
    calc
      _ = ((n : ℝ) / (Nat.totient n : ℝ)) * massTotientRatio n ^ k := by
        rw [pow_succ]; dsimp [massTotientRatio]; ring
      _ = ∑ d ∈ n.divisors, sqfreeTotientInv d * massTotientRatio n ^ k := by
        rw [← sum_divisors_sqfreeTotientInv', Finset.sum_mul]
      _ = _ := Finset.sum_congr rfl fun d hd => by
        rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
  rw [Finset.sum_congr rfl (fun n _ => hterm n),
    sum_divisors_swap N (fun d m => sqfreeTotientInv d * massTotientRatio (d * m)^k)]
  have hinner (d : ℕ) (hd : d ∈ Icc 1 N) :
      ∑ m ∈ Icc 1 (N / d), sqfreeTotientInv d * massTotientRatio (d * m)^k ≤
        C * (N : ℝ) * (sqfreeTotientInv d * massTotientRatio d^k / (d : ℝ)) := by
    have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
    have hnonneg : 0 ≤ sqfreeTotientInv d * massTotientRatio d^k :=
      mul_nonneg (sqfreeTotientInv_nonneg d) (pow_nonneg (ratio_nonneg d) k)
    calc
      _ ≤ ∑ m ∈ Icc 1 (N / d),
          sqfreeTotientInv d * (massTotientRatio d^k * massTotientRatio m^k) := by
        apply Finset.sum_le_sum
        intro m hm
        apply mul_le_mul_of_nonneg_left _ (sqfreeTotientInv_nonneg d)
        rw [← mul_pow]
        exact pow_le_pow_left₀ (ratio_nonneg _) (ratio_mul_le d m hd0 (Finset.mem_Icc.mp hm).1) k
      _ = (sqfreeTotientInv d * massTotientRatio d^k) *
          ∑ m ∈ Icc 1 (N / d), massTotientRatio m^k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        ring
      _ ≤ (sqfreeTotientInv d * massTotientRatio d^k) * (C * ((N / d : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (hmean (N / d)) hnonneg
      _ ≤ (sqfreeTotientInv d * massTotientRatio d^k) * (C * ((N : ℝ) / (d : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ hnonneg
        exact mul_le_mul_of_nonneg_left (Nat.cast_div_le (m := N) (n := d)) hC
      _ = _ := by ring
  calc
    _ ≤ ∑ d ∈ Icc 1 N, C * (N : ℝ) *
        (sqfreeTotientInv d * massTotientRatio d^k / (d : ℝ)) := Finset.sum_le_sum hinner
    _ = C * (N : ℝ) *
        ∑ d ∈ Icc 1 N, sqfreeTotientInv d * massTotientRatio d^k / (d : ℝ) :=
      (Finset.mul_sum ..).symm
    _ ≤ C * (N : ℝ) * B :=
      mul_le_mul_of_nonneg_left (hweight N) (mul_nonneg hC (Nat.cast_nonneg _))
    _ = _ := by ring

/-- The reciprocal totient ratio has a uniformly bounded cubic average. -/
theorem sum_totientRatio_cube_le (N : ℕ) :
    ∑ n ∈ Icc 1 N, ((n : ℝ) / (Nat.totient n : ℝ))^3 ≤ 16384 * (N : ℝ) := by
  have h0 (X : ℕ) : ∑ n ∈ Icc 1 X, massTotientRatio n^0 ≤ 1 * (X : ℝ) := by simp
  have hw0 (X : ℕ) :
      ∑ n ∈ Icc 1 X, sqfreeTotientInv n * massTotientRatio n^0 / (n : ℝ) ≤ 4 := by
    simpa using sum_sqfreeTotientInv_div_le X
  have h1 (X : ℕ) : ∑ n ∈ Icc 1 X, massTotientRatio n^1 ≤ 4 * (X : ℝ) := by
    simpa using ratio_mean_step 0 (by norm_num : (0 : ℝ) ≤ 1) h0 hw0 X
  have hw1 (X : ℕ) :
      ∑ n ∈ Icc 1 X, sqfreeTotientInv n * massTotientRatio n^1 / (n : ℝ) ≤ 16 := by
    convert sum_sqfreeTotientInv_div_totient_le X using 1
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show 0 < n from (Finset.mem_Icc.mp hn).1).ne'
    dsimp [massTotientRatio]
    field_simp
  have h2 (X : ℕ) : ∑ n ∈ Icc 1 X, massTotientRatio n^2 ≤ 64 * (X : ℝ) := by
    convert ratio_mean_step 1 (by norm_num : (0 : ℝ) ≤ 4) h1 hw1 X using 1
    norm_num
  have hw2 (X : ℕ) :
      ∑ n ∈ Icc 1 X, sqfreeTotientInv n * massTotientRatio n^2 / (n : ℝ) ≤ 256 := by
    convert sum_sqfreeTotientInv_mul_div_totient_sq_le X using 1
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show 0 < n from (Finset.mem_Icc.mp hn).1).ne'
    dsimp [massTotientRatio]
    field_simp
  convert ratio_mean_step 2 (by norm_num : (0 : ℝ) ≤ 64) h2 hw2 N using 1 <;>
    norm_num [massTotientRatio]

end

end RHTower.Sieve
