/- Finite Abel control for quadratic cumulative profiles under increment convolution. -/

import GaloisForLFunctions.RHTower.HarmonicPrimitiveLadder

noncomputable section

open Finset
open scoped BigOperators

namespace RHTower.Sieve

/-- Multiplicative-log convolution written from increments of a cumulative profile. -/
def quadraticIncrementConvolution (C : ℕ → ℝ) (M : ℕ) : ℝ :=
  ∑ j ∈ Finset.range M, (C (j + 1) - C j) * C (M - j)

private def quadraticProfile (c : ℝ) (n : ℕ) : ℝ := c * (n : ℝ) ^ 2

private theorem sum_range_cast (M : ℕ) :
    (∑ j ∈ Finset.range M, (j : ℝ)) =
      (M : ℝ) * ((M : ℝ) - 1) / 2 := by
  induction M with
  | zero => norm_num
  | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

private theorem sum_range_cast_sq (M : ℕ) :
    (∑ j ∈ Finset.range M, (j : ℝ) ^ 2) =
      (M : ℝ) * ((M : ℝ) - 1) * (2 * (M : ℝ) - 1) / 6 := by
  induction M with
  | zero => norm_num
  | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

private theorem sum_range_cast_cube (M : ℕ) :
    (∑ j ∈ Finset.range M, (j : ℝ) ^ 3) =
      (M : ℝ) ^ 2 * ((M : ℝ) - 1) ^ 2 / 4 := by
  induction M with
  | zero => norm_num
  | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

private theorem sum_range_linear_mul_reverse_sq (M : ℕ) :
    (∑ j ∈ Finset.range M,
      (2 * (j : ℝ) + 1) * ((M : ℝ) - (j : ℝ)) ^ 2) =
      (M : ℝ) * ((M : ℝ) + 1) *
        ((M : ℝ) ^ 2 + (M : ℝ) + 1) / 6 := by
  induction M with
  | zero => norm_num
  | succ M ih =>
      rw [Finset.sum_range_succ]
      have hsplit :
          (∑ j ∈ Finset.range M,
              (2 * (j : ℝ) + 1) *
                (((M + 1 : ℕ) : ℝ) - (j : ℝ)) ^ 2) =
            (∑ j ∈ Finset.range M,
              (2 * (j : ℝ) + 1) * ((M : ℝ) - (j : ℝ)) ^ 2) +
            ∑ j ∈ Finset.range M,
              (-4 * (j : ℝ) ^ 2 + 4 * (M : ℝ) * (j : ℝ) +
                (2 * (M : ℝ) + 1)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        push_cast
        ring
      rw [hsplit, ih]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← Finset.mul_sum, ← Finset.mul_sum, sum_range_cast,
        sum_range_cast_sq]
      push_cast
      ring

private theorem quadraticIncrementConvolution_profile (c : ℝ) (M : ℕ) :
    quadraticIncrementConvolution (quadraticProfile c) M =
      c ^ 2 * ((M : ℝ) * ((M : ℝ) + 1) *
        ((M : ℝ) ^ 2 + (M : ℝ) + 1) / 6) := by
  rw [quadraticIncrementConvolution]
  calc
    (∑ j ∈ Finset.range M,
        (quadraticProfile c (j + 1) - quadraticProfile c j) *
          quadraticProfile c (M - j)) =
        c ^ 2 * ∑ j ∈ Finset.range M,
          (2 * (j : ℝ) + 1) * ((M : ℝ) - (j : ℝ)) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjM : j ≤ M := Nat.le_of_lt (Finset.mem_range.mp hj)
      rw [quadraticProfile, quadraticProfile, quadraticProfile,
        Nat.cast_sub hjM]
      push_cast
      ring
    _ = _ := by rw [sum_range_linear_mul_reverse_sq]

private theorem sum_range_increment (C : ℕ → ℝ) (M : ℕ) :
    (∑ j ∈ Finset.range M, (C (j + 1) - C j)) = C M - C 0 := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      ring

private theorem increment_nonneg {C : ℕ → ℝ} (hC : Monotone C) (j : ℕ) :
    0 ≤ C (j + 1) - C j := sub_nonneg.mpr (hC (Nat.le_succ j))

private theorem abs_increment_inner_error_sum_le
    {C : ℕ → ℝ} {c K : ℝ}
    (hC0 : C 0 = 0) (hCmono : Monotone C)
    (hc : 0 ≤ c) (hK : 0 ≤ K)
    (happrox : ∀ n, |C n - quadraticProfile c n| ≤ K * ((n : ℝ) + 1))
    (M : ℕ) :
    |∑ j ∈ Finset.range M,
        (C (j + 1) - C j) *
          (C (M - j) - quadraticProfile c (M - j))| ≤
      K * (c + K) * ((M : ℝ) + 1) ^ 3 := by
  calc
    |∑ j ∈ Finset.range M,
        (C (j + 1) - C j) *
          (C (M - j) - quadraticProfile c (M - j))| ≤
        ∑ j ∈ Finset.range M,
          |(C (j + 1) - C j) *
            (C (M - j) - quadraticProfile c (M - j))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range M,
          (C (j + 1) - C j) * (K * ((M : ℝ) + 1)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjM : j ≤ M := Nat.le_of_lt (Finset.mem_range.mp hj)
      rw [abs_mul, abs_of_nonneg (increment_nonneg hCmono j)]
      have he := happrox (M - j)
      have hcast : (((M - j : ℕ) : ℝ) + 1) ≤ (M : ℝ) + 1 := by
        exact_mod_cast Nat.succ_le_succ (Nat.sub_le M j)
      exact mul_le_mul (le_rfl) (he.trans (mul_le_mul_of_nonneg_left hcast hK))
        (abs_nonneg _) (increment_nonneg hCmono j)
    _ = K * ((M : ℝ) + 1) * C M := by
      rw [← Finset.sum_mul, sum_range_increment, hC0, sub_zero]
      ring
    _ ≤ K * (c + K) * ((M : ℝ) + 1) ^ 3 := by
      have hCM := (abs_le.mp (happrox M)).2
      have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
      have hCMupper : C M ≤ (c + K) * ((M : ℝ) + 1) ^ 2 := by
        rw [quadraticProfile] at hCM
        nlinarith [sq_nonneg ((M : ℝ) + 1), mul_nonneg hc (sq_nonneg (M : ℝ))]
      have hfront : 0 ≤ K * ((M : ℝ) + 1) := mul_nonneg hK (by positivity)
      calc
        K * ((M : ℝ) + 1) * C M ≤
            K * ((M : ℝ) + 1) * ((c + K) * ((M : ℝ) + 1) ^ 2) :=
          mul_le_mul_of_nonneg_left hCMupper hfront
        _ = _ := by ring

private theorem abs_increment_model_error_sum_le
    {C : ℕ → ℝ} {c K : ℝ}
    (hC0 : C 0 = 0) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (happrox : ∀ n, |C n - quadraticProfile c n| ≤ K * ((n : ℝ) + 1))
    (M : ℕ) :
    |∑ j ∈ Finset.range M,
        ((C (j + 1) - C j) -
          (quadraticProfile c (j + 1) - quadraticProfile c j)) *
          quadraticProfile c (M - j)| ≤
      4 * K * c * ((M : ℝ) + 1) ^ 3 := by
  by_cases hM : M = 0
  · subst M
    norm_num
    positivity
  have hMpos : 0 < M := Nat.pos_of_ne_zero hM
  let e : ℕ → ℝ := fun n => C n - quadraticProfile c n
  let A : ℕ → ℝ := fun n => quadraticProfile c (M + 1 - n)
  have habel := RHTower.sum_telescope_abel e A (M - 1)
  have hMsub : M - 1 + 1 = M := by omega
  rw [hMsub] at habel
  have hreindex :
      (∑ j ∈ Finset.range M,
          ((C (j + 1) - C j) -
            (quadraticProfile c (j + 1) - quadraticProfile c j)) *
            quadraticProfile c (M - j)) =
        ∑ n ∈ Finset.Icc 1 M, (e n - e (n - 1)) * A n := by
    let F : ℕ → ℝ := fun n => (e n - e (n - 1)) * A n
    have hset : Finset.range (M + 1) = insert 0 (Finset.Icc 1 M) := by
      ext n
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc,
        Nat.lt_succ_iff]
      omega
    calc
      (∑ j ∈ Finset.range M,
          ((C (j + 1) - C j) -
            (quadraticProfile c (j + 1) - quadraticProfile c j)) *
            quadraticProfile c (M - j)) =
          ∑ j ∈ Finset.range M, F (j + 1) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [F, e, A]
        have hjM : j < M := Finset.mem_range.mp hj
        have hsub : M + 1 - (j + 1) = M - j := by omega
        rw [hsub]
        have hpred : j + 1 - 1 = j := by omega
        rw [hpred]
        ring
      _ = ∑ n ∈ Finset.range (M + 1), F n := by
        rw [Finset.sum_range_succ']
        simp [F]
      _ = ∑ n ∈ Finset.Icc 1 M, F n := by
        rw [hset, Finset.sum_insert (by simp)]
        simp [F]
      _ = _ := rfl
  rw [hreindex, habel]
  have he0 : e 0 = 0 := by simp [e, hC0, quadraticProfile]
  rw [he0, zero_mul, sub_zero]
  calc
    |e M * A M +
        ∑ n ∈ Finset.Icc 1 (M - 1), e n * (A n - A (n + 1))| ≤
        |e M * A M| +
          ∑ n ∈ Finset.Icc 1 (M - 1), |e n * (A n - A (n + 1))| := by
      exact (abs_add_le _ _).trans
        (add_le_add_right (Finset.abs_sum_le_sum_abs _ _) _)
    _ ≤ K * ((M : ℝ) + 1) * c +
        ∑ n ∈ Finset.Icc 1 (M - 1),
          (K * ((n : ℝ) + 1)) * (c * (2 * (M : ℝ) + 1)) := by
      apply add_le_add
      · rw [abs_mul]
        have hAM : A M = c := by
          simp [A, quadraticProfile]
        rw [hAM, abs_of_nonneg hc]
        exact mul_le_mul_of_nonneg_right (happrox M) hc
      · apply Finset.sum_le_sum
        intro n hn
        rw [abs_mul]
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have hnM : n ≤ M - 1 := (Finset.mem_Icc.mp hn).2
        have hdiffEq : A n - A (n + 1) =
            c * (2 * ((M - n : ℕ) : ℝ) + 1) := by
          simp only [A, quadraticProfile]
          have hsub1 : M + 1 - n = (M - n) + 1 := by omega
          have hsub2 : M + 1 - (n + 1) = M - n := by omega
          rw [hsub1, hsub2]
          push_cast
          ring
        have hdiff0 : 0 ≤ A n - A (n + 1) := by
          rw [hdiffEq]
          positivity
        rw [abs_of_nonneg hdiff0]
        have hdiff : A n - A (n + 1) ≤ c * (2 * (M : ℝ) + 1) := by
          rw [hdiffEq]
          have hsub : ((M - n : ℕ) : ℝ) ≤ (M : ℝ) := by
            exact_mod_cast Nat.sub_le M n
          gcongr
        exact mul_le_mul (happrox n) hdiff hdiff0
          (mul_nonneg hK (by positivity))
    _ ≤ 4 * K * c * ((M : ℝ) + 1) ^ 3 := by
      have hcardNat : (Finset.Icc 1 (M - 1)).card ≤ M := by
        calc
          (Finset.Icc 1 (M - 1)).card ≤ (Finset.range M).card :=
            Finset.card_le_card (show Finset.Icc 1 (M - 1) ⊆ Finset.range M by
              intro n hn
              exact Finset.mem_range.mpr (by
                have := (Finset.mem_Icc.mp hn).2
                omega))
          _ = M := Finset.card_range M
      have hcard : ((Finset.Icc 1 (M - 1)).card : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast hcardNat
      have hnterm : ∀ n ∈ Finset.Icc 1 (M - 1),
          K * ((n : ℝ) + 1) * (c * (2 * (M : ℝ) + 1)) ≤
            K * ((M : ℝ) + 1) * (c * (2 * (M : ℝ) + 1)) := by
        intro n hn
        have hnM : (n : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by
          have := (Finset.mem_Icc.mp hn).2
          omega : n ≤ M)
        gcongr
      have hsum := Finset.sum_le_card_nsmul _ _ _ hnterm
      rw [nsmul_eq_mul] at hsum
      have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
      have hterm0 : 0 ≤ K * ((M : ℝ) + 1) * (c * (2 * (M : ℝ) + 1)) := by
        positivity
      have hsum' :
          ∑ n ∈ Finset.Icc 1 (M - 1),
              K * ((n : ℝ) + 1) * (c * (2 * (M : ℝ) + 1)) ≤
            (M : ℝ) *
              (K * ((M : ℝ) + 1) * (c * (2 * (M : ℝ) + 1))) :=
        hsum.trans (mul_le_mul_of_nonneg_right hcard hterm0)
      nlinarith [hsum', sq_nonneg ((M : ℝ) + 1),
        mul_nonneg hK hc]

/-- Quadratic cumulative growth is stable under one increment convolution, with cubic error. -/
theorem abs_quadraticIncrementConvolution_sub_le
    {C : ℕ → ℝ} {c K : ℝ}
    (hC0 : C 0 = 0) (hCmono : Monotone C)
    (hc : 0 ≤ c) (hK : 0 ≤ K)
    (happrox : ∀ n, |C n - c * (n : ℝ) ^ 2| ≤ K * ((n : ℝ) + 1))
    (M : ℕ) :
    |quadraticIncrementConvolution C M -
        c ^ 2 * ((M : ℝ) * ((M : ℝ) + 1) *
          ((M : ℝ) ^ 2 + (M : ℝ) + 1) / 6)| ≤
      5 * K * (c + K) * ((M : ℝ) + 1) ^ 3 := by
  have happrox' : ∀ n, |C n - quadraticProfile c n| ≤ K * ((n : ℝ) + 1) := happrox
  rw [← quadraticIncrementConvolution_profile c M]
  let E₁ : ℝ := ∑ j ∈ Finset.range M,
    (C (j + 1) - C j) * (C (M - j) - quadraticProfile c (M - j))
  let E₂ : ℝ := ∑ j ∈ Finset.range M,
    ((C (j + 1) - C j) -
      (quadraticProfile c (j + 1) - quadraticProfile c j)) *
      quadraticProfile c (M - j)
  have hdecomp : quadraticIncrementConvolution C M -
      quadraticIncrementConvolution (quadraticProfile c) M = E₁ + E₂ := by
    rw [quadraticIncrementConvolution, quadraticIncrementConvolution]
    simp only [E₁, E₂]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hdecomp]
  calc
    |E₁ + E₂| ≤ |E₁| + |E₂| := abs_add_le _ _
    _ ≤ K * (c + K) * ((M : ℝ) + 1) ^ 3 +
        4 * K * c * ((M : ℝ) + 1) ^ 3 :=
      add_le_add
        (abs_increment_inner_error_sum_le hC0 hCmono hc hK happrox' M)
        (abs_increment_model_error_sum_le hC0 hc hK happrox' M)
    _ ≤ 5 * K * (c + K) * ((M : ℝ) + 1) ^ 3 := by
      have : 0 ≤ (M : ℝ) + 1 := by positivity
      nlinarith [mul_nonneg hK hc, mul_nonneg hK hK,
        pow_nonneg this 3]

end RHTower.Sieve
