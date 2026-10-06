import GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimePairs

/-!
# The two actual gap moments paying complete hyperbolic cancellation

The actual cumulative pair sieve bounds the reciprocal-square moment at ALL
gaps and the first moment through the active square-root cutoff. Both bounds
have one cutoff-independent constant and threshold.
-/

noncomputable section

namespace RHTower

open Finset Filter Topology

private theorem reciprocal_sq_abel (f : ℕ → ℝ) (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, f d / (d : ℝ) ^ 2) =
      (1 / ((D : ℝ) + 1) ^ 2) * (∑ d ∈ Finset.Icc 1 D, f d) +
        ∑ d ∈ Finset.Icc 1 D, (1 / (d : ℝ) ^ 2 - 1 / ((d : ℝ) + 1) ^ 2) *
          (∑ k ∈ Finset.Icc 1 d, f k) := by
  have h := sum_Ioc_weight_mul_eq (fun d => (f d : ℂ))
    (fun d => ((1 / (d : ℝ) ^ 2 : ℝ) : ℂ)) (a := 0) (b := D) (Nat.zero_le D)
  have hsets : ∀ n : ℕ, Finset.Ioc 0 n = Finset.Icc 1 n := by
    intro n
    simpa using (Finset.Icc_add_one_left_eq_Ioc (0 : ℕ) n).symm
  simp only [hsets, Nat.cast_add, Nat.cast_one] at h
  apply Complex.ofReal_inj.1
  push_cast at h ⊢
  simpa [div_eq_mul_inv, mul_comm] using h

private theorem reciprocal_sq_sum_le_two (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, 1 / (d : ℝ) ^ 2) ≤ 2 := by
  have hterm {d : ℕ} (hd : 1 ≤ d) :
      1 / (d : ℝ) ^ 2 ≤ 2 * (1 / (d : ℝ) - 1 / ((d : ℝ) + 1)) := by
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hd0 : (0 : ℝ) < d := by linarith
    have hdp : (0 : ℝ) < (d : ℝ) + 1 := by positivity
    have heq : 2 * (1 / (d : ℝ) - 1 / ((d : ℝ) + 1)) =
        2 / ((d : ℝ) * ((d : ℝ) + 1)) := by field_simp; ring
    rw [heq]
    apply (div_le_div_iff₀ (sq_pos_of_pos hd0) (mul_pos hd0 hdp)).2
    nlinarith
  have htel := sum_Ioc_sub_succ (fun d => 1 / (d : ℝ)) (a := 0) (b := D) (Nat.zero_le D)
  rw [← Finset.Icc_add_one_left_eq_Ioc] at htel
  simp only [Nat.zero_add, Nat.cast_add, Nat.cast_one] at htel
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 D, 2 * (1 / (d : ℝ) - 1 / ((d : ℝ) + 1)) :=
      Finset.sum_le_sum (fun d hd => hterm (Finset.mem_Icc.1 hd).1)
    _ = 2 * (1 - 1 / ((D : ℝ) + 1)) := by
      rw [← Finset.mul_sum, htel]
      norm_num
    _ ≤ 2 := by
      have : 0 ≤ 1 / ((D : ℝ) + 1) := by positivity
      linarith

private theorem reciprocal_sq_le_of_prefix (f : ℕ → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hprefix : ∀ D : ℕ, (∑ d ∈ Finset.Icc 1 D, f d) ≤ A * D) (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, f d / (d : ℝ) ^ 2) ≤ 2 * A := by
  have hconst : ∀ n : ℕ, (∑ _k ∈ Finset.Icc 1 n, A) = A * n := by
    intro n
    simp [Finset.sum_const, Nat.card_Icc, mul_comm]
  calc
    _ = _ := reciprocal_sq_abel f D
    _ ≤ (1 / ((D : ℝ) + 1) ^ 2) * (∑ _d ∈ Finset.Icc 1 D, A) +
        ∑ d ∈ Finset.Icc 1 D, (1 / (d : ℝ) ^ 2 - 1 / ((d : ℝ) + 1) ^ 2) *
          (∑ _k ∈ Finset.Icc 1 d, A) := by
      apply add_le_add
      · rw [hconst]
        exact mul_le_mul_of_nonneg_left (hprefix D) (by positivity)
      · apply Finset.sum_le_sum
        intro d hd
        rw [hconst]
        have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.1 hd).1
        apply mul_le_mul_of_nonneg_left (hprefix d)
        apply sub_nonneg.2
        apply one_div_le_one_div_of_le (sq_pos_of_pos hd0)
        nlinarith
    _ = ∑ d ∈ Finset.Icc 1 D, A / (d : ℝ) ^ 2 := (reciprocal_sq_abel (fun _ => A) D).symm
    _ = A * (∑ d ∈ Finset.Icc 1 D, 1 / (d : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
      simp only [mul_one_div]
    _ ≤ A * 2 := mul_le_mul_of_nonneg_left (reciprocal_sq_sum_le_two D) hA
    _ = _ := mul_comm _ _

/-- Both complete actual gap moments follow from the source pair sieve, with
one constant and threshold valid at every cutoff, including zero. -/
theorem exists_chiCubicPrimeGapCount_moment_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℝ in atTop, ∀ D : ℕ,
      (∑ d ∈ Finset.Icc 1 D, chiCubicPrimeGapCount N d / (d : ℝ) ^ 2) ≤
        C * N / Real.log N ^ 2 ∧
      (∑ d ∈ Finset.Icc 1 D, chiCubicPrimeGapCount N d * (d : ℝ)) ≤
        C * (D : ℝ) ^ 2 * N / Real.log N ^ 2 := by
  obtain ⟨A, hA, hpre⟩ := exists_chiCubicPrimeGapCount_prefix_bound
  refine ⟨2 * A, by positivity, ?_⟩
  filter_upwards [hpre, eventually_gt_atTop (1 : ℝ)] with N hpreN hN
  have hN0 : 0 < N := by linarith
  intro D
  constructor
  · have hprefix : ∀ d : ℕ, (∑ k ∈ Finset.Icc 1 d, chiCubicPrimeGapCount N k) ≤
        (A * N / Real.log N ^ 2) * d := by
      intro d
      convert hpreN d using 1
      ring
    exact (reciprocal_sq_le_of_prefix _ (by positivity) hprefix D).trans_eq (by ring)
  · calc
      _ ≤ (D : ℝ) * (∑ d ∈ Finset.Icc 1 D, chiCubicPrimeGapCount N d) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro d hd
        have hdD : (d : ℝ) ≤ D := by exact_mod_cast (Finset.mem_Icc.1 hd).2
        have hP : 0 ≤ chiCubicPrimeGapCount N d := Nat.cast_nonneg _
        exact (mul_le_mul_of_nonneg_left hdD hP).trans_eq (mul_comm _ _)
      _ ≤ (D : ℝ) * (A * D * N / Real.log N ^ 2) :=
        mul_le_mul_of_nonneg_left (hpreN D) (Nat.cast_nonneg D)
      _ ≤ (D : ℝ) * ((2 * A) * D * N / Real.log N ^ 2) := by
        gcongr
        linarith
      _ = _ := by ring

end RHTower
