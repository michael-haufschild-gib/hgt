import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheDivisorBoundControlsResonatorEnergy

/-!
# Weighted energy of a truncated resonator

The sharp Dirichlet mean-value theorem charges the coefficient at `k`
by `k`. Splitting this factor along `k = mn` gives a support cost
`m^(1+ε)` and the subcritical zeta kernel `n^(1+ε-2σ)`.
-/

noncomputable section
open Real Finset Filter Topology
open _root_.RHTower

namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

/-- The factor charged by the sharp mean-value theorem separates on each fibre. -/
theorem weighted_truncResonatorCoeff_sq_le {ε σ : ℝ} (hε : 0 < ε)
    (hεσ : ε < 2 * σ - 1) (A : Finset ℕ) (r : ℕ → ℂ) (N k : ℕ) :
    (k : ℝ) * ‖truncResonatorCoeff A r σ N k‖ ^ 2 ≤
      Sieve.divisorBoundConst ε * ∑ m ∈ A,
        (‖r m‖ ^ 2 * (m : ℝ) ^ (1 + ε)) *
          (if m ∣ k then (if k / m ≤ N then
            ((k / m : ℕ) : ℝ) ^ (1 + ε - 2 * σ) else 0) else 0) := by
  classical
  rcases eq_or_ne k 0 with rfl | hk
  · simp only [Nat.cast_zero, zero_mul]
    apply mul_nonneg (Sieve.divisorBoundConst_pos hε).le
    exact Finset.sum_nonneg fun m _ => mul_nonneg (by positivity)
      (by split_ifs <;> positivity)
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  have hbound := mul_le_mul_of_nonneg_left
    (norm_truncResonatorCoeff_sq_le_divisor_weight hε A r σ N hk) hkR.le
  apply hbound.trans_eq
  calc
    _ = Sieve.divisorBoundConst ε *
        ∑ m ∈ A.filter (fun m => m ∣ k ∧ k / m ≤ N),
          (‖r m‖ ^ 2 * (m : ℝ) ^ (1 + ε)) *
            ((k / m : ℕ) : ℝ) ^ (1 + ε - 2 * σ) := by
      rw [show (k : ℝ) * (Sieve.divisorBoundConst ε * (k : ℝ) ^ ε *
          ∑ m ∈ A.filter (fun m => m ∣ k ∧ k / m ≤ N),
            ‖r m‖ ^ 2 * ((k / m : ℕ) : ℝ) ^ (-2 * σ)) =
        Sieve.divisorBoundConst ε * ((k : ℝ) ^ (1 + ε) *
          ∑ m ∈ A.filter (fun m => m ∣ k ∧ k / m ≤ N),
            ‖r m‖ ^ 2 * ((k / m : ℕ) : ℝ) ^ (-2 * σ)) by
          rw [Real.rpow_add hkR, Real.rpow_one]; ring,
        Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro m hm
      have hd := (Finset.mem_filter.mp hm).2.1
      have hm0 : m ≠ 0 := by
        intro h
        subst m
        obtain ⟨n, hn⟩ := hd
        exact hk (by simpa only [zero_mul] using hn)
      calc
        _ = ‖r m‖ ^ 2 * ((k : ℝ) ^ (1 + ε) *
            ((k / m : ℕ) : ℝ) ^ (-2 * σ)) := by ring
        _ = _ := by
          rw [weighted_divisor_rpow (by linarith only [hε] : 0 < 1 + ε)
            (by linarith only [hεσ] : 1 + ε < 2 * σ) hm0 hd]
          ring
    _ = _ := by
      congr 1
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro m _
      by_cases hd : m ∣ k <;> by_cases hn : k / m ≤ N <;> simp [hd, hn]

/-- The truncated subcritical kernel has finite support and an integral-test bound. -/
theorem tsum_truncated_rpow_le {b : ℝ} (hb0 : -1 < b) (hb1 : b < 0) (N : ℕ) :
    (∑' n : ℕ, if n ≤ N then (n : ℝ) ^ b else 0) ≤
      (N : ℝ) ^ (1 + b) / (1 + b) + 1 := by
  have heq : (∑' n : ℕ, if n ≤ N then (n : ℝ) ^ b else 0) =
      ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ b := by
    rw [tsum_eq_sum (s := Finset.Icc 1 N)]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [if_pos (Finset.mem_Icc.mp hn).2]
    · intro n hn
      by_cases hn0 : n = 0
      · subst n
        simp only [Nat.cast_zero, Real.zero_rpow hb1.ne, ite_self]
      · rw [if_neg (by intro h; exact hn (Finset.mem_Icc.mpr ⟨by omega, h⟩))]
  rw [heq]
  have h := Sieve.sum_rpow_neg_subcritical_le
    (c := -b) (by linarith only [hb1]) (by linarith only [hb0]) N
  simpa only [neg_neg, sub_neg_eq_add] using h

/-- The weighted coefficient energy has the sharp polynomial support and cutoff costs. -/
theorem summable_weighted_truncResonatorCoeff_sq_and_bound {ε σ : ℝ} (hε : 0 < ε)
    (hεσ : ε < 2 * σ - 1) (hσ1 : σ < 1)
    {A : Finset ℕ} (hA : ∀ m ∈ A, m ≠ 0) (r : ℕ → ℂ) (N : ℕ) :
    Summable (fun k : ℕ => (k : ℝ) * ‖truncResonatorCoeff A r σ N k‖ ^ 2) ∧
    (∑' k : ℕ, (k : ℝ) * ‖truncResonatorCoeff A r σ N k‖ ^ 2) ≤
      Sieve.divisorBoundConst ε * (∑ m ∈ A, ‖r m‖ ^ 2 * (m : ℝ) ^ (1 + ε)) *
        ((N : ℝ) ^ (2 + ε - 2 * σ) / (2 + ε - 2 * σ) + 1) := by
  let f : ℕ → ℝ := fun n => if n ≤ N then (n : ℝ) ^ (1 + ε - 2 * σ) else 0
  have hf : Summable f := summable_of_ne_finset_zero (s := Finset.range (N + 1))
    (fun n hn => if_neg (by have := Finset.mem_range.not.mp hn; omega))
  have hmajor : Summable (fun k : ℕ => Sieve.divisorBoundConst ε * ∑ m ∈ A,
      (‖r m‖ ^ 2 * (m : ℝ) ^ (1 + ε)) * (if m ∣ k then f (k / m) else 0)) :=
    (summable_sum fun m hm =>
      (summable_multiple_kernel (hA m hm) hf).mul_left _).mul_left _
  have hpoint (k : ℕ) := weighted_truncResonatorCoeff_sq_le hε hεσ A r N k
  have hsmall : Summable (fun k : ℕ =>
      (k : ℝ) * ‖truncResonatorCoeff A r σ N k‖ ^ 2) :=
    hmajor.of_nonneg_of_le (fun k => mul_nonneg (Nat.cast_nonneg k) (sq_nonneg _)) hpoint
  refine ⟨hsmall, ?_⟩
  calc
    _ ≤ ∑' k : ℕ, Sieve.divisorBoundConst ε * ∑ m ∈ A,
        (‖r m‖ ^ 2 * (m : ℝ) ^ (1 + ε)) * (if m ∣ k then f (k / m) else 0) :=
      Summable.tsum_le_tsum hpoint hsmall hmajor
    _ = Sieve.divisorBoundConst ε *
        (∑ m ∈ A, ‖r m‖ ^ 2 * (m : ℝ) ^ (1 + ε)) * ∑' n : ℕ, f n := by
      rw [tsum_mul_left, tsum_finite_multiple_kernels hA _ hf]
      exact (mul_assoc _ _ _).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (Sieve.divisorBoundConst_pos hε).le (by positivity))
      have h := tsum_truncated_rpow_le (b := 1 + ε - 2 * σ)
        (by linarith only [hε, hσ1]) (by linarith only [hεσ]) N
      simpa only [show 1 + (1 + ε - 2 * σ) = 2 + ε - 2 * σ by ring] using h

#print axioms weighted_truncResonatorCoeff_sq_le
#print axioms summable_weighted_truncResonatorCoeff_sq_and_bound

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
