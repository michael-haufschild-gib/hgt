import GaloisForLFunctions.RHTower.LogarithmicCausalPair

/-!
# Fixed horizons for causal arithmetic pairings

A causal pair may be expanded on any square containing its time-dependent
cutoff. This lets one use a single finite square on an entire time window.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

theorem causalProfile_mul_shift_eq_zero (f : ℝ → ℝ) (hf : ∀ t < 0, f t = 0)
    {T : ℝ} {n m : ℕ} (hn : ⌊Real.exp T⌋₊ < n) (hm : 1 ≤ m) :
    f (T - Real.log (n * m : ℕ)) = 0 := by
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn
  have habpos : (0 : ℝ) < (n * m : ℕ) := by
    exact_mod_cast Nat.mul_pos hnpos (lt_of_lt_of_le Nat.zero_lt_one hm)
  have he : Real.exp T < n := (Nat.floor_lt (Real.exp_pos T).le).mp hn
  have hprod : (n : ℝ) ≤ (n * m : ℕ) := by
    exact_mod_cast (show n ≤ n * m by simpa using Nat.mul_le_mul_left n hm)
  exact hf _ (sub_neg.mpr ((Real.lt_log_iff_exp_lt habpos).mpr (he.trans_le hprod)))

theorem logarithmicWeightedDilation_pair_eq_square_of_horizon
    (a b : ℕ → ℝ) (f : ℝ → ℝ) (hf : ∀ t < 0, f t = 0)
    {T : ℝ} {N : ℕ} (hN : ⌊Real.exp T⌋₊ ≤ N) :
    logarithmicWeightedDilation a (logarithmicWeightedDilation b f) T =
      ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
        a n * b m * f (T - Real.log (n * m : ℕ)) := by
  rw [logarithmicWeightedDilation_pair_eq_square a b f hf T]
  have hsub : Finset.Icc 1 ⌊Real.exp T⌋₊ ⊆ Finset.Icc 1 N := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans hN⟩
  have hi (n : ℕ) (hn : 1 ≤ n) :
      (∑ m ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, a n * b m * f (T - Real.log (n * m : ℕ))) =
      ∑ m ∈ Finset.Icc 1 N, a n * b m * f (T - Real.log (n * m : ℕ)) := by
    apply Finset.sum_subset hsub
    intro m hm hnot
    have hmf : ⌊Real.exp T⌋₊ < m := by
      have := (Finset.mem_Icc.mp hm).1
      simp only [Finset.mem_Icc] at hnot
      omega
    rw [Nat.mul_comm n m, causalProfile_mul_shift_eq_zero f hf hmf hn, mul_zero]
  calc
    _ = ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, ∑ m ∈ Finset.Icc 1 N,
        a n * b m * f (T - Real.log (n * m : ℕ)) :=
      Finset.sum_congr rfl (fun n hn => hi n (Finset.mem_Icc.mp hn).1)
    _ = _ := by
      apply Finset.sum_subset hsub
      intro n hn hnot
      have hnf : ⌊Real.exp T⌋₊ < n := by
        have := (Finset.mem_Icc.mp hn).1
        simp only [Finset.mem_Icc] at hnot
        omega
      apply Finset.sum_eq_zero
      intro m hm
      rw [causalProfile_mul_shift_eq_zero f hf hnf (Finset.mem_Icc.mp hm).1, mul_zero]

end RHTower
