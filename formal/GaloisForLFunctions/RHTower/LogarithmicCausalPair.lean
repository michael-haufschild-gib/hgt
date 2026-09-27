import GaloisForLFunctions.RHTower.LogarithmicMobiusReconstruction

/-!
# Square expansion of causal arithmetic pairings

For a profile vanishing at negative time, the nested arithmetic cutoff
can be replaced by a full finite square. Outside the product cutoff the
profile itself vanishes. Every signed coefficient is retained.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

theorem logarithmicWeightedDilation_pair_eq_square (a b : ℕ → ℝ) (f : ℝ → ℝ)
    (hf : ∀ t < 0, f t = 0) (T : ℝ) :
    logarithmicWeightedDilation a (logarithmicWeightedDilation b f) T =
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, ∑ m ∈ Finset.Icc 1 ⌊Real.exp T⌋₊,
        a n * b m * f (T - Real.log (n * m : ℕ)) := by
  unfold logarithmicWeightedDilation
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hcut : ⌊Real.exp (T - Real.log n)⌋₊ ≤ ⌊Real.exp T⌋₊ :=
    Nat.floor_mono (Real.exp_le_exp.mpr (sub_le_self T hlogn))
  have hs : Finset.Icc 1 ⌊Real.exp (T - Real.log n)⌋₊ ⊆ Finset.Icc 1 ⌊Real.exp T⌋₊ := by
    intro m hm
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hm).1, (Finset.mem_Icc.mp hm).2.trans hcut⟩
  have he : (∑ m ∈ Finset.Icc 1 ⌊Real.exp (T - Real.log n)⌋₊,
      b m * f (T - Real.log n - Real.log m)) =
      ∑ m ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, b m * f (T - Real.log n - Real.log m) := by
    apply Finset.sum_subset hs
    intro m hm hnot
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hmlow : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hgt : ⌊Real.exp (T - Real.log n)⌋₊ < m := by
      simp only [Finset.mem_Icc] at hnot
      omega
    have hegt : Real.exp (T - Real.log n) < m :=
      (Nat.floor_lt (Real.exp_pos _).le).mp hgt
    have hlog : T - Real.log n < Real.log m := (Real.lt_log_iff_exp_lt hmpos).mpr hegt
    rw [hf _ (sub_neg.mpr hlog), mul_zero]
  rw [he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  rw [Nat.cast_mul, Real.log_mul hnpos.ne' hmpos.ne', sub_sub]
  ring

end RHTower
