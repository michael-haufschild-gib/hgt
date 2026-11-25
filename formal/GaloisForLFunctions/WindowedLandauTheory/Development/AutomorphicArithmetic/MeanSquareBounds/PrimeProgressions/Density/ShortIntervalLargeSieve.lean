import GaloisForLFunctions.BezoutValuationIncidence.LogFreeMultiplicativeLargeSieve

/-! The multiplicative large sieve on a translated interval of integers. -/

open Complex Finset RHTower RHTower.Sieve
open GaloisForLFunctions.BezoutValuationIncidence
open scoped ComplexConjugate

namespace QH.PrimeProgressions

open Classical in
/-- In the Gauss-sum transform, translating the additive polynomial multiplies it by
a unit phase. The bound therefore depends on the interval length. -/
theorem primitive_short_interval_large_sieve {Q M L : ℕ} (hQ : 2 ≤ Q)
    {S : Finset ℕ} (hS : S ⊆ Ico M (M + L)) (a : ℕ → ℂ) :
    ∑ r ∈ range Q, ∑ χ ∈ univ.filter (DirichletCharacter.IsPrimitive (R := ℂ) (n := r + 1)),
        ‖∑ n ∈ S, a n * χ (n : ZMod (r + 1))‖ ^ 2 ≤
      ((L : ℝ) + 2 * (Q : ℝ) ^ 2 - 1) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  classical
  let b (n : ℕ) : ℂ := if n ∈ S then conj (a n) else 0
  let c (k : Fin L) := b (M + k)
  have hsub : S ⊆ range (M + L) := fun n hn => mem_range.mpr (mem_Ico.mp (hS hn)).2
  have hcoef : ∑ k : Fin L, ‖c k‖ ^ 2 = ∑ n ∈ S, ‖a n‖ ^ 2 := by
    change (∑ k : Fin L, ‖b (M + (k : ℕ))‖ ^ 2) = _
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => ‖b (M + k)‖ ^ 2), range_eq_Ico]
    simp only [Nat.add_comm M]
    rw [sum_Ico_add' (f := fun n => ‖b n‖ ^ 2) 0 L M, zero_add, Nat.add_comm L M]
    rw [← sum_subset hS (fun n _ hn => by simp [b, hn])]
    exact sum_congr rfl fun n hn => by simp [b, hn]
  have hterm (r : ℕ) :
      ∑ χ ∈ univ.filter (DirichletCharacter.IsPrimitive (R := ℂ) (n := r + 1)),
          ‖∑ n ∈ S, a n * χ (n : ZMod (r + 1))‖ ^ 2 ≤
        ∑ j ∈ (Icc 1 (r + 1)).filter (fun j => Nat.Coprime j (r + 1)),
          ‖expSum L c ((j : ℝ) / ((r + 1 : ℕ) : ℝ))‖ ^ 2 := by
    have hchar (χ : DirichletCharacter ℂ (r + 1)) :
        conj (∑ n ∈ S, a n * χ (n : ZMod (r + 1))) =
        ∑ n ∈ range (M + L), b n * conj (χ (n : ZMod (r + 1))) := by
      rw [map_sum, ← sum_subset hsub (fun n _ hn => by simp [b, hn])]
      exact sum_congr rfl fun n hn => by simp [b, hn]
    have hadd (j : ℕ) :
        ∑ n ∈ range (M + L), b n * stdChar (r + 1) (n * (j : ZMod (r + 1))) =
        circleFreq ((j : ℝ) / ((r + 1 : ℕ) : ℝ)) ^ M *
          expSum L c ((j : ℝ) / ((r + 1 : ℕ) : ℝ)) := by
      let z := circleFreq ((j : ℝ) / ((r + 1 : ℕ) : ℝ))
      simp_rw [stdChar_natCast_mul]
      change (∑ n ∈ range (M + L), b n * z ^ n) = z ^ M * expSum L c _
      rw [sum_range_add]
      have hz : ∑ n ∈ range M, b n * z ^ n = 0 := by
        refine sum_eq_zero fun n hn => ?_
        have hnS : n ∉ S := fun hm => (not_le_of_gt (mem_range.mp hn)) (mem_Ico.mp (hS hm)).1
        simp [b, hnS]
      rw [hz, zero_add, expSum, sum_range, mul_sum]
      refine sum_congr rfl fun k _ => ?_
      change b (M + (k : ℕ)) * z ^ (M + (k : ℕ)) = z ^ M * (b (M + (k : ℕ)) * z ^ (k : ℕ))
      rw [pow_add, mul_left_comm]
    have hφ' : (r + 1).totient / ((r + 1 : ℕ) : ℝ) ≤ 1 :=
      (div_le_one (by positivity)).2 (by exact_mod_cast Nat.totient_le (r + 1))
    calc
      _ = ∑ χ ∈ univ.filter (DirichletCharacter.IsPrimitive (R := ℂ) (n := r + 1)),
          ‖∑ n ∈ range (M + L), b n * conj (χ (n : ZMod (r + 1)))‖ ^ 2 := by
        refine sum_congr rfl fun χ _ => ?_
        rw [← hchar, norm_conj]
      _ ≤ (r + 1).totient / ((r + 1 : ℕ) : ℝ) *
          ∑ j ∈ (Icc 1 (r + 1)).filter (fun j => Nat.Coprime j (r + 1)),
            ‖expSum L c ((j : ℝ) / ((r + 1 : ℕ) : ℝ))‖ ^ 2 := by
        have h := sum_primitive_normSq_le (r := r + 1) (M + L) b
        rw [sum_units_eq_sum_coprime] at h
        refine h.trans_eq (congrArg (fun x : ℝ => (r + 1).totient / ((r + 1 : ℕ) : ℝ) * x) ?_)
        exact sum_congr rfl fun j _ => by rw [hadd, norm_mul, norm_pow, norm_circleFreq, one_pow, one_mul]
      _ ≤ _ := mul_le_of_le_one_left (sum_nonneg fun _ _ => sq_nonneg _) hφ'
  refine (sum_le_sum (fun r _ => hterm r)).trans ?_
  rw [range_eq_Ico, sum_Ico_add' (f := fun q =>
    ∑ j ∈ (Icc 1 q).filter (fun j => Nat.Coprime j q),
      ‖expSum L c ((j : ℝ) / (q : ℝ))‖ ^ 2) 0 Q 1]
  have hI : Ico (0 + 1) (Q + 1) = Icc 1 Q := by
    ext n
    simp only [zero_add, mem_Ico, mem_Icc]
    omega
  rw [hI, ← hcoef]
  exact largeSieve_expSum_double_logFree L hQ c

end QH.PrimeProgressions
