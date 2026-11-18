import GaloisForLFunctions.RHTower.SelbergWeightBlockMass

/-!
# Truncating a sum with a bounded weight on the integer quotient

Below the square root there are few arguments. Above it there are few
distinct quotients, and each quotient fibre is still an interval after
truncation. A bound for all signed prefixes suffices on both halves.
-/

noncomputable section
open Finset RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem quotient_fibre (M N j : ℕ) (hj : 1 ≤ j) :
    ((Ioc M N).filter fun t => N/t=j) = Ioc (max M (N/(j+1))) (N/j) := by
  have hf := filter_fiber_eq_Ioc N (j-1) j
  rw [Nat.sub_add_cancel hj] at hf
  ext t
  have he := Finset.ext_iff.mp hf t
  simp only [mem_filter,mem_Icc,mem_Ioc,max_lt_iff] at he ⊢
  have := Nat.div_le_self N j
  omega

/-- A bounded quotient weight against bounded prefixes costs at most four
times the square root, uniformly in the lower truncation. -/
theorem abs_truncated_quotient_pair {N : ℕ} (L : ℕ) (a w : ℕ → ℝ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ t ≤ N, |∑ v ∈ Ioc 0 t, a v| ≤ A) (hw : ∀ j, |w j| ≤ B) :
    |∑ t ∈ Ioc L N, a t*w (N/t)| ≤ 4*A*B*(Nat.sqrt N : ℕ) := by
  classical
  by_cases hLN : L ≤ N
  swap
  · rw [Ioc_eq_empty_of_le (by omega),sum_empty,abs_zero]
    positivity
  let s := Nat.sqrt N
  let M := max L s
  have hM : M ≤ N := max_le hLN (Nat.sqrt_le_self N)
  have hL : L ≤ M := le_max_left ..
  have hS : s ≤ M := le_max_right ..
  have hi (l u : ℕ) (hu : u ≤ N) : |∑ t ∈ Ioc l u, a t| ≤ 2*A := by
    by_cases hlu : l ≤ u
    · have he := sum_Ioc_consecutive a (Nat.zero_le l) hlu
      rw [show (∑ t ∈ Ioc l u, a t) = (∑ t ∈ Ioc 0 u, a t)-(∑ t ∈ Ioc 0 l, a t) by linarith only [he]]
      exact (abs_sub _ _).trans (by linarith only [ha u hu,ha l (hlu.trans hu)])
    · rw [Ioc_eq_empty_of_le (by omega),sum_empty,abs_zero]
      positivity
  have small : |∑ t ∈ Ioc L M, a t*w (N/t)| ≤ (2*A*B)*s := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc _ ≤ ∑ _t ∈ Ioc L M, 2*A*B := by
              apply sum_le_sum
              intro t ht
              obtain ⟨htl,htu⟩ := mem_Ioc.mp ht
              have hs : Ioc (t-1) t = {t} := by ext v; simp only [mem_Ioc,mem_singleton]; omega
              have ht' := hi (t-1) t (htu.trans hM)
              rw [hs,sum_singleton] at ht'
              rw [abs_mul]
              exact mul_le_mul ht' (hw _) (abs_nonneg _) (by positivity)
         _ ≤ _ := by
              simp only [sum_const,Nat.card_Ioc,nsmul_eq_mul]
              rw [mul_comm]
              exact mul_le_mul_of_nonneg_left (by exact_mod_cast (by dsimp [M]; omega : M-L ≤ s)) (by positivity)
  have maps : ∀ t ∈ Ioc M N, N/t ∈ Icc 1 s := by
    intro t ht
    obtain ⟨hl,hu⟩ := mem_Ioc.mp ht
    refine mem_Icc.mpr ⟨(Nat.one_le_div_iff (by omega : 0<t)).mpr hu,?_⟩
    by_contra! h
    have hsq := Nat.mul_le_mul (show s+1 ≤ N/t by omega) (show s+1 ≤ t by omega)
    exact (Nat.not_le_of_lt (Nat.lt_succ_sqrt N)) (hsq.trans (Nat.div_mul_le_self N t))
  have big : |∑ t ∈ Ioc M N, a t*w (N/t)| ≤ (2*A*B)*s := by
    rw [←sum_fiberwise_of_maps_to maps]
    apply (abs_sum_le_sum_abs _ _).trans
    calc _ ≤ ∑ _j ∈ Icc 1 s, 2*A*B := by
              apply sum_le_sum
              intro j hj
              let S := (Ioc M N).filter (fun t => N/t=j)
              have he : (∑ t ∈ S, a t*w (N/t)) = (∑ t ∈ S, a t)*w j := by
                rw [sum_mul]
                exact sum_congr rfl fun t ht => by rw [(mem_filter.mp ht).2]
              rw [he,abs_mul]
              dsimp [S]
              rw [quotient_fibre M N j (mem_Icc.mp hj).1]
              exact mul_le_mul (hi _ _ (Nat.div_le_self ..)) (hw _) (abs_nonneg _) (by positivity)
         _ = _ := by simp [mul_comm]
  rw [←sum_Ioc_consecutive (fun t => a t*w (N/t)) hL hM]
  apply (abs_add_le _ _).trans
  linarith only [small,big]

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
