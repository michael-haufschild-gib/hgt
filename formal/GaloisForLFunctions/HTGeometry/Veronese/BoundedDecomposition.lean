import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Integral decomposition of bounded degree vectors

Lin–Zhang, arXiv:2611.05915, Lemma 5.2: a degree `k * s` vector bounded
by `k * b` splits into `k` degree-`s` vectors bounded by `b`.
The proof selects one row between the necessary lower and upper bounds,
then applies induction. It also includes the empty decomposition `k = 0`.
-/

namespace GaloisForLFunctions.VeroneseIdeal

open Finset

variable {ι : Type*} [DecidableEq ι]

private theorem exists_bounded_sum (S : Finset ι) (u : ι → ℕ) (n : ℕ)
    (hn : n ≤ ∑ i ∈ S, u i) :
    ∃ f : ι → ℕ, (∀ i, f i ≤ u i) ∧ ∑ i ∈ S, f i = n := by
  induction S using Finset.induction generalizing n with
  | empty =>
      refine ⟨fun _ => 0, fun _ => Nat.zero_le _, ?_⟩
      simpa using hn
  | @insert a S ha ih =>
      have hrem : n - min (u a) n ≤ ∑ i ∈ S, u i := by
        rw [sum_insert ha] at hn
        omega
      obtain ⟨f, hf, hsum⟩ := ih (n - min (u a) n) hrem
      refine ⟨Function.update f a (min (u a) n), ?_, ?_⟩
      · intro i
        by_cases hi : i = a
        · subst i; simp only [Function.update_same]; exact min_le_left _ _
        · simpa only [Function.update_of_ne hi] using hf i
      · rw [sum_insert ha, Function.update_same]
        have hS : ∑ i ∈ S, Function.update f a (min (u a) n) i = ∑ i ∈ S, f i := by
          apply sum_congr rfl
          intro i hi
          exact Function.update_of_ne (ne_of_mem_of_not_mem hi ha) _ _
        rw [hS, hsum]
        omega

private theorem exists_sum_between [Fintype ι] (l u : ι → ℕ) (s : ℕ)
    (hlu : ∀ i, l i ≤ u i) (hl : (∑ i, l i) ≤ s) (hu : s ≤ ∑ i, u i) :
    ∃ a : ι → ℕ, (∀ i, l i ≤ a i ∧ a i ≤ u i) ∧ ∑ i, a i = s := by
  have hcap : s - ∑ i, l i ≤ ∑ i, (u i - l i) := by
    rw [Finset.sum_tsub_distrib (fun i _ => hlu i)]
    omega
  obtain ⟨f, hf, hsum⟩ := exists_bounded_sum univ (fun i => u i - l i)
    (s - ∑ i, l i) hcap
  refine ⟨fun i => l i + f i, ?_, ?_⟩
  · intro i
    have := hf i
    have := hlu i
    omega
  · rw [sum_add_distrib, hsum]
    omega

/-- Exact integral decomposition criterion for a box intersected with a degree hyperplane. -/
theorem bounded_degree_decomposition_iff [Fintype ι] (k s : ℕ) (b α : ι → ℕ) :
    ((∑ i, α i) = k * s ∧ ∀ i, α i ≤ k * b i) ↔
      ∃ β : Fin k → ι → ℕ,
        (∀ j, (∑ i, β j i) = s) ∧
        (∀ j i, β j i ≤ b i) ∧
        ∀ i, (∑ j, β j i) = α i := by
  constructor
  · intro h
    induction k generalizing α with
    | zero =>
        refine ⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j, ?_⟩
        intro i
        have hi := h.2 i
        simpa using hi.symm
    | succ k ih =>
        let l : ι → ℕ := fun i => α i - k * b i
        let u : ι → ℕ := fun i => min (α i) (b i)
        have hlu : ∀ i, l i ≤ u i := by
          intro i
          have hi := h.2 i
          dsimp [l, u]
          rw [Nat.succ_mul] at hi
          omega
        have hlow : ∀ i, (k + 1) * l i ≤ α i := by
          intro i
          have hi := h.2 i
          dsimp [l]
          by_cases hi' : α i ≤ k * b i
          · rw [Nat.sub_eq_zero_of_le hi']; simp
          · have hsub := Nat.sub_add_cancel (Nat.le_of_lt (Nat.lt_of_not_ge hi'))
            have hmul := Nat.mul_le_mul_left k hi
            nlinarith only [hsub, hmul]
        have hupp : ∀ i, α i ≤ (k + 1) * u i := by
          intro i
          have hi := h.2 i
          dsimp [u]
          by_cases hi' : α i ≤ b i
          · rw [min_eq_left hi']
            nlinarith only [Nat.zero_le (k * α i)]
          · rw [min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge hi'))]
            exact hi
        have hl : (∑ i, l i) ≤ s := by
          have hh := sum_le_sum (fun i (_ : i ∈ (univ : Finset ι)) => hlow i)
          rw [← mul_sum, h.1] at hh
          exact Nat.le_of_mul_le_mul_left hh (by omega)
        have hu : s ≤ ∑ i, u i := by
          have hh := sum_le_sum (fun i (_ : i ∈ (univ : Finset ι)) => hupp i)
          rw [← mul_sum, h.1] at hh
          exact Nat.le_of_mul_le_mul_left hh (by omega)
        obtain ⟨a, ha, has⟩ := exists_sum_between l u s hlu hl hu
        have haα : ∀ i, a i ≤ α i := fun i => (ha i).2.trans (min_le_left _ _)
        have hrest : (∑ i, (α i - a i)) = k * s ∧
            ∀ i, α i - a i ≤ k * b i := by
          constructor
          · rw [Finset.sum_tsub_distrib (fun i _ => haα i), h.1, has, Nat.succ_mul]
            omega
          · intro i
            have hi := (ha i).1
            dsimp [l] at hi
            omega
        obtain ⟨β, hβs, hβb, hβα⟩ := ih (fun i => α i - a i) hrest
        refine ⟨Fin.cons a β, ?_, ?_, ?_⟩
        · intro j
          refine Fin.cases ?_ (fun j => ?_) j
          · exact has
          · exact hβs j
        · intro j i
          refine Fin.cases ?_ (fun j => ?_) j
          · exact (ha i).2.trans (min_le_right _ _)
          · exact hβb j i
        · intro i
          rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ, hβα]
          exact Nat.add_sub_of_le (haα i)
  · rintro ⟨β, hβs, hβb, hβα⟩
    constructor
    · simp only [← hβα, sum_comm (f := fun i j => β j i), hβs,
        sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    · intro i
      rw [← hβα i]
      calc
        (∑ j, β j i) ≤ ∑ _ : Fin k, b i := sum_le_sum fun j _ => hβb j i
        _ = k * b i := by simp

end GaloisForLFunctions.VeroneseIdeal
