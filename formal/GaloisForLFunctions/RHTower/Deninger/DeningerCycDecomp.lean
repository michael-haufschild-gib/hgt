import GaloisForLFunctions.RHTower.Deninger.DeningerCycBase

/-!
# Decomposing a word that is not cyclically reduced

A reduced alternating word of length at least two whose first and last letters lie in the same
factor is a first letter, a middle, and a last letter in that factor, with the middle nonempty.

* `deningerNotCycRed_decomp` : the decomposition.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

omit [∀ i, Group (G i)] in
/-- **The decomposition.** -/
theorem deningerNotCycRed_decomp (L : List (Σ i, G i)) (hne : L ≠ [])
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L)
    (hlen : ¬ L.length ≤ 1)
    (hcyc : ¬ ∀ p ∈ L.getLast?, ∀ q ∈ L.head?, p.1 ≠ q.1) :
    ∃ (j : ι) (z y : G j) (M : List (Σ i, G i)), M ≠ [] ∧
      L = (⟨j, z⟩ : Σ i, G i) :: (M ++ [(⟨j, y⟩ : Σ i, G i)]) := by
  classical
  push Not at hcyc
  obtain ⟨r, hr, q, hq, hqr⟩ := hcyc
  rw [Option.mem_def] at hr hq
  obtain ⟨Ltl, hLtl⟩ : ∃ Ltl, L = q :: Ltl := by
    cases L with
    | nil => exact absurd rfl hne
    | cons a L'' =>
      rw [List.head?_cons, Option.some.injEq] at hq
      exact ⟨L'', by rw [hq]⟩
  have hLtlne : Ltl ≠ [] := by
    intro hnil
    rw [hLtl, hnil] at hlen
    simp at hlen
  have hrtl : Ltl.getLast? = some r := by
    rw [hLtl, List.getLast?_cons_of_ne_nil hLtlne] at hr
    exact hr
  obtain ⟨M, hM⟩ : ∃ M, Ltl = M ++ [r] :=
    ⟨Ltl.dropLast, (List.dropLast_append_getLast? _ hrtl).symm⟩
  obtain ⟨j, z⟩ := q
  obtain ⟨i, y⟩ := r
  simp only at hqr
  subst hqr
  refine ⟨i, z, y, M, ?_, by rw [hLtl, hM]⟩
  intro hnil
  rw [hLtl, hM, hnil, List.nil_append, List.isChain_cons] at halt
  exact halt.1 (⟨i, y⟩ : Σ i, G i) (by simp) rfl

end RHTower
