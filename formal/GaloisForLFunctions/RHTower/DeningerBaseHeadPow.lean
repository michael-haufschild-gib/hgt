import GaloisForLFunctions.RHTower.DeningerBaseConjWord
import GaloisForLFunctions.RHTower.DeningerCycRedPowInj

/-!
# Powers of a cyclically reduced element with a base head

A general element whose normal word is cyclically reduced is a base group element times a
cyclically reduced transversal word.  Its powers are again of that shape: multiplying the word on
the right by a base element and renormalizing shifts the letters and produces a new base element on
the left, so each further power prepends one block of the same length and leaves the blocks already
produced untouched.  In particular the last block of the `n`-th power is the word itself.

* `deningerCyc_of_map_fst_cross` : the cyclic condition compared across two words.
* `deningerShift_transversal` : moving a base element from the right of a word to its left.
* `deningerBaseHead_pow_word` : the block form of a power.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

omit [∀ i, Group (G i)] [DecidableEq ι] [∀ i, DecidableEq (G i)] in
/-- **The cyclic condition compared across two words** whose ends match those of a cyclically
reduced one. -/
theorem deningerCyc_of_map_fst_cross (M A B : List (Σ i, G i))
    (hA : A.map Sigma.fst = M.map Sigma.fst)
    (hB : B.head?.map Sigma.fst = M.head?.map Sigma.fst)
    (hcyc : ∀ p ∈ M.getLast?, ∀ q ∈ M.head?, p.1 ≠ q.1) :
    ∀ p ∈ A.getLast?, ∀ q ∈ B.head?, p.1 ≠ q.1 := by
  intro p hp q hq
  have h1 : A.getLast?.map Sigma.fst = M.getLast?.map Sigma.fst := by
    rw [← List.getLast?_map, ← List.getLast?_map, hA]
  rw [Option.mem_def] at hp hq
  rw [hp] at h1
  rw [hq] at hB
  cases hM : M.getLast? with
  | none => rw [hM] at h1; simp at h1
  | some p' =>
    cases hM' : M.head? with
    | none => rw [hM'] at hB; simp at hB
    | some q' =>
      rw [hM] at h1
      rw [hM'] at hB
      have hp1 : p.1 = p'.1 := by simpa using h1
      have hq1 : q.1 = q'.1 := by simpa using hB
      rw [hp1, hq1]
      exact hcyc p' (by rw [hM]; rfl) q' (by rw [hM']; rfl)

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in
include d in
/-- **Moving a base element from the right of a word to its left.**  The letters shift and a new
base element appears on the left; the sequence of factors is unchanged. -/
theorem deningerShift_transversal (M : List (Σ i, G i)) (hMne : M ≠ [])
    (hMred : ∀ p ∈ M, p.2 ∉ (φ p.1).range) (a : H) :
    ∃ (a' : H) (M' : List (Σ i, G i)), M'.map Sigma.fst = M.map Sigma.fst ∧
      (∀ p ∈ M', p.2 ∈ d.set p.1) ∧ (∀ p ∈ M', p.2 ∉ (φ p.1).range) ∧
      deningerLetterProd (φ := φ) M * PushoutI.base φ a =
        PushoutI.base φ a' * deningerLetterProd (φ := φ) M' := by
  classical
  obtain ⟨N, q, hM⟩ : ∃ N q, M = N ++ [q] := by
    obtain ⟨w, hw⟩ : ∃ w, M.getLast? = some w := by
      cases hMg : M.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.1 hMg) hMne
      | some w => exact ⟨w, rfl⟩
    exact ⟨M.dropLast, w, (List.dropLast_append_getLast? _ hw).symm⟩
  subst hM
  set M₁ : List (Σ i, G i) := N ++ [(⟨q.1, q.2 * φ q.1 a⟩ : Σ i, G i)] with hM₁
  have hM₁red : ∀ p ∈ M₁, p.2 ∉ (φ p.1).range := deningerAbsorbRight_reduced N q a hMred
  obtain ⟨a', M', hmap, hset, hred, heq⟩ :=
    deningerExists_transversal_form (d := d) M₁ hM₁red
  refine ⟨a', M', ?_, hset, hred, ?_⟩
  · rw [hmap, hM₁, deningerAbsorbRight_map_fst]
  · rw [deningerLetterProd_mul_base_snoc N q a, ← hM₁, heq]

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in
include d in
/-- **The block form of a power.**  A power of a base element times a cyclically reduced transversal
word is a base element times a word which ends in that word and is one block longer for each
further power. -/
theorem deningerBaseHead_pow_word (M : List (Σ i, G i)) (hMne : M ≠ [])
    (hMset : ∀ p ∈ M, p.2 ∈ d.set p.1) (hMred : ∀ p ∈ M, p.2 ∉ (φ p.1).range)
    (hMalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) M)
    (hMcyc : ∀ p ∈ M.getLast?, ∀ q ∈ M.head?, p.1 ≠ q.1) (j : H) (n : ℕ) :
    ∃ (h : H) (N : List (Σ i, G i)),
      N.length = n * M.length ∧
      (∀ p ∈ N ++ M, p.2 ∈ d.set p.1) ∧
      (∀ p ∈ N ++ M, p.2 ∉ (φ p.1).range) ∧
      List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) (N ++ M) ∧
      (N ++ M).head?.map Sigma.fst = M.head?.map Sigma.fst ∧
      (PushoutI.base φ j * deningerLetterProd (φ := φ) M) ^ (n + 1) =
        PushoutI.base φ h * deningerLetterProd (φ := φ) (N ++ M) := by
  classical
  induction n with
  | zero =>
    refine ⟨j, [], by simp, by simpa using hMset, by simpa using hMred, by simpa using hMalt,
      by simp, by simp⟩
  | succ n ih =>
    obtain ⟨h, N, hlen, hset, hred, halt, hhead, heq⟩ := ih
    obtain ⟨h', M', hmap', hset', hred', hshift⟩ :=
      deningerShift_transversal (d := d) M hMne hMred h
    have hM'ne : M' ≠ [] := by
      intro hnil
      have := congrArg List.length hmap'
      rw [hnil] at this
      simp only [List.map_nil, List.length_nil, List.length_map] at this
      exact hMne (List.length_eq_zero_iff.1 this.symm)
    have halt' : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) M' :=
      deningerIsChain_of_map_fst M M' hmap' hMalt
    have hjunc : ∀ p ∈ M'.getLast?, ∀ q ∈ (N ++ M).head?, p.1 ≠ q.1 :=
      deningerCyc_of_map_fst_cross M M' (N ++ M) hmap' hhead hMcyc
    refine ⟨j * h', M' ++ N, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.length_append, hlen]
      have : M'.length = M.length := by
        have := congrArg List.length hmap'
        simpa using this
      rw [this]
      ring
    · rw [List.append_assoc]
      intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact hset' p hp
      · exact hset p hp
    · rw [List.append_assoc]
      intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact hred' p hp
      · exact hred p hp
    · rw [List.append_assoc]
      exact List.isChain_append.2 ⟨halt', halt, hjunc⟩
    · rw [List.append_assoc, List.head?_append_of_ne_nil _ hM'ne, ← List.head?_map,
        ← List.head?_map, hmap']
    · rw [pow_succ', heq, ← mul_assoc, mul_assoc (PushoutI.base φ j), hshift, List.append_assoc]
      simp only [deningerLetterProd_append, map_mul]
      group

end RHTower
