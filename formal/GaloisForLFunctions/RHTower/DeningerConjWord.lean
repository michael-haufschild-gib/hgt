import GaloisForLFunctions.RHTower.DeningerWordMerge

/-!
# The normal word of a conjugated power

If a conjugator, a cyclically reduced word and a second conjugator meet without cancellation, then
the normal word of the corresponding conjugated power is the plain concatenation.

* `deningerFlatten_getLast` : the last letter of a concatenation of copies.
* `deningerNormalWord_conj_pow` : the normal word of `C · Lᵏ · D`.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

omit [∀ i, Group (G i)] [DecidableEq ι] [∀ i, DecidableEq (G i)] in
theorem deningerFlatten_getLast (L : List (Σ i, G i)) (hne : L ≠ []) (n : ℕ) :
    (deningerFlatten (G := G) L (n + 1)).getLast? = L.getLast? := by
  induction n with
  | zero => simp [deningerFlatten]
  | succ n ih =>
    rw [deningerFlatten_succ, List.getLast?_append, ih]
    cases hL : L.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.1 hL) hne
    | some z => simp

/-- **The normal word of a conjugated power.**  If the junctions do not cancel, the normal word of
`C · Lᵏ · D` is the concatenation. -/
theorem deningerNormalWord_conj_pow (C L D : List (Σ i, G i)) (k : ℕ) (hk : 0 < k)
    (hLne : L ≠ [])
    (hCset : ∀ p ∈ C, p.2 ∈ d.set p.1) (hCred : ∀ p ∈ C, p.2 ∉ (φ p.1).range)
    (hCalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) C)
    (hLset : ∀ p ∈ L, p.2 ∈ d.set p.1) (hLred : ∀ p ∈ L, p.2 ∉ (φ p.1).range)
    (hLalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L)
    (hLcyc : ∀ p ∈ L.getLast?, ∀ q ∈ L.head?, p.1 ≠ q.1)
    (hDset : ∀ p ∈ D, p.2 ∈ d.set p.1) (hDred : ∀ p ∈ D, p.2 ∉ (φ p.1).range)
    (hDalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) D)
    (hCL : ∀ p ∈ C.getLast?, ∀ q ∈ L.head?, p.1 ≠ q.1)
    (hLD : ∀ p ∈ L.getLast?, ∀ q ∈ D.head?, p.1 ≠ q.1) :
    ((deningerLetterProd (φ := φ) C * (deningerLetterProd (φ := φ) L) ^ k *
        deningerLetterProd (φ := φ) D) • (NormalWord.empty : NormalWord d)).toList =
      C ++ (deningerFlatten (G := G) L k ++ D) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hprod : deningerLetterProd (φ := φ) C * (deningerLetterProd (φ := φ) L) ^ (m + 1) *
      deningerLetterProd (φ := φ) D =
      deningerLetterProd (φ := φ) (C ++ (deningerFlatten (G := G) L (m + 1) ++ D)) := by
    rw [deningerLetterProd_append, deningerLetterProd_append, deningerLetterProd_flatten,
      mul_assoc]
  have hFset : ∀ p ∈ deningerFlatten (G := G) L (m + 1), p.2 ∈ d.set p.1 :=
    fun p hp => hLset p (deningerFlatten_mem L (m + 1) p hp)
  have hFred : ∀ p ∈ deningerFlatten (G := G) L (m + 1), p.2 ∉ (φ p.1).range :=
    fun p hp => hLred p (deningerFlatten_mem L (m + 1) p hp)
  have hFalt := deningerFlatten_isChain L hLalt hLcyc (m + 1)
  have hFhead := deningerFlatten_head L m hLne
  have hFlast := deningerFlatten_getLast L hLne m
  have haltFD : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1)
      (deningerFlatten (G := G) L (m + 1) ++ D) := by
    refine List.isChain_append.2 ⟨hFalt, hDalt, ?_⟩
    intro x hx y hy
    rw [Option.mem_def, hFlast] at hx
    exact hLD x hx y hy
  have haltAll : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1)
      (C ++ (deningerFlatten (G := G) L (m + 1) ++ D)) := by
    refine List.isChain_append.2 ⟨hCalt, haltFD, ?_⟩
    intro x hx y hy
    rw [Option.mem_def, List.head?_append_of_ne_nil _ ?_, hFhead] at hy
    · exact hCL x hx y hy
    · intro hnil
      have hlen := deningerFlatten_length (G := G) L (m + 1)
      rw [hnil] at hlen
      simp only [List.length_nil] at hlen
      have : L.length = 0 := by
        rcases Nat.mul_eq_zero.1 hlen.symm with h | h
        · omega
        · exact h
      exact hLne (List.length_eq_zero_iff.1 this)
  rw [hprod]
  exact (deningerNormalWord_letterProd _
    (by
      intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact hCset p hp
      · rcases List.mem_append.1 hp with hp | hp
        · exact hFset p hp
        · exact hDset p hp)
    (by
      intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact hCred p hp
      · rcases List.mem_append.1 hp with hp | hp
        · exact hFred p hp
        · exact hDred p hp)
    haltAll).1

end RHTower
