import GaloisForLFunctions.RHTower.DeningerPushoutMerge

/-!
# Cyclic reduction

Every element of an amalgamated free product is conjugate to one which either lies in a factor or
whose reduced alternating word begins and ends in different factors.  The proof conjugates by the
first letter whenever the first and last letters lie in the same factor, which shortens the word.

* `DeningerCycRed` : the property of having a cyclically reduced word.
* `deningerExists_cycRed` : cyclic reduction.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in
theorem deningerInvList_head_fst (M : List (Σ i, G i)) :
    (deningerInvList (G := G) M).head?.map Sigma.fst = M.getLast?.map Sigma.fst := by
  simp [deningerInvList, List.head?_reverse, List.getLast?_map, Function.comp_def]

/-- An element is cyclically reduced if its reduced alternating word is nonempty and begins and
ends in different factors. -/
def DeningerCycRed (φ : ∀ i, H →* G i) (g : PushoutI φ) : Prop :=
  ∃ L : List (Σ i, G i), L ≠ [] ∧ (∀ p ∈ L, p.2 ∉ (φ p.1).range) ∧
    List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L ∧
    (∀ p ∈ L.getLast?, ∀ q ∈ L.head?, p.1 ≠ q.1) ∧ g = deningerLetterProd (φ := φ) L

/-- The first letter of the normal form of a reduced alternating product. -/
theorem deningerFstIdx_letterProd (L : List (Σ i, G i))
    (hred : ∀ p ∈ L, p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L) (p : Σ i, G i)
    (hp : p ∈ L.head?) :
    (((deningerLetterProd (φ := φ) L) • (NormalWord.empty : NormalWord d)) : NormalWord d).fstIdx =
      some p.1 := by
  have hfst : ∀ q ∈ L.getLast?,
      (((1 : PushoutI φ) • (NormalWord.empty : NormalWord d)) : NormalWord d).fstIdx ≠
        some q.1 := by
    intro q _
    rw [one_smul]
    simp [NormalWord.empty, Word.fstIdx]
  have := (deningerLen_prepend (d := d) L 1 hred halt hfst).2 p hp
  rwa [mul_one] at this

/-- **Cyclic reduction.**  Every element is conjugate to one lying in a factor or having a
cyclically reduced word. -/
theorem deningerExists_cycRed (g : PushoutI φ) :
    ∃ c : PushoutI φ, deningerLen d (c⁻¹ * g * c) ≤ 1 ∨ DeningerCycRed φ (c⁻¹ * g * c) := by
  classical
  suffices Hn : ∀ n : ℕ, ∀ g : PushoutI φ, deningerLen d g ≤ n →
      ∃ c : PushoutI φ, deningerLen d (c⁻¹ * g * c) ≤ 1 ∨ DeningerCycRed φ (c⁻¹ * g * c) from
    Hn (deningerLen d g) g le_rfl
  intro n
  induction n with
  | zero =>
    intro g hg
    exact ⟨1, Or.inl (by simpa using hg.trans (by omega))⟩
  | succ n ih =>
    intro g hg
    rcases deningerExists_letterProd (d := d) g with
      ⟨h, hgb, hlen0⟩ | ⟨L, hLne, hred, halt, hlen, hgL⟩
    · exact ⟨1, Or.inl (by simpa using hlen0.le.trans (by omega))⟩
    by_cases hshort : L.length ≤ 1
    · exact ⟨1, Or.inl (by simpa using hlen ▸ hshort)⟩
    by_cases hcyc : ∀ p ∈ L.getLast?, ∀ q ∈ L.head?, p.1 ≠ q.1
    · exact ⟨1, Or.inr ⟨L, hLne, hred, halt, hcyc, by simpa using hgL⟩⟩
    push Not at hcyc
    obtain ⟨p, hp, q, hq, hpq⟩ := hcyc
    have hLcons : L = q :: L.tail := by
      cases L with
      | nil => exact absurd rfl hLne
      | cons a L'' =>
        rw [List.head?_cons, Option.mem_def] at hq
        obtain rfl : a = q := Option.some.inj hq
        rfl
    have htailne : L.tail ≠ [] := by
      intro hnil
      rw [hLcons, hnil] at hshort
      simp at hshort
    have hredT : ∀ r ∈ L.tail, r.2 ∉ (φ r.1).range := by
      intro r hr
      exact hred r (by rw [hLcons]; exact List.mem_cons_of_mem _ hr)
    have haltT : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L.tail := halt.tail
    have hlastT : L.tail.getLast? = some p := by
      rw [Option.mem_def] at hp
      have hgl := List.getLast?_cons_of_ne_nil (x := q) htailne
      rw [← hLcons] at hgl
      exact hgl.symm.trans hp
    have hgsplit : g = PushoutI.of q.1 q.2 * deningerLetterProd (φ := φ) L.tail := by
      rw [hgL]
      conv_lhs => rw [hLcons]
      rw [deningerLetterProd_cons]
    have hconj : (PushoutI.of q.1 q.2)⁻¹ * g * PushoutI.of q.1 q.2 =
        deningerLetterProd (φ := φ) L.tail * PushoutI.of q.1 q.2 := by
      rw [hgsplit]
      group
    have hinvfst : (((deningerLetterProd (φ := φ) L.tail)⁻¹ •
        (NormalWord.empty : NormalWord d)) : NormalWord d).fstIdx = some q.1 := by
      rw [deningerLetterProd_inv]
      obtain ⟨r, hr⟩ : ∃ r, (deningerInvList (G := G) L.tail).head? = some r := by
        cases hIL : (deningerInvList (G := G) L.tail).head? with
        | none =>
          refine absurd ?_ htailne
          have hnil := List.head?_eq_none_iff.1 hIL
          rwa [deningerInvList, List.reverse_eq_nil_iff, List.map_eq_nil_iff] at hnil
        | some r => exact ⟨r, rfl⟩
      have hrfst : r.1 = q.1 := by
        have := deningerInvList_head_fst (G := G) L.tail
        rw [hr, hlastT] at this
        exact (Option.some.inj this).trans hpq
      rw [deningerFstIdx_letterProd (d := d) _ (deningerInvList_reduced L.tail hredT)
        (deningerInvList_isChain L.tail haltT) r (by rw [hr]; rfl), hrfst]
    have hbound : deningerLen d ((PushoutI.of q.1 q.2)⁻¹ * g * PushoutI.of q.1 q.2) ≤ n := by
      rw [hconj]
      have h1 := deningerLen_mul_of_le (d := d) q.1 q.2 _ hinvfst
      have h2 : deningerLen d (deningerLetterProd (φ := φ) L.tail) = L.tail.length :=
        deningerLen_letterProd L.tail hredT haltT
      have h3 : L.tail.length + 1 = L.length := by
        conv_rhs => rw [hLcons]
        simp
      omega
    obtain ⟨c₁, hc₁⟩ := ih ((PushoutI.of q.1 q.2)⁻¹ * g * PushoutI.of q.1 q.2) hbound
    refine ⟨PushoutI.of q.1 q.2 * c₁, ?_⟩
    have hrw : (PushoutI.of q.1 q.2 * c₁)⁻¹ * g * (PushoutI.of q.1 q.2 * c₁) =
        c₁⁻¹ * ((PushoutI.of q.1 q.2)⁻¹ * g * PushoutI.of q.1 q.2) * c₁ := by group
    rw [hrw]
    exact hc₁

end RHTower
