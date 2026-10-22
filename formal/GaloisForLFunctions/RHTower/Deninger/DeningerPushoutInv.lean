import GaloisForLFunctions.RHTower.Deninger.DeningerPushoutDecomp

/-!
# The length of a word and of an inverse

The word length of a product of a reduced alternating list of letters is the number of letters, and
inversion preserves the word length: the word of an inverse is the reversed list of inverted
letters.

* `deningerLen_letterProd` : the length of a reduced alternating word.
* `deningerInvList`, `deningerLetterProd_inv` : the word of an inverse.
* `deningerLen_inv` : inversion preserves the length.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

/-- The word length of a product of a reduced alternating list of letters is the number of
letters. -/
theorem deningerLen_letterProd (L : List (Σ i, G i))
    (hred : ∀ p ∈ L, p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L) :
    deningerLen d (deningerLetterProd (φ := φ) L) = L.length := by
  have hfst : ∀ p ∈ L.getLast?,
      (((1 : PushoutI φ) • (NormalWord.empty : NormalWord d)) : NormalWord d).fstIdx ≠ some p.1 := by
    intro p _
    rw [one_smul]
    simp [NormalWord.empty, Word.fstIdx]
  have := (deningerLen_prepend (d := d) L 1 hred halt hfst).1
  rwa [mul_one, deningerLen_one, add_zero] at this

/-- The reversed list of inverted letters. -/
def deningerInvList (L : List (Σ i, G i)) : List (Σ i, G i) :=
  (L.map (fun p => (⟨p.1, p.2⁻¹⟩ : Σ i, G i))).reverse

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in
theorem deningerInvList_length (L : List (Σ i, G i)) :
    (deningerInvList (G := G) L).length = L.length := by
  simp [deningerInvList]

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in
theorem deningerInvList_reduced (L : List (Σ i, G i))
    (hred : ∀ p ∈ L, p.2 ∉ (φ p.1).range) :
    ∀ p ∈ deningerInvList (G := G) L, p.2 ∉ (φ p.1).range := by
  intro p hp
  simp only [deningerInvList, List.mem_reverse, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  intro hmem
  exact hred q hq (by simpa using Subgroup.inv_mem _ hmem)

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in
theorem deningerInvList_isChain (L : List (Σ i, G i))
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L) :
    List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) (deningerInvList (G := G) L) := by
  rw [deningerInvList, List.isChain_reverse]
  induction L with
  | nil => simp
  | cons p L ih =>
    rw [List.map_cons, List.isChain_cons] at *
    refine ⟨?_, ih halt.2⟩
    intro y hy
    simp only [List.head?_map, Option.mem_def, Option.map_eq_some_iff] at hy
    obtain ⟨q, hq, rfl⟩ := hy
    exact (halt.1 q hq).symm

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in
theorem deningerLetterProd_inv (L : List (Σ i, G i)) :
    (deningerLetterProd (φ := φ) L)⁻¹ = deningerLetterProd (φ := φ) (deningerInvList (G := G) L) := by
  rw [deningerLetterProd, List.prod_inv_reverse, deningerLetterProd, deningerInvList,
    List.map_reverse, List.map_map, List.map_map]
  rfl

/-- **Inversion preserves the word length.** -/
theorem deningerLen_inv (g : PushoutI φ) : deningerLen d g⁻¹ = deningerLen d g := by
  rcases deningerExists_letterProd (d := d) g with ⟨h, hg, _⟩ | ⟨L, _, hred, halt, hlen, hg⟩
  · rw [hg, ← map_inv, deningerLen_base, deningerLen_base]
  · rw [hg, deningerLetterProd_inv,
      deningerLen_letterProd _ (deningerInvList_reduced L hred) (deningerInvList_isChain L halt),
      deningerInvList_length, hlen, hg]

end RHTower
