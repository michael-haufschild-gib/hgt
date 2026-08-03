import GaloisForLFunctions.RHTower.DeningerPushoutConcat

/-!
# Powers of a cyclically reduced element

An element of an amalgamated free product whose reduced alternating word begins and ends in
different factors has powers whose length grows linearly: the words simply concatenate.

* `deningerAbsorb` : absorbing an element of the base group into the first letter.
* `deningerLen_pow` : the length of a power.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in
theorem deningerLetterProd_append (L M : List (Σ i, G i)) :
    deningerLetterProd (φ := φ) (L ++ M) =
      deningerLetterProd (φ := φ) L * deningerLetterProd (φ := φ) M := by
  simp [deningerLetterProd, List.map_append, List.prod_append]

/-- Absorb an element of the base group into the first letter of a word. -/
def deningerAbsorb (φ : ∀ i, H →* G i) (h : H) :
    List (Σ i, G i) → List (Σ i, G i)
  | [] => []
  | p :: L => ⟨p.1, φ p.1 h * p.2⟩ :: L

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in
theorem deningerAbsorb_map_fst (h : H) (L : List (Σ i, G i)) :
    (deningerAbsorb φ h L).map Sigma.fst = L.map Sigma.fst := by
  cases L with
  | nil => rfl
  | cons p L => rfl

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in
theorem deningerAbsorb_length (h : H) (L : List (Σ i, G i)) :
    (deningerAbsorb φ h L).length = L.length := by
  cases L with
  | nil => rfl
  | cons p L => rfl

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in
theorem deningerAbsorb_reduced (h : H) (L : List (Σ i, G i))
    (hred : ∀ p ∈ L, p.2 ∉ (φ p.1).range) :
    ∀ p ∈ deningerAbsorb φ h L, p.2 ∉ (φ p.1).range := by
  cases L with
  | nil => simp [deningerAbsorb]
  | cons q L =>
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · rintro ⟨y, hy⟩
      exact hred q List.mem_cons_self ⟨(h)⁻¹ * y, by rw [map_mul, map_inv, hy]; group⟩
    · exact hred p (List.mem_cons_of_mem _ hp)

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in
theorem deningerAbsorb_isChain (h : H) (L : List (Σ i, G i))
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L) :
    List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) (deningerAbsorb φ h L) := by
  cases L with
  | nil => exact halt
  | cons q L =>
    show List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) (⟨q.1, φ q.1 h * q.2⟩ :: L)
    rw [List.isChain_cons] at halt ⊢
    exact ⟨halt.1, halt.2⟩

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in
theorem deningerBase_mul_letterProd (h : H) (L : List (Σ i, G i)) (hne : L ≠ []) :
    PushoutI.base φ h * deningerLetterProd (φ := φ) L =
      deningerLetterProd (φ := φ) (deningerAbsorb φ h L) := by
  cases L with
  | nil => exact absurd rfl hne
  | cons p L =>
    rw [deningerLetterProd_cons, deningerAbsorb, deningerLetterProd_cons, ← mul_assoc]
    congr 1
    rw [map_mul, ← PushoutI.of_apply_eq_base φ p.1 h]

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in
theorem deningerAbsorb_ne_nil (h : H) (L : List (Σ i, G i)) (hne : L ≠ []) :
    deningerAbsorb φ h L ≠ [] := by
  cases L with
  | nil => exact absurd rfl hne
  | cons p L => simp [deningerAbsorb]

/-- **The length of a power of a cyclically reduced element.**  If the reduced alternating word
begins and ends in different factors, the words of the powers are the concatenations, so the length
grows linearly. -/
theorem deningerLen_pow (L : List (Σ i, G i)) (h : H) (n : ℕ)
    (hne : L ≠ [])
    (hred : ∀ p ∈ L, p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L)
    (hcyc : ∀ p ∈ L.getLast?, ∀ q ∈ L.head?, p.1 ≠ q.1) :
    deningerLen d ((deningerLetterProd (φ := φ) L * PushoutI.base φ h) ^ (n + 1)) =
      (n + 1) * L.length := by
  have hfstbase : ((PushoutI.base φ h • (NormalWord.empty : NormalWord d)) : NormalWord d).fstIdx
      = none := by
    rw [NormalWord.base_smul_def]
    rfl
  have habsHead : (deningerAbsorb φ h L).head?.map Sigma.fst = L.head?.map Sigma.fst := by
    rw [← List.head?_map, ← List.head?_map, deningerAbsorb_map_fst]
  have habsLast : (deningerAbsorb φ h L).getLast?.map Sigma.fst = L.getLast?.map Sigma.fst := by
    rw [← List.getLast?_map, ← List.getLast?_map, deningerAbsorb_map_fst]
  have key : ∀ m : ℕ, ∃ K : List (Σ i, G i),
      K ≠ [] ∧ K.length = (m + 1) * L.length ∧
      (∀ p ∈ K, p.2 ∉ (φ p.1).range) ∧
      List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) K ∧
      K.head?.map Sigma.fst = L.head?.map Sigma.fst ∧
      K.getLast?.map Sigma.fst = L.getLast?.map Sigma.fst ∧
      (deningerLetterProd (φ := φ) L * PushoutI.base φ h) ^ (m + 1) =
        deningerLetterProd (φ := φ) K * PushoutI.base φ h := by
    intro m
    induction m with
    | zero => exact ⟨L, hne, by omega, hred, halt, rfl, rfl, by rw [pow_one]⟩
    | succ m ih =>
      obtain ⟨K, hKne, hKlen, hKred, hKalt, hKhead, hKlast, hKeq⟩ := ih
      refine ⟨K ++ deningerAbsorb φ h L, by simp [hKne], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.length_append, hKlen, deningerAbsorb_length]
        ring
      · intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact hKred p hp
        · exact deningerAbsorb_reduced h L hred p hp
      · refine List.isChain_append.2 ⟨hKalt, deningerAbsorb_isChain h L halt, ?_⟩
        intro x hx y hy
        rw [Option.mem_def] at hx hy
        have hx' : L.getLast?.map Sigma.fst = some x.1 := by rw [← hKlast, hx]; rfl
        have hy' : L.head?.map Sigma.fst = some y.1 := by rw [← habsHead, hy]; rfl
        obtain ⟨p, hp, hpx⟩ := Option.map_eq_some_iff.1 hx'
        obtain ⟨q, hq, hqy⟩ := Option.map_eq_some_iff.1 hy'
        rw [← hpx, ← hqy]
        exact hcyc p hp q hq
      · rw [List.head?_append_of_ne_nil _ hKne, hKhead]
      · obtain ⟨z, hz⟩ : ∃ z, (deningerAbsorb φ h L).getLast? = some z := by
          cases hL : (deningerAbsorb φ h L).getLast? with
          | none => exact absurd (List.getLast?_eq_none_iff.1 hL) (deningerAbsorb_ne_nil h L hne)
          | some z => exact ⟨z, rfl⟩
        rw [List.getLast?_append, ← habsLast, hz]
        simp
      · rw [pow_succ, hKeq, deningerLetterProd_append,
          ← deningerBase_mul_letterProd h L hne]
        group
  obtain ⟨K, _, hKlen, hKred, hKalt, _, _, hKeq⟩ := key n
  rw [hKeq]
  have hprep := deningerLen_prepend (d := d) K (PushoutI.base φ h) hKred hKalt
    (fun p _ => by rw [hfstbase]; simp)
  rw [hprep.1, hKlen, deningerLen_base, add_zero]

end RHTower
