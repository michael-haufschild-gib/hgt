import GaloisForLFunctions.RHTower.Deninger.DeningerHeadOnly
import GaloisForLFunctions.RHTower.Deninger.DeningerConjWord

/-!
# The length of a power

The powers of an element grow linearly in the length of its cyclically reduced part.  No transversal
hypothesis is needed: the length of a normal form, unlike its letters, is unchanged by putting a
reduced alternating word into transversal form.

* `deningerLen_conj_pow` : the length of a power.
* `deningerLen_conj_pow_sub` : the increment.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **The length of a power.**  For an element presented as a conjugate `C · V · C⁻¹` of a
cyclically reduced word, the `(k+1)`-st power has length `|C| + k·|V| + |R|`, where `R` is the tail
of the word. -/
theorem deningerLen_conj_pow (C R V : List (Σ i, G i))
    (hCRred : ∀ p ∈ C ++ R, p.2 ∉ (φ p.1).range)
    (hCRalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) (C ++ R))
    (hVne : V ≠ [])
    (hVred : ∀ p ∈ V, p.2 ∉ (φ p.1).range)
    (hValt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) V)
    (hVcyc : ∀ p ∈ V.getLast?, ∀ q ∈ V.head?, p.1 ≠ q.1)
    (hhead : V.head?.map Sigma.fst = R.head?.map Sigma.fst)
    (hprod : deningerLetterProd (φ := φ) R =
      deningerLetterProd (φ := φ) V * (deningerLetterProd (φ := φ) C)⁻¹)
    (k : ℕ) :
    deningerLen d ((deningerLetterProd (φ := φ) (C ++ R)) ^ (k + 1)) =
      C.length + k * V.length + R.length := by
  obtain ⟨hCalt, hRalt, hCR⟩ := List.isChain_append.1 hCRalt
  have htrans : ∀ q ∈ R.head?, ∃ q' ∈ V.head?, q'.1 = q.1 := by
    intro q hq
    rw [Option.mem_def] at hq
    rw [hq] at hhead
    cases hV : V.head? with
    | none => rw [hV] at hhead; simp at hhead
    | some v₀ => exact ⟨v₀, rfl, by rw [hV] at hhead; simpa using hhead⟩
  have hpow : (deningerLetterProd (φ := φ) (C ++ R)) ^ (k + 1) =
      deningerLetterProd (φ := φ) (C ++ (deningerFlatten (G := G) V k ++ R)) := by
    rw [deningerLetterProd_append, deningerLetterProd_append, deningerLetterProd_append,
      deningerLetterProd_flatten, hprod,
      ← mul_assoc (deningerLetterProd (φ := φ) C) (deningerLetterProd (φ := φ) V)
        (deningerLetterProd (φ := φ) C)⁻¹,
      ← mul_assoc (deningerLetterProd (φ := φ) C) (deningerLetterProd (φ := φ) V ^ k)]
    exact deningerConj_pow_split _ _ k
  have hflat : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1)
      (deningerFlatten (G := G) V k) := deningerFlatten_isChain V hValt hVcyc k
  have hheadFR : (deningerFlatten (G := G) V k ++ R).head?.map Sigma.fst =
      R.head?.map Sigma.fst := by
    cases k with
    | zero => simp [deningerFlatten]
    | succ m =>
      rw [List.head?_append_of_ne_nil _ (by
        intro hc
        have h := deningerFlatten_length (G := G) V (m + 1)
        rw [hc] at h
        simp only [List.length_nil] at h
        rcases Nat.mul_eq_zero.1 h.symm with h' | h'
        · omega
        · exact hVne (List.length_eq_zero_iff.1 h')),
        deningerFlatten_head V m hVne, hhead]
  have haltFR : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1)
      (deningerFlatten (G := G) V k ++ R) := by
    refine List.isChain_append.2 ⟨hflat, hRalt, ?_⟩
    intro p hp q hq
    cases k with
    | zero => rw [show deningerFlatten (G := G) V 0 = [] from rfl] at hp; simp at hp
    | succ m =>
      rw [deningerFlatten_getLast V hVne m] at hp
      obtain ⟨q', hq', hqq⟩ := htrans q hq
      rw [← hqq]
      exact hVcyc p hp q' hq'
  have halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1)
      (C ++ (deningerFlatten (G := G) V k ++ R)) := by
    refine List.isChain_append.2 ⟨hCalt, haltFR, ?_⟩
    intro p hp q hq
    rw [Option.mem_def] at hq
    have h1 : (deningerFlatten (G := G) V k ++ R).head?.map Sigma.fst = some q.1 := by
      rw [hq]; rfl
    rw [hheadFR] at h1
    cases hR : R.head? with
    | none => rw [hR] at h1; simp at h1
    | some r =>
      rw [hR] at h1
      simp only [Option.map_some, Option.some.injEq] at h1
      rw [← h1]
      exact hCR p hp r hR
  have hred : ∀ p ∈ C ++ (deningerFlatten (G := G) V k ++ R), p.2 ∉ (φ p.1).range := by
    intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hCRred p (List.mem_append.2 (Or.inl hp))
    · rcases List.mem_append.1 hp with hp | hp
      · exact hVred p (deningerFlatten_mem V k p hp)
      · exact hCRred p (List.mem_append.2 (Or.inr hp))
  have hlen := congrArg List.length
    (deningerNormalWord_map_fst (d := d) (C ++ (deningerFlatten (G := G) V k ++ R)) hred halt)
  rw [List.length_map, List.length_map] at hlen
  show ((_ • (NormalWord.empty : NormalWord d)) : NormalWord d).toList.length = _
  rw [hpow, hlen]
  simp only [List.length_append, deningerFlatten_length]
  ring

include d in
/-- **The increment.**  Each further power adds the length of the cyclically reduced part. -/
theorem deningerLen_conj_pow_sub (C R V : List (Σ i, G i))
    (hCRred : ∀ p ∈ C ++ R, p.2 ∉ (φ p.1).range)
    (hCRalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) (C ++ R))
    (hVne : V ≠ [])
    (hVred : ∀ p ∈ V, p.2 ∉ (φ p.1).range)
    (hValt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) V)
    (hVcyc : ∀ p ∈ V.getLast?, ∀ q ∈ V.head?, p.1 ≠ q.1)
    (hhead : V.head?.map Sigma.fst = R.head?.map Sigma.fst)
    (hprod : deningerLetterProd (φ := φ) R =
      deningerLetterProd (φ := φ) V * (deningerLetterProd (φ := φ) C)⁻¹)
    (k : ℕ) :
    deningerLen d ((deningerLetterProd (φ := φ) (C ++ R)) ^ (k + 1)) =
      deningerLen d (deningerLetterProd (φ := φ) (C ++ R)) + k * V.length := by
  have h0 := deningerLen_conj_pow (d := d) C R V hCRred hCRalt hVne hVred hValt hVcyc hhead hprod 0
  have hk := deningerLen_conj_pow (d := d) C R V hCRred hCRalt hVne hVred hValt hVcyc hhead hprod k
  rw [pow_one] at h0
  omega

end RHTower
