import GaloisForLFunctions.RHTower.Deninger.DeningerCycLenEq

/-!
# Putting a word into transversal form

Any reduced alternating word equals an element of the base group times a reduced alternating word
whose letters lie in the chosen transversal and which has the same sequence of indices.  The base
group elements are pushed to the left, one letter at a time.

* `deningerIsChain_of_map_fst` : alternation only depends on the indices.
* `deningerExists_transversal_form` : the transversal form of a word.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

omit [∀ i, Group (G i)] [DecidableEq ι] [∀ i, DecidableEq (G i)] in
theorem deningerIsChain_of_map_fst (L M : List (Σ i, G i))
    (h : M.map Sigma.fst = L.map Sigma.fst)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L) :
    List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) M := by
  rw [← List.isChain_map (R := fun a b : ι => a ≠ b) Sigma.fst] at halt ⊢
  rwa [h]

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in
include d in
/-- **The transversal form of a word.**  Every reduced alternating word is an element of the base
group times a reduced alternating word with the same indices whose letters lie in the
transversal. -/
theorem deningerExists_transversal_form (L : List (Σ i, G i))
    (hred : ∀ p ∈ L, p.2 ∉ (φ p.1).range) :
    ∃ (h : H) (M : List (Σ i, G i)),
      M.map Sigma.fst = L.map Sigma.fst ∧
      (∀ p ∈ M, p.2 ∈ d.set p.1) ∧ (∀ p ∈ M, p.2 ∉ (φ p.1).range) ∧
      deningerLetterProd (φ := φ) L =
        PushoutI.base φ h * deningerLetterProd (φ := φ) M := by
  induction L with
  | nil => exact ⟨1, [], rfl, by simp, by simp, by simp⟩
  | cons p L' ih =>
    obtain ⟨h', M', hmap, hset, hredM, heq⟩ :=
      ih (fun q hq => hred q (List.mem_cons_of_mem _ hq))
    set y : G p.1 := p.2 * φ p.1 h' with hy
    set k : H := (MonoidHom.ofInjective (d.injective p.1)).symm ((d.compl p.1).equiv y).1 with hk
    set s : G p.1 := (((d.compl p.1).equiv y).2 : G p.1) with hs
    have hks : φ p.1 k * s = y := by
      rw [hk, MonoidHom.apply_ofInjective_symm, hs]
      exact (d.compl p.1).equiv_fst_mul_equiv_snd y
    have hsset : s ∈ d.set p.1 := ((d.compl p.1).equiv y).2.2
    have hsred : s ∉ (φ p.1).range := by
      rintro ⟨z, hz⟩
      refine hred p List.mem_cons_self ?_
      refine ⟨k * z * (h')⁻¹, ?_⟩
      rw [map_mul, map_mul, hz, hks, hy, map_inv]
      group
    refine ⟨k, ⟨p.1, s⟩ :: M', by simpa using hmap, ?_, ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hsset
      · exact hset q hq
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hsred
      · exact hredM q hq
    · have hletter : PushoutI.of p.1 p.2 * PushoutI.base φ h' =
          PushoutI.base φ k * PushoutI.of p.1 s := by
        rw [← PushoutI.of_apply_eq_base φ p.1 h', ← map_mul, ← hy, ← hks, map_mul,
          PushoutI.of_apply_eq_base φ p.1 k]
      rw [deningerLetterProd_cons, heq, deningerLetterProd_cons, ← mul_assoc, hletter, mul_assoc]

end RHTower
