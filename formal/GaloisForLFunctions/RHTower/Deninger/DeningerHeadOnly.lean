import GaloisForLFunctions.RHTower.Deninger.DeningerWordIndices

/-!
# Words transversal except at the front

If every letter of a reduced alternating word except the first lies in the transversal, then putting
it into normal form only normalizes that first letter: the base group element it releases becomes
the head and never reaches the other letters.  Such words are therefore determined by their
products together with their first factor.

* `deningerNormalWord_head_only` : the normal form of such a word.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

/-- **The normal form of a word transversal except at the front.** -/
theorem deningerNormalWord_head_only (j : ι) (x : G j) (L : List (Σ i, G i))
    (hset : ∀ q ∈ L, q.2 ∈ d.set q.1)
    (hred : ∀ q ∈ (⟨j, x⟩ : Σ i, G i) :: L, q.2 ∉ (φ q.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) ((⟨j, x⟩ : Σ i, G i) :: L)) :
    ∃ (k : H) (s : G j), s ∈ d.set j ∧ s ∉ (φ j).range ∧ x = φ j k * s ∧
      ((deningerLetterProd (φ := φ) ((⟨j, x⟩ : Σ i, G i) :: L)) •
        (NormalWord.empty : NormalWord d)).toList = (⟨j, s⟩ : Σ i, G i) :: L := by
  set k : H := (MonoidHom.ofInjective (d.injective j)).symm ((d.compl j).equiv x).1 with hk
  set s : G j := (((d.compl j).equiv x).2 : G j) with hs
  have hks : φ j k * s = x := by
    rw [hk, MonoidHom.apply_ofInjective_symm, hs]
    exact (d.compl j).equiv_fst_mul_equiv_snd x
  have hsset : s ∈ d.set j := ((d.compl j).equiv x).2.2
  have hsred : s ∉ (φ j).range := by
    rintro ⟨w, hw⟩
    refine hred (⟨j, x⟩ : Σ i, G i) List.mem_cons_self ⟨k * w, ?_⟩
    rw [map_mul, hw, hks]
  refine ⟨k, s, hsset, hsred, hks.symm, ?_⟩
  have hsplit : deningerLetterProd (φ := φ) ((⟨j, x⟩ : Σ i, G i) :: L) =
      PushoutI.base φ k * deningerLetterProd (φ := φ) ((⟨j, s⟩ : Σ i, G i) :: L) := by
    have hof : PushoutI.of (φ := φ) j x = PushoutI.base φ k * PushoutI.of (φ := φ) j s := by
      rw [← hks, map_mul, PushoutI.of_apply_eq_base]
    show PushoutI.of (φ := φ) j x * deningerLetterProd (φ := φ) L = _
    rw [hof, deningerLetterProd_cons]
    show _ = PushoutI.base φ k * (PushoutI.of (φ := φ) j s * deningerLetterProd (φ := φ) L)
    rw [mul_assoc]
  rw [hsplit, deningerNormalWord_base_mul]
  refine (deningerNormalWord_letterProd (d := d) ((⟨j, s⟩ : Σ i, G i) :: L) ?_ ?_ ?_).1
  · intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact hsset
    · exact hset q hq
  · intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact hsred
    · exact hred q (List.mem_cons_of_mem _ hq)
  · rw [List.isChain_cons] at halt ⊢
    exact ⟨halt.1, halt.2⟩

end RHTower
