import GaloisForLFunctions.RHTower.DeningerPushoutPower

/-!
# The letter decomposition of an element

Every element of an amalgamated free product is either in the image of the base group, or a product
of a nonempty reduced alternating list of letters.  This is the normal form, with the element of the
base group absorbed into the first letter.

* `deningerTransversal_notMem_range` : a nontrivial transversal element is not in the base group.
* `deningerExists_letterProd` : the letter decomposition.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in
/-- A transversal element other than the identity does not lie in the base group. -/
theorem deningerTransversal_notMem_range (i : ι) (x : G i) (hx : x ∈ d.set i) (hx1 : x ≠ 1) :
    x ∉ (φ i).range := by
  intro hmem
  refine hx1 ?_
  have h1 : (((d.compl i).equiv x).2 : G i) = x :=
    ((d.compl i).equiv_snd_eq_self_iff_mem (one_mem _)).2 hx
  have h2 : (((d.compl i).equiv x).2 : G i) = 1 :=
    ((d.compl i).coe_equiv_snd_eq_one_iff_mem (d.one_mem i)).2 hmem
  rw [← h1, h2]

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in
theorem deningerOfCoprodI_prod (w : Word G) :
    PushoutI.ofCoprodI (φ := φ) w.prod = deningerLetterProd (φ := φ) w.toList := by
  rw [Word.prod, deningerLetterProd, map_list_prod, List.map_map]
  rfl

/-- **The letter decomposition.**  Every element is in the base group or is a product of a nonempty
reduced alternating list of letters. -/
theorem deningerExists_letterProd (g : PushoutI φ) :
    (∃ h : H, g = PushoutI.base φ h ∧ deningerLen d g = 0) ∨
      ∃ L : List (Σ i, G i), L ≠ [] ∧
        (∀ p ∈ L, p.2 ∉ (φ p.1).range) ∧
        List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L ∧
        L.length = deningerLen d g ∧
        g = deningerLetterProd (φ := φ) L := by
  set w : NormalWord d := g • NormalWord.empty with hw
  have hprod : g = PushoutI.base φ w.head * PushoutI.ofCoprodI (φ := φ) w.toWord.prod := by
    have := NormalWord.prod_smul g (NormalWord.empty : NormalWord d)
    rw [NormalWord.prod_empty, mul_one] at this
    rw [← this, ← hw, NormalWord.prod]
  have hred : ∀ p ∈ w.toList, p.2 ∉ (φ p.1).range := fun p hp =>
    deningerTransversal_notMem_range p.1 p.2 (w.normalized p.1 p.2 hp) (w.toWord.ne_one p hp)
  have halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) w.toList := w.toWord.chain_ne
  rcases hL : w.toList with _ | ⟨p, L'⟩
  · left
    refine ⟨w.head, ?_, ?_⟩
    · rw [hprod, deningerOfCoprodI_prod, hL]
      simp
    · show w.toList.length = 0
      rw [hL]
      rfl
  · right
    refine ⟨deningerAbsorb φ w.head (p :: L'), by simp [deningerAbsorb], ?_, ?_, ?_, ?_⟩
    · exact deningerAbsorb_reduced w.head _ (by rw [← hL]; exact hred)
    · exact deningerAbsorb_isChain w.head _ (by rw [← hL]; exact halt)
    · show (deningerAbsorb φ w.head (p :: L')).length = w.toList.length
      rw [deningerAbsorb_length, hL]
    · rw [hprod, deningerOfCoprodI_prod, hL,
        deningerBase_mul_letterProd w.head (p :: L') (by simp)]

end RHTower
