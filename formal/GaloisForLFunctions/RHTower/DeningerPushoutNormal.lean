import GaloisForLFunctions.RHTower.DeningerPushoutTorsion

/-!
# The normal word of a transversal word

If every letter of a reduced alternating list lies in the chosen transversal, then the list is
literally the normal word of its product, and the head is trivial.  This makes such words unique:
two transversal words with the same product are equal.

* `deningerNormalWord_letterProd` : the normal word of a transversal word is the word itself.
* `deningerLetterProd_injective` : transversal words are determined by their products.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in
theorem deningerEquiv_fst_eq_one (i : ι) (x : G i) (hx : x ∈ d.set i) :
    (((d.compl i).equiv x).1 : G i) = 1 := by
  have h2 : (((d.compl i).equiv x).2 : G i) = x :=
    ((d.compl i).equiv_snd_eq_self_iff_mem (one_mem _)).2 hx
  have h1 := (d.compl i).equiv_fst_mul_equiv_snd (g := x)
  rw [h2] at h1
  refine mul_right_cancel (b := x) ?_
  rw [h1, one_mul]

/-- **The normal word of a transversal word.**  If every letter lies in the transversal, the normal
form of the product is the word itself, with trivial head. -/
theorem deningerNormalWord_letterProd (L : List (Σ i, G i))
    (hset : ∀ p ∈ L, p.2 ∈ d.set p.1)
    (hred : ∀ p ∈ L, p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L) :
    ((deningerLetterProd (φ := φ) L • (NormalWord.empty : NormalWord d)) :
        NormalWord d).toList = L ∧
      ((deningerLetterProd (φ := φ) L • (NormalWord.empty : NormalWord d)) :
        NormalWord d).head = 1 := by
  induction L with
  | nil =>
    refine ⟨?_, ?_⟩ <;> simp [deningerLetterProd_nil]
  | cons p L' ih =>
    obtain ⟨ihlist, ihhead⟩ := ih (fun q hq => hset q (List.mem_cons_of_mem _ hq))
      (fun q hq => hred q (List.mem_cons_of_mem _ hq)) halt.tail
    set w : NormalWord d := deningerLetterProd (φ := φ) L' • NormalWord.empty with hwdef
    have hfst : w.fstIdx ≠ some p.1 := by
      intro hc
      rw [Word.fstIdx, ihlist] at hc
      cases L' with
      | nil => simp at hc
      | cons q L'' =>
        have hne : p.1 ≠ q.1 := (List.isChain_cons.1 halt).1 q (by simp)
        simp only [List.head?_cons, Option.map_some] at hc
        exact hne (Option.some.inj hc).symm
    obtain ⟨hhead, htail⟩ := deningerEquivPair_of_fstIdx_ne p.1 w hfst
    have hpair : p.2 * (NormalWord.equivPair p.1 w).head = p.2 := by
      rw [hhead, ihhead, map_one, mul_one]
    have hsymm : ∀ q : NormalWord.Pair d p.1, (NormalWord.equivPair p.1).symm q =
        NormalWord.rcons p.1 q := fun _ => rfl
    have hne1 : (((d.compl p.1).equiv (p.2 * (NormalWord.equivPair p.1 w).head)).2 : G p.1) ≠ 1 := by
      rw [hpair]
      intro hc
      exact hred p List.mem_cons_self
        ((Subgroup.IsComplement.coe_equiv_snd_eq_one_iff_mem _ (d.one_mem p.1)).1 hc)
    have hsnd : (((d.compl p.1).equiv (p.2 * (NormalWord.equivPair p.1 w).head)).2 : G p.1) =
        p.2 := by
      rw [hpair]
      exact ((d.compl p.1).equiv_snd_eq_self_iff_mem (one_mem _)).2 (hset p List.mem_cons_self)
    have hfstone : (((d.compl p.1).equiv (p.2 * (NormalWord.equivPair p.1 w).head)).1 : G p.1)
        = 1 := by
      rw [hpair]
      exact deningerEquiv_fst_eq_one p.1 p.2 (hset p List.mem_cons_self)
    have hstep : deningerLetterProd (φ := φ) (p :: L') • (NormalWord.empty : NormalWord d) =
        NormalWord.rcons p.1 { NormalWord.equivPair p.1 w with
          head := p.2 * (NormalWord.equivPair p.1 w).head } := by
      rw [deningerLetterProd_cons, mul_smul, ← hwdef, NormalWord.of_smul_eq_smul,
        NormalWord.summand_smul_def', hsymm]
    constructor
    · rw [hstep]
      show (Word.rcons (i := p.1)
        ⟨(((d.compl p.1).equiv (p.2 * (NormalWord.equivPair p.1 w).head)).2 : G p.1),
          (NormalWord.equivPair p.1 w).tail, _⟩).toList = p :: L'
      rw [Word.rcons, dif_neg hne1]
      show (⟨p.1, (((d.compl p.1).equiv (p.2 * (NormalWord.equivPair p.1 w).head)).2 : G p.1)⟩ :
        Σ i, G i) :: (NormalWord.equivPair p.1 w).tail.toList = p :: L'
      rw [hsnd, htail, ihlist]
    · rw [hstep]
      show (MonoidHom.ofInjective (d.injective p.1)).symm
        ((d.compl p.1).equiv (p.2 * (NormalWord.equivPair p.1 w).head)).1 = 1
      rw [show ((d.compl p.1).equiv (p.2 * (NormalWord.equivPair p.1 w).head)).1 = 1 from
        Subtype.ext (by rw [hfstone]; rfl), map_one]

/-- **Transversal words are determined by their products.** -/
theorem deningerLetterProd_injective (L M : List (Σ i, G i))
    (hsetL : ∀ p ∈ L, p.2 ∈ d.set p.1) (hredL : ∀ p ∈ L, p.2 ∉ (φ p.1).range)
    (haltL : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L)
    (hsetM : ∀ p ∈ M, p.2 ∈ d.set p.1) (hredM : ∀ p ∈ M, p.2 ∉ (φ p.1).range)
    (haltM : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) M)
    (h : deningerLetterProd (φ := φ) L = deningerLetterProd (φ := φ) M) : L = M := by
  have hL := deningerNormalWord_letterProd (d := d) L hsetL hredL haltL
  have hM := deningerNormalWord_letterProd (d := d) M hsetM hredM haltM
  rw [← hL.1, ← hM.1, h]

end RHTower
