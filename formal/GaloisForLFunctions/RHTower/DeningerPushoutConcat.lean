import GaloisForLFunctions.RHTower.DeningerHomologyUnion
import GaloisForLFunctions.RHTower.DeningerPushoutFirstLetter

/-!
# Prepending letters to a normal form

Multiplying by a letter of a factor that does not already occur at the front of a normal form, and
that does not come from the base group, lengthens the word by one and puts that factor at the
front.

* `deningerFstIdx_of_mul` : the new first letter.
* `deningerLetterProd`, `deningerLen_prepend` : the length of a product of alternating letters.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

/-- Prepending a letter outside the base group, in a factor which is not already at the front,
makes that factor the front of the normal form. -/
theorem deningerFstIdx_of_mul (i : ι) (x : G i) (g : PushoutI φ)
    (hx : x ∉ (φ i).range)
    (hg : ((g • (NormalWord.empty : NormalWord d)) : NormalWord d).fstIdx ≠ some i) :
    (((PushoutI.of i x * g) • (NormalWord.empty : NormalWord d)) : NormalWord d).fstIdx =
      some i := by
  set w : NormalWord d := g • NormalWord.empty with hwdef
  obtain ⟨hhead, htail⟩ := deningerEquivPair_of_fstIdx_ne i w hg
  have hsymm : ∀ q : NormalWord.Pair d i, (NormalWord.equivPair i).symm q =
      NormalWord.rcons i q := fun _ => rfl
  have hnot : x * (NormalWord.equivPair i w).head ∉ (φ i).range := by
    rw [hhead]
    rintro ⟨y, hy⟩
    exact hx ⟨y * (w.head)⁻¹, by rw [map_mul, hy, map_inv]; group⟩
  have hn : (((d.compl i).equiv (x * (NormalWord.equivPair i w).head)).2 : G i) ≠ 1 := fun hc =>
    hnot ((Subgroup.IsComplement.coe_equiv_snd_eq_one_iff_mem _ (d.one_mem i)).1 hc)
  show ((PushoutI.of i x * g) • (NormalWord.empty : NormalWord d)).fstIdx = some i
  rw [mul_smul, ← hwdef, NormalWord.of_smul_eq_smul, NormalWord.summand_smul_def', hsymm]
  show (Word.rcons (i := i)
    ⟨(((d.compl i).equiv (x * (NormalWord.equivPair i w).head)).2 : G i),
      (NormalWord.equivPair i w).tail, _⟩).fstIdx = some i
  rw [Word.rcons, dif_neg hn, Word.fstIdx_cons]

/-- The product of a list of letters. -/
def deningerLetterProd (L : List (Σ i, G i)) : PushoutI φ :=
  (L.map (fun p => PushoutI.of p.1 p.2)).prod

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
@[simp] theorem deningerLetterProd_nil : deningerLetterProd (φ := φ) [] = 1 := rfl

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
@[simp] theorem deningerLetterProd_cons (p : Σ i, G i) (L : List (Σ i, G i)) :
    deningerLetterProd (φ := φ) (p :: L) =
      PushoutI.of p.1 p.2 * deningerLetterProd (φ := φ) L := rfl

/-- **The length of a product of alternating letters.**  Prepending a reduced alternating word to
an element whose normal form does not begin in the last factor used adds the number of letters, and
puts the first letter at the front. -/
theorem deningerLen_prepend (L : List (Σ i, G i)) (g : PushoutI φ)
    (hred : ∀ p ∈ L, p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L)
    (hlast : ∀ p ∈ L.getLast?,
      ((g • (NormalWord.empty : NormalWord d)) : NormalWord d).fstIdx ≠ some p.1) :
    deningerLen d (deningerLetterProd (φ := φ) L * g) = L.length + deningerLen d g ∧
      ∀ p ∈ L.head?, ((deningerLetterProd (φ := φ) L * g) •
        (NormalWord.empty : NormalWord d)).fstIdx = some p.1 := by
  induction L with
  | nil => simp
  | cons p L' ih =>
    have hredL' : ∀ q ∈ L', q.2 ∉ (φ q.1).range := fun q hq => hred q (List.mem_cons_of_mem _ hq)
    have haltL' : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L' := halt.tail
    have hlastL' : ∀ q ∈ L'.getLast?,
        ((g • (NormalWord.empty : NormalWord d)) : NormalWord d).fstIdx ≠ some q.1 := by
      intro q hq
      refine hlast q ?_
      rw [List.getLast?_cons_of_ne_nil]
      · exact hq
      · intro hnil
        rw [hnil] at hq
        simp at hq
    obtain ⟨ihlen, ihfst⟩ := ih hredL' haltL' hlastL'
    have hfst : ((deningerLetterProd (φ := φ) L' * g) •
        (NormalWord.empty : NormalWord d)).fstIdx ≠ some p.1 := by
      cases hL' : L' with
      | nil =>
        subst hL'
        simp only [deningerLetterProd_nil, one_mul]
        exact hlast p (by simp)
      | cons q L'' =>
        subst hL'
        rw [ihfst q (by simp)]
        intro hc
        have hne : p.1 ≠ q.1 := (List.isChain_cons.1 halt).1 q (by simp)
        exact hne (Option.some.inj hc).symm
    constructor
    · rw [deningerLetterProd_cons, mul_assoc,
        deningerLen_of_mul_eq p.1 p.2 _ (hred p List.mem_cons_self) hfst, ihlen]
      simp [add_comm, add_assoc, add_left_comm]
    · intro q hq
      rw [List.head?_cons, Option.mem_def] at hq
      obtain rfl : q = p := (Option.some.inj hq).symm
      rw [deningerLetterProd_cons, mul_assoc]
      exact deningerFstIdx_of_mul q.1 q.2 _ (hred q List.mem_cons_self) hfst

end RHTower
