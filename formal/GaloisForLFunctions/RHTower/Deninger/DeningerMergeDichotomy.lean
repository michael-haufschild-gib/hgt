import GaloisForLFunctions.RHTower.Deninger.DeningerCancelCriterion

/-!
# The merge dichotomy

If the normal form of an element begins in the factor `i`, then multiplying by a letter of `i`
either leaves the front in the factor `i`, or strictly shortens the word: the merged letter either
survives as a letter or falls into the base group.

* `deningerMerge_dichotomy` : the dichotomy.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

/-- **The merge dichotomy.** -/
theorem deningerMerge_dichotomy (i : ι) (x : G i) (b : PushoutI φ)
    (hb : ((b • (NormalWord.empty : NormalWord d)) : NormalWord d).fstIdx = some i) :
    (((PushoutI.of i x * b) • (NormalWord.empty : NormalWord d)) : NormalWord d).fstIdx =
        some i ∨
      deningerLen d (PushoutI.of i x * b) < deningerLen d b := by
  set w : NormalWord d := b • NormalWord.empty with hwdef
  have hhead := deningerEquivPair_head_notMem i w hb
  have hsymm : ∀ q : NormalWord.Pair d i, (NormalWord.equivPair i).symm q =
      NormalWord.rcons i q := fun _ => rfl
  have hw : w = NormalWord.rcons i (NormalWord.equivPair i w) := by
    rw [← hsymm]
    exact ((NormalWord.equivPair i).symm_apply_apply w).symm
  have htail : ({ NormalWord.equivPair i w with
      head := x * (NormalWord.equivPair i w).head } : NormalWord.Pair d i).tail =
    (NormalWord.equivPair i w).tail := rfl
  have hlenw : deningerLen d b = (NormalWord.equivPair i w).tail.toList.length + 1 := by
    show w.toList.length = _
    conv_lhs => rw [hw]
    exact deningerLen_rcons_of_notMem i _ hhead
  have hprod : (PushoutI.of i x * b) • (NormalWord.empty : NormalWord d) =
      NormalWord.rcons i { NormalWord.equivPair i w with
        head := x * (NormalWord.equivPair i w).head } := by
    rw [mul_smul, ← hwdef, NormalWord.of_smul_eq_smul, NormalWord.summand_smul_def', hsymm]
  by_cases hcase : x * (NormalWord.equivPair i w).head ∈ (φ i).range
  · right
    show ((PushoutI.of i x * b) • (NormalWord.empty : NormalWord d)).toList.length < _
    rw [hprod, deningerLen_rcons_of_mem i _ hcase, htail]
    omega
  · left
    have hn : (((d.compl i).equiv (x * (NormalWord.equivPair i w).head)).2 : G i) ≠ 1 := fun hc =>
      hcase ((Subgroup.IsComplement.coe_equiv_snd_eq_one_iff_mem _ (d.one_mem i)).1 hc)
    show ((PushoutI.of i x * b) • (NormalWord.empty : NormalWord d)).fstIdx = some i
    rw [hprod]
    show (Word.rcons (i := i)
      ⟨(((d.compl i).equiv (x * (NormalWord.equivPair i w).head)).2 : G i),
        (NormalWord.equivPair i w).tail, _⟩).fstIdx = some i
    rw [Word.rcons, dif_neg hn, Word.fstIdx_cons]

end RHTower
