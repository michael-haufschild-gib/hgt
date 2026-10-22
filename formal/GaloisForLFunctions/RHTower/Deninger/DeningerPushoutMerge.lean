import GaloisForLFunctions.RHTower.Deninger.DeningerPushoutInv

/-!
# Merging a letter into the front of a word

If the normal form of an element already begins in the factor `i`, then multiplying by a letter of
that factor does not lengthen it: the two letters merge.  Combined with invariance of the length
under inversion this also bounds multiplication on the right.

* `deningerEquivPair_head_notMem` : the head of the pair decomposition is a genuine letter.
* `deningerLen_of_mul_le_of_fstIdx` : merging on the left.
* `deningerLen_mul_of_le` : merging on the right.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

theorem deningerRcons_toWord_of_mem (i : ι) (p : NormalWord.Pair d i)
    (hp : p.head ∈ (φ i).range) :
    (NormalWord.rcons i p).toWord = p.tail := by
  have hn : (((d.compl i).equiv p.head).2 : G i) = 1 :=
    (Subgroup.IsComplement.coe_equiv_snd_eq_one_iff_mem _ (d.one_mem i)).2 hp
  show Word.rcons (i := i)
    ⟨(((d.compl i).equiv p.head).2 : G i), p.tail, p.fstIdx_ne⟩ = p.tail
  rw [Word.rcons, dif_pos hn]

/-- If the normal form begins in the factor `i`, the head of its `i`-th pair decomposition is not
in the base group. -/
theorem deningerEquivPair_head_notMem (i : ι) (w : NormalWord d) (h : w.fstIdx = some i) :
    (NormalWord.equivPair i w).head ∉ (φ i).range := by
  intro hmem
  have hsymm : (NormalWord.equivPair i).symm (NormalWord.equivPair i w) =
      NormalWord.rcons i (NormalWord.equivPair i w) := rfl
  have hw : NormalWord.rcons i (NormalWord.equivPair i w) = w := by
    rw [← hsymm, Equiv.symm_apply_apply]
  have htoword := deningerRcons_toWord_of_mem i (NormalWord.equivPair i w) hmem
  rw [hw] at htoword
  exact (NormalWord.equivPair i w).fstIdx_ne (htoword ▸ h)

/-- **Merging on the left.**  If the normal form of `g` begins in the factor `i`, multiplying by a
letter of `i` does not lengthen it. -/
theorem deningerLen_of_mul_le_of_fstIdx (i : ι) (x : G i) (g : PushoutI φ)
    (hg : ((g • (NormalWord.empty : NormalWord d)) : NormalWord d).fstIdx = some i) :
    deningerLen d (PushoutI.of i x * g) ≤ deningerLen d g := by
  set w : NormalWord d := g • NormalWord.empty with hwdef
  have hhead := deningerEquivPair_head_notMem i w hg
  have hsymm : ∀ q : NormalWord.Pair d i, (NormalWord.equivPair i).symm q =
      NormalWord.rcons i q := fun _ => rfl
  have hw : w = NormalWord.rcons i (NormalWord.equivPair i w) := by
    rw [← hsymm]
    exact ((NormalWord.equivPair i).symm_apply_apply w).symm
  have htail : ({ NormalWord.equivPair i w with
      head := x * (NormalWord.equivPair i w).head } : NormalWord.Pair d i).tail =
    (NormalWord.equivPair i w).tail := rfl
  have hlenw : deningerLen d g = (NormalWord.equivPair i w).tail.toList.length + 1 := by
    show w.toList.length = _
    conv_lhs => rw [hw]
    exact deningerLen_rcons_of_notMem i _ hhead
  show ((PushoutI.of i x * g) • (NormalWord.empty : NormalWord d)).toList.length ≤ deningerLen d g
  rw [mul_smul, ← hwdef, NormalWord.of_smul_eq_smul, NormalWord.summand_smul_def', hsymm]
  by_cases hcase : x * (NormalWord.equivPair i w).head ∈ (φ i).range
  · rw [deningerLen_rcons_of_mem i _ hcase, htail]
    omega
  · rw [deningerLen_rcons_of_notMem i _ hcase, htail]
    omega

/-- **Merging on the right.** -/
theorem deningerLen_mul_of_le (i : ι) (x : G i) (g : PushoutI φ)
    (hg : ((g⁻¹ • (NormalWord.empty : NormalWord d)) : NormalWord d).fstIdx = some i) :
    deningerLen d (g * PushoutI.of i x) ≤ deningerLen d g := by
  rw [← deningerLen_inv (d := d) (g * PushoutI.of i x), mul_inv_rev, ← map_inv,
    ← deningerLen_inv (d := d) g]
  exact deningerLen_of_mul_le_of_fstIdx i x⁻¹ g⁻¹ hg

end RHTower
