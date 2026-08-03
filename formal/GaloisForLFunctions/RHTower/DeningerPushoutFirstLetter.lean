import GaloisForLFunctions.RHTower.DeningerBassSerreTree

/-!
# The first letter of a normal form, and the sharp length law

Multiplying on the left by a letter of a factor that does not already occur at the front of the
normal form lengthens the word by exactly one.  This is the geometric input that makes the tree of
cosets acyclic: among the cosets of the base group inside a fixed coset of a factor, exactly one is
closest to the base coset, and the others are strictly further away.

* `deningerEquivPair_of_fstIdx_ne` : the pair decomposition of a normal word whose first letter is
  not in the given factor.
* `deningerLen_of_mul_eq` : the sharp length law.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

/-- If the first letter of a normal word does not lie in the factor `i`, then its `i`-th pair
decomposition has the head coming entirely from the base group and the tail equal to the whole
word. -/
theorem deningerEquivPair_of_fstIdx_ne (i : ι) (w : NormalWord d)
    (h : w.fstIdx ≠ some i) :
    (NormalWord.equivPair i w).head = φ i w.head ∧
      (NormalWord.equivPair i w).tail = w.toWord := by
  have hw : Word.equivPair i (CoprodI.of (φ i w.head) • w.toWord) =
      ⟨φ i w.head * (Word.equivPair i w.toWord).head,
        (Word.equivPair i w.toWord).tail, (Word.equivPair i w.toWord).fstIdx_ne⟩ :=
    Word.equivPair_smul_same _ _
  have hw2 : Word.equivPair i w.toWord = ⟨1, w.toWord, h⟩ :=
    Word.equivPair_eq_of_fstIdx_ne h
  constructor
  · show (Word.equivPair i (CoprodI.of (φ i w.head) • w.toWord)).head = _
    rw [hw, hw2]
    simp
  · show (Word.equivPair i (CoprodI.of (φ i w.head) • w.toWord)).tail = _
    rw [hw, hw2]

/-- **The sharp length law**: multiplying by a letter of a factor which is not already at the front
of the normal form, and which does not come from the base group, lengthens the word by exactly
one. -/
theorem deningerLen_of_mul_eq (i : ι) (x : G i) (g : PushoutI φ)
    (hx : x ∉ (φ i).range)
    (hg : ((g • (NormalWord.empty : NormalWord d)) : NormalWord d).fstIdx ≠ some i) :
    deningerLen d (PushoutI.of i x * g) = deningerLen d g + 1 := by
  set w : NormalWord d := g • NormalWord.empty with hwdef
  obtain ⟨hhead, htail⟩ := deningerEquivPair_of_fstIdx_ne i w hg
  have hsymm : ∀ q : NormalWord.Pair d i, (NormalWord.equivPair i).symm q =
      NormalWord.rcons i q := fun _ => rfl
  have hnot : x * (NormalWord.equivPair i w).head ∉ (φ i).range := by
    rw [hhead]
    rintro ⟨y, hy⟩
    exact hx ⟨y * (w.head)⁻¹, by rw [map_mul, hy, map_inv]; group⟩
  show ((PushoutI.of i x * g) • (NormalWord.empty : NormalWord d)).toList.length = _
  rw [mul_smul, ← hwdef, NormalWord.of_smul_eq_smul, NormalWord.summand_smul_def', hsymm]
  rw [deningerLen_rcons_of_notMem i _ hnot]
  show _ = w.toList.length + 1
  rw [show ({ NormalWord.equivPair i w with
      head := x * (NormalWord.equivPair i w).head } : NormalWord.Pair d i).tail =
    (NormalWord.equivPair i w).tail from rfl, htail]

/-- The index of the first letter of the normal form attached to a coset of the base group.  It is
well defined because multiplying by the base group changes only the head of a normal word. -/
noncomputable def deningerFirstIdx (d : NormalWord.Transversal φ)
    (x : PushoutI φ ⧸ (PushoutI.base φ).range) : Option ι :=
  Quotient.liftOn' x (fun g => ((g⁻¹ • (NormalWord.empty : NormalWord d)) : NormalWord d).fstIdx)
    (fun a b hab => by
      obtain ⟨h, hh⟩ : a⁻¹ * b ∈ (PushoutI.base φ).range := QuotientGroup.leftRel_apply.1 hab
      have hba : b = a * PushoutI.base φ h := by rw [hh]; group
      have hb : b⁻¹ = PushoutI.base φ h⁻¹ * a⁻¹ := by
        rw [hba, mul_inv_rev, ← map_inv]
      rw [hb, mul_smul, NormalWord.base_smul_def])

@[simp] theorem deningerFirstIdx_mk (g : PushoutI φ) :
    deningerFirstIdx d (QuotientGroup.mk g : PushoutI φ ⧸ (PushoutI.base φ).range) =
      ((g⁻¹ • (NormalWord.empty : NormalWord d)) : NormalWord d).fstIdx := rfl

/-- **Cosets of the base group inside a coset of a factor.**  If the coset `gC` is not already
reached through the factor `i`, then every other coset of the base group inside `gA_i` is one step
further from the base coset. -/
theorem deningerCosetLen_mul_of_eq (i : ι) (g : PushoutI φ) (y : G i)
    (hfirst : deningerFirstIdx d (QuotientGroup.mk g : PushoutI φ ⧸ _) ≠ some i)
    (hne : (QuotientGroup.mk (g * PushoutI.of i y) : PushoutI φ ⧸ (PushoutI.base φ).range) ≠
      QuotientGroup.mk g) :
    deningerCosetLen d (QuotientGroup.mk (g * PushoutI.of i y)) =
      deningerCosetLen d (QuotientGroup.mk g) + 1 := by
  have hy : y ∉ (φ i).range := by
    rintro ⟨z, hz⟩
    refine hne ?_
    rw [QuotientGroup.eq]
    refine ⟨z⁻¹, ?_⟩
    rw [map_inv, ← hz, PushoutI.of_apply_eq_base]
    group
  rw [deningerCosetLen_mk, deningerCosetLen_mk, mul_inv_rev, ← map_inv]
  refine deningerLen_of_mul_eq i y⁻¹ g⁻¹ ?_ ?_
  · simpa using hy
  · simpa using hfirst

end RHTower
