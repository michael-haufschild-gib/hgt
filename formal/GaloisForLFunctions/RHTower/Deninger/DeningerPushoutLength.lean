import GaloisForLFunctions.RHTower.Deninger.DeningerPermutationShapiro
import Mathlib.GroupTheory.PushoutI

/-!
# Word length in an amalgamated free product

Relative to a transversal of the base group, every element of a pushout of groups has a normal
form, and the length of its underlying word is a well behaved length function: it is unchanged by
multiplication by the base group on the left, it vanishes exactly on the base group, and
multiplication by an element of one of the factors changes it by at most one.

* `deningerLen` : the length function.
* `deningerLen_eq_zero_iff` : it vanishes exactly on the image of the base group.
* `deningerLen_of_mul_le`, `deningerLen_le_of_mul` : multiplication by a factor moves it by one.
* `deningerCosetLen` : the induced length on the cosets of the base group, with the base coset as
  its unique zero.

The length depends on the chosen transversal only through the base group: it is the number of
letters of the normal form, which is a well defined invariant of the double coset structure.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

/-- Prepending a letter already lying in the base group does not lengthen a normal word. -/
theorem deningerLen_rcons_of_mem (i : ι) (p : NormalWord.Pair d i)
    (hp : p.head ∈ (φ i).range) :
    (NormalWord.rcons i p).toList.length = p.tail.toList.length := by
  have hn : (((d.compl i).equiv p.head).2 : G i) = 1 ↔ p.head ∈ (φ i).range :=
    Subgroup.IsComplement.coe_equiv_snd_eq_one_iff_mem _ (d.one_mem i)
  show (Word.rcons (i := i)
    ⟨(((d.compl i).equiv p.head).2 : G i), p.tail, p.fstIdx_ne⟩).toList.length = _
  rw [Word.rcons, dif_pos (hn.2 hp)]

/-- Prepending a letter outside the base group lengthens a normal word by one. -/
theorem deningerLen_rcons_of_notMem (i : ι) (p : NormalWord.Pair d i)
    (hp : p.head ∉ (φ i).range) :
    (NormalWord.rcons i p).toList.length = p.tail.toList.length + 1 := by
  have hn : (((d.compl i).equiv p.head).2 : G i) = 1 ↔ p.head ∈ (φ i).range :=
    Subgroup.IsComplement.coe_equiv_snd_eq_one_iff_mem _ (d.one_mem i)
  show (Word.rcons (i := i)
    ⟨(((d.compl i).equiv p.head).2 : G i), p.tail, p.fstIdx_ne⟩).toList.length = _
  rw [Word.rcons, dif_neg (fun hc => hp (hn.1 hc))]
  simp [Word.cons]

/-- The word length of an element of the pushout, relative to a transversal. -/
noncomputable def deningerLen (d : NormalWord.Transversal φ) (g : PushoutI φ) : ℕ :=
  ((g • (NormalWord.empty : NormalWord d)) : NormalWord d).toList.length

theorem deningerLen_one : deningerLen d (1 : PushoutI φ) = 0 := by
  show ((1 : PushoutI φ) • (NormalWord.empty : NormalWord d)).toList.length = 0
  rw [one_smul]
  rfl

theorem deningerLen_base_mul (h : H) (g : PushoutI φ) :
    deningerLen d (base φ h * g) = deningerLen d g := by
  show ((base φ h * g) • (NormalWord.empty : NormalWord d)).toList.length = _
  rw [mul_smul, NormalWord.base_smul_def]
  rfl

theorem deningerLen_base (h : H) : deningerLen d (base φ h) = 0 := by
  rw [show base φ h = base φ h * 1 from (mul_one _).symm, deningerLen_base_mul, deningerLen_one]

theorem deningerLen_eq_zero_iff (g : PushoutI φ) :
    deningerLen d g = 0 ↔ g ∈ (base φ).range := by
  refine ⟨fun hg => ?_, fun ⟨h, hh⟩ => hh ▸ deningerLen_base h⟩
  set w : NormalWord d := g • NormalWord.empty with hw
  have hnil : w.toList = [] := List.length_eq_zero_iff.1 hg
  have hprod : w.prod = g := by
    rw [hw, NormalWord.prod_smul, NormalWord.prod_empty, mul_one]
  have hw1 : (w.toWord).prod = 1 := by
    rw [Word.prod, hnil]
    simp
  refine ⟨w.head, ?_⟩
  rw [← hprod, NormalWord.prod, hw1]
  simp

/-- Multiplying a normal word by an element of one of the factors changes its length by at most
one in either direction. -/
theorem deningerLen_summand_smul (i : ι) (x : G i) (w : NormalWord d) :
    ((x • w : NormalWord d)).toList.length ≤ w.toList.length + 1 ∧
      w.toList.length ≤ ((x • w : NormalWord d)).toList.length + 1 := by
  set p := NormalWord.equivPair i w with hp
  have hsymm : ∀ q : NormalWord.Pair d i, (NormalWord.equivPair i).symm q =
      NormalWord.rcons i q := fun _ => rfl
  have hw : w = NormalWord.rcons i p := by
    rw [← hsymm p, hp]
    exact ((NormalWord.equivPair i).symm_apply_apply w).symm
  have hxw : (x • w : NormalWord d) = NormalWord.rcons i { p with head := x * p.head } := by
    rw [NormalWord.summand_smul_def', ← hp, hsymm]
  have htail : ({ p with head := x * p.head } : NormalWord.Pair d i).tail = p.tail := rfl
  by_cases h1 : p.head ∈ (φ i).range <;> by_cases h2 : x * p.head ∈ (φ i).range
  · rw [hxw, deningerLen_rcons_of_mem i _ h2, htail]
    conv_lhs => rw [hw]
    conv_rhs => rw [hw]
    rw [deningerLen_rcons_of_mem i p h1]
    omega
  · rw [hxw, deningerLen_rcons_of_notMem i _ h2, htail]
    conv_lhs => rw [hw]
    conv_rhs => rw [hw]
    rw [deningerLen_rcons_of_mem i p h1]
    omega
  · rw [hxw, deningerLen_rcons_of_mem i _ h2, htail]
    conv_lhs => rw [hw]
    conv_rhs => rw [hw]
    rw [deningerLen_rcons_of_notMem i p h1]
    omega
  · rw [hxw, deningerLen_rcons_of_notMem i _ h2, htail]
    conv_lhs => rw [hw]
    conv_rhs => rw [hw]
    rw [deningerLen_rcons_of_notMem i p h1]
    omega

theorem deningerLen_of_mul_le (i : ι) (x : G i) (g : PushoutI φ) :
    deningerLen d (of i x * g) ≤ deningerLen d g + 1 := by
  show ((of i x * g) • (NormalWord.empty : NormalWord d)).toList.length ≤ _
  rw [mul_smul, NormalWord.of_smul_eq_smul]
  exact (deningerLen_summand_smul i x _).1

theorem deningerLen_le_of_mul (i : ι) (x : G i) (g : PushoutI φ) :
    deningerLen d g ≤ deningerLen d (of i x * g) + 1 := by
  show _ ≤ ((of i x * g) • (NormalWord.empty : NormalWord d)).toList.length + 1
  rw [mul_smul, NormalWord.of_smul_eq_smul]
  exact (deningerLen_summand_smul i x _).2

section Cosets

variable (d)

/-- The length of a coset of the base group: the word length of the inverse of any representative.
Inversion is what turns the left invariance of the length under the base group into an invariant of
left cosets. -/
noncomputable def deningerCosetLen (x : PushoutI φ ⧸ (base φ).range) : ℕ :=
  Quotient.liftOn' x (fun g => deningerLen d g⁻¹) (fun a b hab => by
    obtain ⟨h, hh⟩ : a⁻¹ * b ∈ (base φ).range := QuotientGroup.leftRel_apply.1 hab
    have hb : b = a * base φ h := by rw [hh]; group
    rw [hb, mul_inv_rev, ← map_inv, deningerLen_base_mul])

@[simp]
theorem deningerCosetLen_mk (g : PushoutI φ) :
    deningerCosetLen d (QuotientGroup.mk g : PushoutI φ ⧸ (base φ).range) =
      deningerLen d g⁻¹ := rfl

/-- The base coset is the unique one of length zero: it is the root of the tree of cosets. -/
theorem deningerCosetLen_eq_zero_iff (x : PushoutI φ ⧸ (base φ).range) :
    deningerCosetLen d x = 0 ↔ x = (QuotientGroup.mk 1 : PushoutI φ ⧸ (base φ).range) := by
  induction x using QuotientGroup.induction_on with
  | _ g =>
    rw [deningerCosetLen_mk, deningerLen_eq_zero_iff, QuotientGroup.eq]
    simp

/-- Two cosets of the base group joined by a letter of one of the factors have lengths differing by
at most one.  This is the statement that the tree of cosets is graded by the length. -/
theorem deningerCosetLen_mul_of (i : ι) (x : G i) (g : PushoutI φ) :
    deningerCosetLen d (QuotientGroup.mk (g * of i x)) ≤
        deningerCosetLen d (QuotientGroup.mk g) + 1 ∧
      deningerCosetLen d (QuotientGroup.mk g) ≤
        deningerCosetLen d (QuotientGroup.mk (g * of i x)) + 1 := by
  rw [deningerCosetLen_mk, deningerCosetLen_mk, mul_inv_rev, ← map_inv]
  exact ⟨deningerLen_of_mul_le i x⁻¹ g⁻¹, deningerLen_le_of_mul i x⁻¹ g⁻¹⟩

end Cosets

end RHTower
