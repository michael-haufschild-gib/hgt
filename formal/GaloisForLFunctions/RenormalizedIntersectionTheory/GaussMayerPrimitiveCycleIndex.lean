import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerPrimitivePairCycles
import Mathlib.Data.PNat.Basic

/-! Exact indexing of nonempty words by primitive cycles, positive repetition,
and a position in the primitive root. -/

open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCoding
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerPrimitiveCycles
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCycleIndex

variable {α : Type*}

/-- Primitive words modulo cyclic rotation. -/
def primitiveSetoid (α : Type*) : Setoid {u : List α // Primitive u} where
  r u v := List.IsRotated u.val v.val
  iseqv := ⟨fun u => List.IsRotated.refl u.val,
    fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

def PrimitiveCycle (α : Type*) := Quotient (primitiveSetoid α)

def representative (c : PrimitiveCycle α) : {u : List α // Primitive u} := Quotient.out c

def cycleLength (c : PrimitiveCycle α) : ℕ := (representative c).val.length

theorem cycleLength_pos (c : PrimitiveCycle α) : 0 < cycleLength c :=
  List.length_pos_iff.mpr (representative c).property.1

/-- A primitive cycle, a positive repetition, and a distinct root rotation. -/
def CycleIndex (α : Type*) := Σ c : PrimitiveCycle α, ℕ+ × Fin (cycleLength c)

def expand (p : CycleIndex α) : List α :=
  wordPower ((representative p.1).val.rotate p.2.2.val) p.2.1.val

theorem expand_ne_nil (p : CycleIndex α) : expand p ≠ [] := by
  intro he
  have hlen := congrArg List.length he
  simp only [expand,wordPower_length,List.length_rotate,List.length_nil] at hlen
  exact (Nat.ne_of_gt (Nat.mul_pos p.2.1.pos (cycleLength_pos p.1))) hlen

theorem expand_length (p : CycleIndex α) :
    (expand p).length = p.2.1.val * cycleLength p.1 := by
  simp only [expand,wordPower_length,List.length_rotate,cycleLength]

private theorem cycle_eq_of_rotated_representatives {c d : PrimitiveCycle α}
    (h : List.IsRotated (representative c).val (representative d).val) : c = d := by
  have he : Quotient.mk (primitiveSetoid α) (representative c) =
      Quotient.mk (primitiveSetoid α) (representative d) := Quotient.sound h
  simpa only [representative,PrimitiveCycle,Quotient.out_eq] using he

/-- Different cycle, repetition, and root-position data give different words. -/
theorem expand_injective : Function.Injective (expand : CycleIndex α → List α) := by
  rintro ⟨c,m,i⟩ ⟨d,n,j⟩ he
  have hr : (representative c).val.rotate i.val = (representative d).val.rotate j.val :=
    primitive_root_unique ((representative c).property.rotate i.val)
      ((representative d).property.rotate j.val) m.pos n.pos he
  have hcd : c = d := cycle_eq_of_rotated_representatives
    ((show List.IsRotated (representative c).val ((representative c).val.rotate i.val)
      from ⟨i.val,rfl⟩).trans
      (by rw [hr]; exact (show List.IsRotated (representative d).val
        ((representative d).val.rotate j.val) from ⟨j.val,rfl⟩).symm))
  subst d
  have hmn : m = n := by
    apply Subtype.ext
    have hl := congrArg List.length he
    simp only [expand,wordPower_length,List.length_rotate] at hl
    exact Nat.mul_right_cancel (cycleLength_pos c) hl
  subst n
  have hij : i = j := (primitiveRotationEquiv (representative c).val
    (representative c).property).injective (Subtype.ext hr)
  subst j
  rfl

/-- Every nonempty word occurs once in the primitive-cycle indexing. -/
theorem expand_surjective (u : List α) (hu : u ≠ []) : ∃ p : CycleIndex α, expand p = u := by
  obtain ⟨v,n,hv,hn,he⟩ := exists_primitive_root u hu
  let c : PrimitiveCycle α := Quotient.mk (primitiveSetoid α) ⟨v,hv⟩
  have hc : List.IsRotated (representative c).val v :=
    Quotient.exact (Quotient.out_eq c)
  obtain ⟨i,hi⟩ := (primitiveRotationEquiv (representative c).val
    (representative c).property).surjective ⟨v,hc⟩
  refine ⟨⟨c,⟨n,hn⟩,i⟩,?_⟩
  have hrot : (representative c).val.rotate i.val = v := congrArg Subtype.val hi
  change wordPower ((representative c).val.rotate i.val) n = u
  rw [hrot,← he]

/-- The exact countable index change behind primitive-orbit trace products. -/
def wordCycleEquiv : CycleIndex α ≃ {u : List α // u ≠ []} :=
  Equiv.ofBijective (fun p => ⟨expand p,expand_ne_nil p⟩) ⟨
    fun _ _ h => expand_injective (congrArg Subtype.val h),
    fun u => by
      obtain ⟨p,hp⟩ := expand_surjective u.val u.property
      exact ⟨p,Subtype.ext hp⟩⟩

#print axioms expand_length
#print axioms expand_injective
#print axioms expand_surjective
#print axioms wordCycleEquiv
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCycleIndex
