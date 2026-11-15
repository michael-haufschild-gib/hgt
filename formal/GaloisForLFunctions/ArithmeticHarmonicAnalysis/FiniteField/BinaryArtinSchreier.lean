import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.GroupWithZero.Idempotent
import Mathlib.Tactic.Ring

/-!
# Binary Artin–Schreier maps and their fibres

The map `x ↦ x² + x` is linear over the binary prime field and commutes with
ring homomorphisms. Its kernel consists exactly of idempotents; over fields
this is the prime-field line. Translating by a solution identifies its whole
fibre with the kernel, without any reducedness assumption on the algebra.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open Module

/-- The binary Artin–Schreier operator as a linear map over the prime field. -/
def binaryArtinSchreier (A : Type*) [CommRing A] [Algebra (ZMod 2) A] : A →ₗ[ZMod 2] A where
  toFun x := x ^ 2 + x
  map_add' x y := by
    have hz : x * y + x * y = 0 := by
      simpa only [add_smul, one_smul, zero_smul] using
        congrArg (fun c : ZMod 2 => c • (x * y)) (CharTwo.add_self_eq_zero (1 : ZMod 2))
    calc
      (x + y) ^ 2 + (x + y) = (x ^ 2 + x) + (y ^ 2 + y) + (x * y + x * y) := by ring
      _ = _ := by rw [hz, add_zero]
  map_smul' c x := by
    by_cases hc : c = 0
    · simp [hc]
    · have hc1 : c = 1 := by simpa using ZMod.pow_card_sub_one_eq_one hc
      simp [hc1]

@[simp]
theorem binaryArtinSchreier_apply (A : Type*) [CommRing A] [Algebra (ZMod 2) A] (x : A) :
    binaryArtinSchreier A x = x ^ 2 + x := rfl

/-- Over any binary algebra, the Artin–Schreier kernel consists exactly of idempotents. -/
theorem mem_ker_binaryArtinSchreier_iff_square
    (A : Type*) [CommRing A] [Algebra (ZMod 2) A] (x : A) :
    x ∈ (binaryArtinSchreier A).ker ↔ x ^ 2 = x := by
  have hx : x + x = 0 := by
    simpa only [add_smul, one_smul, zero_smul] using
      congrArg (fun c : ZMod 2 => c • x) (CharTwo.add_self_eq_zero (1 : ZMod 2))
  change x ^ 2 + x = 0 ↔ x ^ 2 = x
  constructor
  · intro h
    have h' := congrArg (fun z : A => z + x) h
    simpa only [add_assoc, hx, add_zero, zero_add] using h'
  · intro h
    rw [h, hx]

variable (L : Type*) [Field L] [Algebra (ZMod 2) L]

/-- The kernel of the binary Artin–Schreier operator is exactly the prime-field line. -/
theorem ker_binaryArtinSchreier :
    (binaryArtinSchreier L).ker = Submodule.span (ZMod 2) {(1 : L)} := by
  have hone : (1 : L) + 1 = 0 := by
    simpa only [add_smul, one_smul, zero_smul] using
      congrArg (fun c : ZMod 2 => c • (1 : L)) (CharTwo.add_self_eq_zero (1 : ZMod 2))
  have hmapone : binaryArtinSchreier L 1 = 0 := by
    simpa only [binaryArtinSchreier_apply, one_pow] using hone
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro hx
    have hp : x * (x + 1) = 0 := by
      calc
        x * (x + 1) = x ^ 2 + x := by ring
        _ = 0 := hx
    rcases mul_eq_zero.mp hp with hx0 | hx1
    · exact ⟨0, by rw [zero_smul, hx0]⟩
    · have hxone : x = 1 := by
        have h := congrArg (fun z : L => z + 1) hx1
        simpa only [add_assoc, hone, add_zero, zero_add] using h
      exact ⟨1, by rw [one_smul, hxone]⟩
  · rintro ⟨c, rfl⟩
    rw [map_smul, hmapone, smul_zero]


/-- The binary Artin–Schreier operator commutes with every ring homomorphism. -/
theorem binaryArtinSchreier_map {A B : Type*} [CommRing A] [CommRing B]
    [Algebra (ZMod 2) A] [Algebra (ZMod 2) B] (f : A →+* B) (x : A) :
    f (binaryArtinSchreier A x) = binaryArtinSchreier B (f x) := by
  simp only [binaryArtinSchreier_apply, map_add, map_pow]

/-- The Artin–Schreier kernel is canonically the set of ring idempotents. -/
def binaryArtinSchreierKernelEquivIdempotents
    (A : Type*) [CommRing A] [Algebra (ZMod 2) A] :
    (binaryArtinSchreier A).ker ≃ {x : A // IsIdempotentElem x} where
  toFun x := ⟨x.1, by
    have h := (mem_ker_binaryArtinSchreier_iff_square A x.1).mp x.2
    exact (pow_two x.1).symm.trans h⟩
  invFun x := ⟨x.1, (mem_ker_binaryArtinSchreier_iff_square A x.1).mpr
    ((pow_two x.1).trans x.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Translation by a solution identifies its whole fibre with the kernel. -/
def binaryArtinSchreierFibreEquivKernel
    (A : Type*) [CommRing A] [Algebra (ZMod 2) A] (x : A) :
    {y : A // binaryArtinSchreier A y = binaryArtinSchreier A x} ≃
      (binaryArtinSchreier A).ker where
  toFun y := ⟨y.1 - x, by
    change binaryArtinSchreier A (y.1 - x) = 0
    rw [map_sub, y.2, sub_self]⟩
  invFun y := ⟨y.1 + x, by
    rw [map_add, show binaryArtinSchreier A y.1 = 0 from y.2, zero_add]⟩
  left_inv y := Subtype.ext (sub_add_cancel y.1 x)
  right_inv y := Subtype.ext (add_sub_cancel_right y.1 x)

#print axioms binaryArtinSchreier
#print axioms ker_binaryArtinSchreier
#print axioms mem_ker_binaryArtinSchreier_iff_square
#print axioms binaryArtinSchreier_map
#print axioms binaryArtinSchreierKernelEquivIdempotents
#print axioms binaryArtinSchreierFibreEquivKernel
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
