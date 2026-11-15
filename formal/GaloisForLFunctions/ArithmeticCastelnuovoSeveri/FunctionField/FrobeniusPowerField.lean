import GaloisForLFunctions.HTGeometry.RadicalDegreeExact
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical


/-!
# Frobenius power subfields over finite constants

The `p`th powers form an intermediate field over finite constants.
Every element outside this field generates a purely inseparable extension
of degree `p`. A uniformizer is outside it, as its order is not divisible
by the characteristic.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
open scoped IntermediateField
variable (K L : Type*) [Field K] [Field L] [Algebra K L] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p]

/-- The `p`th-power subfield contains the finite constant field. -/
def frobeniusPowerField : IntermediateField K L where
  toSubalgebra := {
    toSubsemiring := (frobenius L p).fieldRange.toSubring.toSubsemiring
    algebraMap_mem' := by
      intro a
      obtain ⟨b, hb⟩ := Finite.surjective_of_injective (frobenius K p).injective a
      refine ⟨algebraMap K L b, ?_⟩
      change b ^ p = a at hb
      change (algebraMap K L b) ^ p = algebraMap K L a
      rw [← map_pow, hb] }
  inv_mem' := fun _ hx => (frobenius L p).fieldRange.inv_mem hx

/-- Membership in the Frobenius field means being a `p`th power in the ambient field. -/
theorem mem_frobeniusPowerField (x : L) :
    x ∈ frobeniusPowerField K L p ↔ ∃ y : L, y ^ p = x := Iff.rfl

/-- An ambient `p`th power, viewed as an element of the Frobenius field. -/
def frobeniusPowerElement (x : L) : frobeniusPowerField K L p := ⟨x ^ p, ⟨x, rfl⟩⟩

/-- A uniformizer cannot be a `p`th power. -/
theorem frobeniusPowerField_uniformizer_notMem
    (v : Valuation L (WithZero (Multiplicative ℤ))) (π : L)
    (hπ : v π = WithZero.exp (-1 : ℤ)) : π ∉ frobeniusPowerField K L p := by
  rintro ⟨y, hy⟩
  change y ^ p = π at hy
  have h := congrArg (fun x => WithZero.log (v x)) hy
  rw [map_pow, WithZero.log_pow, hπ, WithZero.log_exp, nsmul_eq_mul] at h
  have hd : (p : ℤ) ∣ (-1 : ℤ) := ⟨WithZero.log (v y), h.symm⟩
  have hd' : p ∣ 1 := Int.natCast_dvd_natCast.mp (dvd_neg.mp hd)
  exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp hd')

/-- A non-`p`th-power element has irreducible purely inseparable equation over the Frobenius field. -/
theorem frobeniusPowerField_irreducible (x : L) (hx : x ∉ frobeniusPowerField K L p) :
    Irreducible (X ^ p - C (frobeniusPowerElement K L p x)) := by
  apply X_pow_sub_C_irreducible_of_prime (Fact.out : p.Prime)
  intro b hb
  have hpow : (b : L) ^ p = x ^ p := congrArg Subtype.val hb
  have he : (b : L) = x := (frobenius L p).injective hpow
  exact hx (he ▸ b.property)

/-- Every element outside the Frobenius field generates degree exactly the characteristic. -/
theorem frobeniusPowerField_adjoin_finrank (x : L) (hx : x ∉ frobeniusPowerField K L p) :
    Module.finrank (frobeniusPowerField K L p) (frobeniusPowerField K L p)⟮x⟯ = p :=
  GaloisForLFunctions.HTGeometry.finrank_adjoin_of_irreducible (Fact.out : p.Prime).pos
    (frobeniusPowerField_irreducible K L p x hx) rfl

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
