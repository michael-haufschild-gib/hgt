import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.FrobeniusPowerField

/-!
# Frobenius as an isomorphism onto its power field

The `p`th-power map is injective on a field and surjective onto its
actual image. Its inverse gives unique Frobenius roots of coefficients
in that image, preserving sums and products.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable (K L : Type*) [Field K] [Field L] [Algebra K L] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p]

private def frobeniusPowerHom : L →+* frobeniusPowerField K L p where
  toFun := frobeniusPowerElement K L p
  map_zero' := Subtype.ext (zero_pow (Fact.out : p.Prime).ne_zero)
  map_one' := Subtype.ext (one_pow p)
  map_add' a b := Subtype.ext ((frobenius L p).map_add a b)
  map_mul' a b := Subtype.ext ((frobenius L p).map_mul a b)

/-- Frobenius identifies the field with its actual subfield of `p`th powers. -/
def frobeniusPowerFieldEquiv : L ≃+* frobeniusPowerField K L p :=
  RingEquiv.ofBijective (frobeniusPowerHom K L p) ⟨
    fun x y h => (frobenius L p).injective (congrArg Subtype.val h),
    fun a => by
      obtain ⟨x, hx⟩ := a.property
      exact ⟨x, Subtype.ext hx⟩⟩

/-- The Frobenius field isomorphism is the literal `p`th-power map. -/
theorem frobeniusPowerFieldEquiv_apply (x : L) :
    frobeniusPowerFieldEquiv K L p x = frobeniusPowerElement K L p x := rfl

/-- The inverse isomorphism takes each Frobenius coefficient to its unique actual root. -/
theorem frobeniusPowerFieldEquiv_symm_pow (a : frobeniusPowerField K L p) :
    (frobeniusPowerFieldEquiv K L p).symm a ^ p = (a : L) :=
  congrArg Subtype.val ((frobeniusPowerFieldEquiv K L p).apply_symm_apply a)

/-- Extracting the Frobenius root of an ambient `p`th power recovers the original element. -/
theorem frobeniusPowerFieldEquiv_symm_element (x : L) :
    (frobeniusPowerFieldEquiv K L p).symm (frobeniusPowerElement K L p x) = x :=
  (frobeniusPowerFieldEquiv K L p).symm_apply_apply x

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
