import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerConstantBaseChange
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.IntrinsicPlaceEquivalences
import GaloisForLFunctions.HTGeometry.SpecStalkLocalization

/-!
# Rational places of literal Kummer constant tensors

The explicit tensor equivalence gives the existing tensor ring a field
structure. Inverse pullback then identifies its actual rational valuation
places with those of the same Kummer equation over the enlarged constants.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open scoped TensorProduct
variable (K E : Type*) [Field K] [Field E] [Algebra K E] [FiniteDimensional K E]
variable (c : Kˣ) (b R n : ℕ)
local notation "L" => KummerBranchField c b R n
local notation "T" => E ⊗[K] L
local notation "L'" => KummerBranchField (Units.map (RingHom.toMonoidHom (algebraMap K E)) c) b R n

/-- The literal scalar tensor is a field with its original ring operations. -/
@[implicit_reducible] def kummerConstantTensorField : Field T :=
  IsField.toField (_root_.HTGeometry.isField_of_ringEquiv
    (kummerConstantTensorEquiv K E c b R n).symm.toRingEquiv (Field.toIsField L'))

/-- Actual rational valuation places of the literal scalar tensor field. -/
abbrev KummerConstantTensorRationalPlaces :=
  letI := kummerConstantTensorField K E c b R n
  RationalConstantFieldPlaces E T

/-- Rational places of the literal tensor correspond to those of the same equation over the extended constants. -/
def kummerConstantTensorRationalPlaceEquiv :
    KummerConstantTensorRationalPlaces K E c b R n ≃ RationalConstantFieldPlaces E L' := by
  letI := kummerConstantTensorField K E c b R n
  exact rationalConstantFieldPlaceEquiv (kummerConstantTensorEquiv K E c b R n)

/-- Counting rational places on the extended equation counts the actual scalar tensor field. -/
theorem kummerConstantTensor_rationalPlaces_card :
    Nat.card (KummerConstantTensorRationalPlaces K E c b R n) =
      Nat.card (RationalConstantFieldPlaces E L') :=
  Nat.card_congr (kummerConstantTensorRationalPlaceEquiv K E c b R n)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
