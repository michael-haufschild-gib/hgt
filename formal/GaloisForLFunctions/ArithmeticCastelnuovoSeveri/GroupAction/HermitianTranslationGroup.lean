import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.HermitianTranslations
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerConstructedPointCount
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.GroupTheory.PGroup

/-!
# The Hermitian translation p-group

Rational affine Hermitian points form a group under the translation
parameter law. Their already computed cardinality is Q³, so this is
an actual p-group. Its coordinate translations act faithfully on the
Hermitian equation over every extension of the square constants.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "K" => SquareConstantField p s
local notation "HK" => HermitianAffinePoint p s K

/-- The Hermitian parameter law makes the rational Hermitian points an actual group. -/
instance hermitianTranslationGroup : Group HK := by
  letI : Mul HK := ⟨hermitianTranslationProduct p s⟩
  letI : One HK := ⟨hermitianAffineOrigin p s K⟩
  letI : Inv HK := ⟨hermitianTranslationInverse p s⟩
  refine Group.ofLeftAxioms ?_ ?_ ?_
  · intro A B C
    exact (hermitianAffineTranslate_comp p s K A B C).symm
  · intro A
    exact hermitianAffineTranslate_zero p s K A
  · intro A
    change hermitianAffineTranslate p s K (hermitianTranslationInverse p s A) A =
      hermitianAffineOrigin p s K
    have h := hermitianAffineTranslate_inverse_left p s K A (hermitianAffineOrigin p s K)
    rw [hermitianAffineTranslate_origin] at h
    exact h

/-- The actual Hermitian translation group has order Q³. -/
theorem hermitianTranslationGroup_card : Nat.card HK = Q ^ 3 :=
  hermitianAffinePoints_card p s

/-- The rational Hermitian translation group is a p-group for the field characteristic. -/
theorem hermitianTranslationGroup_isPGroup : IsPGroup p HK := by
  apply IsPGroup.of_card (n := (s + 1) * 3)
  exact (hermitianTranslationGroup_card p s).trans (pow_mul p (s + 1) 3).symm

variable (E : Type*) [Field E] [Algebra K E]
local notation "H" => HermitianAffinePoint p s E

/-- Rational Hermitian translations form a permutation representation over every constant extension. -/
def hermitianAffineTranslationHom : HK →* Equiv.Perm H where
  toFun := hermitianAffineTranslationEquiv p s E
  map_one' := by
    apply Equiv.ext
    intro T
    exact hermitianAffineTranslate_zero p s E T
  map_mul' P U := by
    apply Equiv.ext
    intro T
    exact (hermitianAffineTranslate_comp p s E P U T).symm

/-- The translation representation is faithful, as its value at the origin recovers both parameters. -/
theorem hermitianAffineTranslationHom_injective :
    Function.Injective (hermitianAffineTranslationHom p s E) := by
  intro P U h
  have hpoint := congrArg (fun e : Equiv.Perm H => e (hermitianAffineOrigin p s E)) h
  change hermitianAffineTranslate p s E P (hermitianAffineOrigin p s E) =
    hermitianAffineTranslate p s E U (hermitianAffineOrigin p s E) at hpoint
  rw [hermitianAffineTranslate_origin, hermitianAffineTranslate_origin] at hpoint
  apply Subtype.ext
  apply Prod.ext
  · exact (algebraMap K E).injective (congrArg (fun T : H => T.val.1) hpoint)
  · exact (algebraMap K E).injective (congrArg (fun T : H => T.val.2) hpoint)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
