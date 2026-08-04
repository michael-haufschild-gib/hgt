import GaloisForLFunctions.HTGeometry.JetHypertranscendence

/-!
# The formal jet derivation on the fraction-ring presentation

The free differential rational field is a `def` wrapping the fraction ring of the jet polynomial
ring and carries its own field instance.  The ring operations of the two presentations are
definitionally equal, but the `Derivation` structure carries module instance arguments that the
elaborator will not identify, so a derivation of one presentation cannot be cast to the other.

Rebuilding the jet derivation directly on the fraction-ring presentation removes the obstacle: the
underlying function is the same and every structure field transfers by definitional unfolding.  This
is what makes a derivation transported from an ambient differential field comparable with the formal
one.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

open JetField

noncomputable section

variable {C ι : Type*} [Field C]

/-- The formal jet derivation, presented on the fraction ring of the jet polynomial ring. -/
def jetDerivationFractionBase :
    Derivation C (FractionRing (MvPolynomial (ι × ℕ) C))
      (FractionRing (MvPolynomial (ι × ℕ) C)) := by
  refine Derivation.mk'
    { toFun := fun x : FractionRing (MvPolynomial (ι × ℕ) C) =>
        (jetDerivation (C := C) (ι := ι) x : FractionRing (MvPolynomial (ι × ℕ) C))
      map_add' := fun a b => by exact map_add (jetDerivation (C := C) (ι := ι)) a b
      map_smul' := fun c x => by
        exact (jetDerivation (C := C) (ι := ι)).map_smul c x } ?_
  intro a b
  have hleib := (jetDerivation (C := C) (ι := ι)).leibniz a b
  exact hleib

/-- The same derivation over the integers, in the shape a differential structure carries. -/
def jetDerivationFraction :
    Derivation ℤ (FractionRing (MvPolynomial (ι × ℕ) C))
      (FractionRing (MvPolynomial (ι × ℕ) C)) :=
  (jetDerivationFractionBase (C := C) (ι := ι)).restrictScalars ℤ

@[simp] theorem jetDerivationFraction_apply (x : FractionRing (MvPolynomial (ι × ℕ) C)) :
    jetDerivationFraction x = (jetDerivation (C := C) (ι := ι) x :
      FractionRing (MvPolynomial (ι × ℕ) C)) := rfl

/-- The rebuilt derivation advances each jet coordinate. -/
theorem jetDerivationFraction_jet (p : ι × ℕ) :
    jetDerivationFraction (jet p : FractionRing (MvPolynomial (ι × ℕ) C)) =
      (jet (p.1, p.2 + 1) : FractionRing (MvPolynomial (ι × ℕ) C)) :=
  deriv_jet p

/-- The rebuilt derivation kills the base field. -/
theorem jetDerivationFraction_algebraMap (c : C) :
    jetDerivationFraction
      (algebraMap C (FractionRing (MvPolynomial (ι × ℕ) C)) c) = 0 :=
  (jetDerivation (C := C) (ι := ι)).map_algebraMap c

end

end GaloisForLFunctions.HTGeometry
