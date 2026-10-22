import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysWittValuedPoint
import GaloisForLFunctions.HTGeometry.SpecStalkLocalization

/-!
# The valued-point description over the spectrum of an algebraically closed field

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), §13.

`Spec K` for an algebraically closed field `K` satisfies the hypotheses under which the `𝒪`-valued
points of `W_rat (X)` are the character triples: it has a single point, and both its stalk and its
residue field there are `K`.
-/

namespace RHTower

open AlgebraicGeometry CategoryTheory HTGeometry

noncomputable section

universe u

variable (K : Type u) [Field K] [IsAlgClosed K]

omit [IsAlgClosed K] in
theorem deningerSpecField_stalk_isDomain
    (x : (Spec (CommRingCat.of K) : Scheme.{u})) :
    IsDomain ((Spec (CommRingCat.of K)).presheaf.stalk x) := by
  letI := (specField_stalk_isField K x).toField
  infer_instance

omit [IsAlgClosed K] in
theorem deningerSpecField_stalk_isIntegrallyClosed
    (x : (Spec (CommRingCat.of K) : Scheme.{u})) :
    letI := deningerSpecField_stalk_isDomain K x
    IsIntegrallyClosed ((Spec (CommRingCat.of K)).presheaf.stalk x) := by
  letI := (specField_stalk_isField K x).toField
  infer_instance

theorem deningerSpecField_residueField_isAlgClosed
    (x : (Spec (CommRingCat.of K) : Scheme.{u})) :
    IsAlgClosed ((Spec (CommRingCat.of K)).residueField x) :=
  IsAlgClosed.of_ringEquiv K _ (specFieldResidueFieldEquiv K x)

theorem deningerSpecField_fractionRing_isAlgClosed
    (x : (Spec (CommRingCat.of K) : Scheme.{u})) :
    letI := deningerSpecField_stalk_isDomain K x
    IsAlgClosed (FractionRing ((Spec (CommRingCat.of K)).presheaf.stalk x)) := by
  letI := (specField_stalk_isField K x).toField
  haveI : IsAlgClosed ((Spec (CommRingCat.of K)).presheaf.stalk x) :=
    IsAlgClosed.of_ringEquiv K _ (specFieldStalkEquiv K x)
  exact deningerIsAlgClosed_fractionRing _

/-- **Deninger, §13.**  Over the spectrum of an algebraically closed field the `𝒪`-valued points of
`W_rat (X)` in the Witt-homomorphism description are the character triples of Definition 13.2. -/
theorem deningerSpecField_wittValuedPointEquiv (O : Type u) [CommRing O] [IsDomain O]
    [IsLocalRing O] :
    Nonempty (DeningerWittValuedPoint (Spec (CommRingCat.of K)) O
      ≃ DeningerValuedCharTriple (Spec (CommRingCat.of K)) O) := by
  letI : ∀ x : (Spec (CommRingCat.of K) : Scheme.{u}),
      IsDomain ((Spec (CommRingCat.of K)).presheaf.stalk x) :=
    deningerSpecField_stalk_isDomain K
  letI : ∀ x : (Spec (CommRingCat.of K) : Scheme.{u}),
      IsAlgClosed ((Spec (CommRingCat.of K)).residueField x) :=
    deningerSpecField_residueField_isAlgClosed K
  letI : ∀ x : (Spec (CommRingCat.of K) : Scheme.{u}),
      IsIntegrallyClosed ((Spec (CommRingCat.of K)).presheaf.stalk x) :=
    deningerSpecField_stalk_isIntegrallyClosed K
  letI : ∀ x : (Spec (CommRingCat.of K) : Scheme.{u}),
      IsAlgClosed (FractionRing ((Spec (CommRingCat.of K)).presheaf.stalk x)) :=
    deningerSpecField_fractionRing_isAlgClosed K
  exact ⟨deningerWittValuedPointEquiv⟩

end

end RHTower
