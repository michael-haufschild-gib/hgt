import GaloisForLFunctions.HTGeometry.PaperDiscriminantConstantDirections
import GaloisForLFunctions.HTGeometry.PaperNativeInvariantLocalization

/-!
# Constant root clocks on the discriminant-open space

Applying the source invariant-localization theorem to the native vector
fields gives an exact classification: local nilpotence survives inversion
of the discriminant precisely for equal root velocities. Simultaneous
translation is the positive survivor; every individual root motion fails
as soon as at least two roots are present.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial StableCoordinate

noncomputable section

/-- The ordered universal root space with the discriminant inverted. -/
abbrev PaperRootDiscriminantOpen (K : Type*) [CommRing K] (n : ℕ) :=
  Localization.Away (paperUniversalVandermonde K n ^ 2)

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-- The native quotient-rule extension of an arbitrary constant root velocity. -/
def paperRootDiscriminantVectorField (v : Fin n → K) :
    Derivation K (PaperRootDiscriminantOpen K n) (PaperRootDiscriminantOpen K n) :=
  paperNativeLocalization (Submonoid.powers (paperUniversalVandermonde K n ^ 2))
    (constVectorField v)

/-- Discriminant inversion preserves termination exactly for simultaneous root translation. -/
theorem paperRootDiscriminantVectorField_locallyNilpotent_iff (v : Fin n → K) :
    IsLocallyNilpotent (paperRootDiscriminantVectorField v) ↔ ∀ i j, v i = v j := by
  exact (paperNativeAway_locallyNilpotent_iff (constVectorField v)
    (paperConstantVectorField_locallyNilpotent v) _).trans
      (paperConstantVectorField_vandermonde_sq_eq_zero_iff v)

/-- Inverting the unsquared Vandermonde gives the identical classification. -/
theorem paperRootVandermondeVectorField_locallyNilpotent_iff (v : Fin n → K) :
    IsLocallyNilpotent
      (paperNativeLocalization
        (S := Localization.Away (paperUniversalVandermonde K n))
        (Submonoid.powers (paperUniversalVandermonde K n)) (constVectorField v)) ↔
      ∀ i j, v i = v j := by
  exact (paperNativeAway_locallyNilpotent_iff (constVectorField v)
    (paperConstantVectorField_locallyNilpotent v) _).trans
      (paperConstantVectorField_vandermonde_eq_zero_iff v)

/-- Simultaneous translation at every speed survives on the discriminant-open space. -/
theorem paperRootDiscriminantTranslation_locallyNilpotent (n : ℕ) (c : K) :
    IsLocallyNilpotent (paperRootDiscriminantVectorField (fun _ : Fin n => c)) :=
  (paperRootDiscriminantVectorField_locallyNilpotent_iff _).mpr (fun _ _ => rfl)

/-- An individual root motion survives precisely when it is the only root. -/
theorem paperRootDiscriminantCoordinate_locallyNilpotent_iff (i : Fin n) :
    IsLocallyNilpotent
      (paperRootDiscriminantVectorField (fun j => if j = i then (1 : K) else 0)) ↔
      ∀ j, j = i := by
  rw [paperRootDiscriminantVectorField_locallyNilpotent_iff]
  constructor
  · intro h j
    by_contra hji
    have he := h i j
    simp only [if_neg hji] at he
    exact one_ne_zero he
  · intro h i j
    rw [h i, h j]

/-- With at least two roots, every individual root motion loses local nilpotence. -/
theorem paperRootDiscriminantCoordinate_not_locallyNilpotent
    (n : ℕ) (i : Fin (n + 2)) :
    ¬ IsLocallyNilpotent
      (paperRootDiscriminantVectorField (fun j => if j = i then (1 : K) else 0)) := by
  rw [paperRootDiscriminantCoordinate_locallyNilpotent_iff]
  intro h
  have he : (0 : Fin (n + 2)) = 1 := (h 0).trans (h 1).symm
  have := congrArg Fin.val he
  simp at this

end

end GaloisForLFunctions.HTGeometry
