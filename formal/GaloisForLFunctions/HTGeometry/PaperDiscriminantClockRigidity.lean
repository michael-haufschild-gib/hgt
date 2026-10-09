import GaloisForLFunctions.HTGeometry.PaperDiscriminantClockClassification

/-!
# Faithful root motions and a nonzero surviving discriminant clock

Discriminant inversion does not collapse the polynomial ring or identify
different constant velocity vectors. In particular the surviving common
translation is a nonzero locally nilpotent derivation. The obstruction to
individual root motions also applies to the native `MvPolynomial.pderiv`.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial StableCoordinate

noncomputable section

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

omit [CharZero K] in
/-- Root polynomials embed faithfully into the discriminant-open ring. -/
theorem paperRootDiscriminantOpen_injective (n : ℕ) :
    Function.Injective
      (algebraMap (MvPolynomial (Fin n) K) (PaperRootDiscriminantOpen K n)) := by
  have hV : paperUniversalVandermonde K n ≠ 0 :=
    vandermondeProd_ne_zero X_injective
  exact IsLocalization.injective _
    (powers_le_nonZeroDivisors_of_noZeroDivisors (pow_ne_zero 2 hV))

omit [CharZero K] in
/-- No two different constant root motions become equal after discriminant inversion. -/
theorem paperRootDiscriminantVectorField_injective :
    Function.Injective
      (paperRootDiscriminantVectorField : (Fin n → K) →
        Derivation K (PaperRootDiscriminantOpen K n) (PaperRootDiscriminantOpen K n)) := by
  intro v w h
  funext i
  apply C_injective (Fin n) K
  apply paperRootDiscriminantOpen_injective n
  have he := congrArg
    (fun D : Derivation K (PaperRootDiscriminantOpen K n) (PaperRootDiscriminantOpen K n) =>
      D (algebraMap (MvPolynomial (Fin n) K) (PaperRootDiscriminantOpen K n) (X i))) h
  simpa only [paperRootDiscriminantVectorField, paperNativeLocalization_algebraMap,
    constVectorField_X] using he

/-- For every nonempty root system, common unit translation is a nonzero terminating clock. -/
theorem paperRootDiscriminantTranslation_nontrivial (n : ℕ) :
    paperRootDiscriminantVectorField (fun _ : Fin (n + 1) => (1 : K)) ≠ 0 ∧
      IsLocallyNilpotent
        (paperRootDiscriminantVectorField (fun _ : Fin (n + 1) => (1 : K))) := by
  refine ⟨?_, paperRootDiscriminantTranslation_locallyNilpotent _ _⟩
  intro h
  have he : paperRootDiscriminantVectorField (fun _ : Fin (n + 1) => (1 : K))
      (algebraMap (MvPolynomial (Fin (n + 1)) K) (PaperRootDiscriminantOpen K (n + 1))
        (X 0)) = 0 := by rw [h]; rfl
  have he' :
      algebraMap (MvPolynomial (Fin (n + 1)) K) (PaperRootDiscriminantOpen K (n + 1)) 1 =
      algebraMap (MvPolynomial (Fin (n + 1)) K) (PaperRootDiscriminantOpen K (n + 1)) 0 := by
    simpa only [paperRootDiscriminantVectorField, paperNativeLocalization_algebraMap,
      constVectorField_X, map_one, map_zero] using he
  exact one_ne_zero (paperRootDiscriminantOpen_injective (n + 1) he')

omit [CharZero K] in
private theorem coordinate_vectorField_eq_pderiv (i : Fin n) :
    constVectorField (fun j => if j = i then (1 : K) else 0) = pderiv i := by
  apply derivation_ext
  intro j
  by_cases h : j = i
  · subst j
    simp
  · simp only [constVectorField_X, if_neg h, map_zero, pderiv_X_of_ne h]

/-- Native root partial differentiation survives exactly for a singleton root system. -/
theorem paperRootDiscriminantPartial_locallyNilpotent_iff (i : Fin n) :
    IsLocallyNilpotent
      (paperNativeLocalization (S := PaperRootDiscriminantOpen K n)
        (Submonoid.powers (paperUniversalVandermonde K n ^ 2)) (pderiv i)) ↔
      ∀ j, j = i := by
  rw [← coordinate_vectorField_eq_pderiv]
  exact paperRootDiscriminantCoordinate_locallyNilpotent_iff i

/-- None of the native root partial derivatives remains locally nilpotent with two or more roots. -/
theorem paperRootDiscriminantPartial_not_locallyNilpotent
    (n : ℕ) (i : Fin (n + 2)) :
    ¬ IsLocallyNilpotent
      (paperNativeLocalization (S := PaperRootDiscriminantOpen K (n + 2))
        (Submonoid.powers (paperUniversalVandermonde K (n + 2) ^ 2)) (pderiv i)) := by
  rw [← coordinate_vectorField_eq_pderiv]
  exact paperRootDiscriminantCoordinate_not_locallyNilpotent n i

end

end GaloisForLFunctions.HTGeometry
