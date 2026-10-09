import GaloisForLFunctions.HTGeometry.PaperSymmetricDiscriminant
import GaloisForLFunctions.HTGeometry.PaperSymmetricPairNormalSpace
import GaloisForLFunctions.HTGeometry.PaperNativeReesHomogeneousInitial

/-!
# The actual normal discriminant of the native symmetric pair

The source homogeneous Rees formula identifies the quadratic discriminant of
the three normal coordinates with the degree-two initial class of the square
of the universal pair determinant. All ideal-power membership is proved here.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Matrix

noncomputable section

variable (K : Type*) [CommRing K]

/-- The discriminant polynomial in the three native coefficient coordinates. -/
def paperSymmetricPairDiscriminantPolynomial : MvPolynomial (Fin 3) K :=
  X 1 ^ 2 - 4 * (X 0 * X 2)

/-- The discriminant has homogeneous coefficient degree two. -/
theorem paperSymmetricPairDiscriminantPolynomial_homogeneous :
    (paperSymmetricPairDiscriminantPolynomial K).IsHomogeneous 2 := by
  unfold paperSymmetricPairDiscriminantPolynomial
  simpa only [one_mul, map_ofNat] using ((isHomogeneous_X K (1 : Fin 3)).pow 2).sub
    (((isHomogeneous_X K (0 : Fin 3)).mul (isHomogeneous_X K (2 : Fin 3))).C_mul 4)

/-- The squared middle coordinate has coefficient one in every coefficient ring. -/
theorem paperSymmetricPairDiscriminantPolynomial_coeff :
    coeff (Finsupp.single 1 2) (paperSymmetricPairDiscriminantPolynomial K) = 1 := by
  have hne : (Finsupp.single 0 1 + Finsupp.single 2 1 : Fin 3 →₀ ℕ) ≠
      Finsupp.single 1 2 := by
    intro h
    have h1 := congrArg (fun d => d (1 : Fin 3)) h
    simp at h1
  have hm : coeff (Finsupp.single 1 2) (X 0 * X 2 : MvPolynomial (Fin 3) K) = 0 := by
    rw [X, X, monomial_mul]
    simp [coeff_monomial, hne]
  rw [paperSymmetricPairDiscriminantPolynomial,
    show (4 : MvPolynomial (Fin 3) K) = C (4 : K) by rw [map_ofNat],
    coeff_sub, coeff_X_pow, coeff_C_mul, hm]
  simp

/-- The determinant of the actual matrix formed by the two universal vectors. -/
def paperSymmetricPairDeterminant : MvPolynomial (Fin 4) K :=
  (!![X 0, X 1; X 2, X 3] : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 4) K)).det

/-- The discriminant of the native pair evaluates to the actual pair determinant squared. -/
theorem paperSymmetricPairDiscriminantPolynomial_eval :
    aeval (paperSymmetricPairGenerator K) (paperSymmetricPairDiscriminantPolynomial K) =
      paperSymmetricPairDeterminant K ^ 2 := by
  calc
    _ = paperSymmetricDiscriminant (paperSymmetricPairGenerator K) := by
      simp only [paperSymmetricPairDiscriminantPolynomial, paperSymmetricDiscriminant,
        map_sub, map_pow, map_mul, map_ofNat, aeval_X, mul_assoc]
    _ = _ := by
      simpa [paperSymmetricPairGenerator, paperSymmetricPairDeterminant, Matrix.det_fin_two] using
        (paperSymmetricDiscriminant_pair
          (![X 0, X 1] : Fin 2 → MvPolynomial (Fin 4) K) ![X 2, X 3])

/-- The squared determinant belongs to the second power of the actual native coefficient ideal. -/
theorem paperSymmetricPairDeterminant_sq_mem :
    paperSymmetricPairDeterminant K ^ 2 ∈ paperSymmetricPairIdeal K ^ 2 := by
  have h := (paperSymmetricPairNormalPresentation K).homogeneous_evaluation_mem
    (paperSymmetricPairDiscriminantPolynomial K) 2
    (paperSymmetricPairDiscriminantPolynomial_homogeneous K)
  change aeval (paperSymmetricPairGenerator K) (paperSymmetricPairDiscriminantPolynomial K) ∈ _ at h
  rwa [paperSymmetricPairDiscriminantPolynomial_eval] at h

/-- The discriminant of the actual three initial classes. -/
def paperSymmetricPairNormalDiscriminant : PaperIdealAssociatedGraded (paperSymmetricPairIdeal K) :=
  paperSymmetricDiscriminant (fun i => paperSymmetricPairNormalMap K (X i))

/-- The actual normal discriminant is the image of the original coefficient discriminant. -/
theorem paperSymmetricPairNormalDiscriminant_eq_map :
    paperSymmetricPairNormalDiscriminant K =
      paperSymmetricPairNormalMap K (paperSymmetricPairDiscriminantPolynomial K) := by
  simp only [paperSymmetricPairNormalDiscriminant, paperSymmetricDiscriminant,
    paperSymmetricPairDiscriminantPolynomial, map_sub, map_pow, map_mul, map_ofNat, mul_assoc]

/-- The actual normal discriminant vanishes exactly when the coefficient ring is trivial. -/
theorem paperSymmetricPairNormalDiscriminant_eq_zero_iff :
    paperSymmetricPairNormalDiscriminant K = 0 ↔ (1 : K) = 0 := by
  constructor
  · intro h
    rw [paperSymmetricPairNormalDiscriminant_eq_map] at h
    have hp := (paperSymmetricPairNormalMap_eq_zero_iff K _).mp h
    have hc := paperSymmetricPairDiscriminantPolynomial_coeff K
    rw [hp, coeff_zero] at hc
    exact hc.symm
  · intro h
    have h1 : (1 : MvPolynomial (Fin 3) K) = 0 := by
      simpa only [map_one, map_zero] using congrArg (C : K → MvPolynomial (Fin 3) K) h
    have hp : paperSymmetricPairDiscriminantPolynomial K = 0 := by
      calc
        _ = paperSymmetricPairDiscriminantPolynomial K * 1 := (mul_one _).symm
        _ = 0 := by rw [h1, mul_zero]
    rw [paperSymmetricPairNormalDiscriminant_eq_map, hp, map_zero]

/-- Exact geometric content: the normal discriminant is the degree-two initial class
of the actual squared pair determinant. -/
theorem paperSymmetricPairNormalDiscriminant_eq_initial :
    paperSymmetricPairNormalDiscriminant K =
      paperNativeReesSpecialization (paperSymmetricPairIdeal K)
        (ReesGrading.mono (paperSymmetricPairIdeal K) 2 (paperSymmetricPairDeterminant K ^ 2)
          (paperSymmetricPairDeterminant_sq_mem K)) := by
  rw [paperSymmetricPairNormalDiscriminant_eq_map]
  change paperNativeReesSpecialization (paperSymmetricPairIdeal K)
    (paperNativeReesMvPolynomialMap (paperSymmetricPairIdeal K)
      (paperSymmetricPairNormalPresentation K).idealElements
      (paperSymmetricPairDiscriminantPolynomial K)) = _
  apply congrArg (paperNativeReesSpecialization (paperSymmetricPairIdeal K))
  apply Subtype.ext
  exact (paperNativeReesMvPolynomialMap_homogeneous (paperSymmetricPairIdeal K)
    (paperSymmetricPairNormalPresentation K).idealElements
    (paperSymmetricPairDiscriminantPolynomial K) 2
    (paperSymmetricPairDiscriminantPolynomial_homogeneous K)).trans
      (congrArg (Polynomial.monomial 2) (paperSymmetricPairDiscriminantPolynomial_eval K))

end

end GaloisForLFunctions.HTGeometry
