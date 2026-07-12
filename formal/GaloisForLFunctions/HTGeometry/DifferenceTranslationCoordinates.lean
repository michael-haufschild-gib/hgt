import GaloisForLFunctions.HTGeometry.StanleyReisnerFacetCoordinates

/-!
# Difference and translation coordinates

The polynomial coordinate change `x_v = t_v - 1` is an algebra automorphism of the multivariate
polynomial ring, with inverse `t_v = x_v + 1`.  It converts Stanley--Reisner difference monomials
into their finite translation-orbit coefficient expansions without changing algebraic rank.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

/-- Substitute `t_i - 1` for every difference variable. -/
def differenceToTranslationHom
    {R α : Type*} [CommRing R] :
    MvPolynomial α R →ₐ[R] MvPolynomial α R :=
  MvPolynomial.aeval fun i => X i - 1

/-- Substitute `x_i + 1` for every translation variable. -/
def translationToDifferenceHom
    {R α : Type*} [CommRing R] :
    MvPolynomial α R →ₐ[R] MvPolynomial α R :=
  MvPolynomial.aeval fun i => X i + 1

/-- Translation-to-difference substitution is a left inverse. -/
theorem translationToDifference_comp_differenceToTranslation
    {R α : Type*} [CommRing R] :
    (translationToDifferenceHom (R := R) (α := α)).comp
      (differenceToTranslationHom (R := R) (α := α)) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [translationToDifferenceHom, differenceToTranslationHom]

/-- Difference-to-translation substitution is a left inverse. -/
theorem differenceToTranslation_comp_translationToDifference
    {R α : Type*} [CommRing R] :
    (differenceToTranslationHom (R := R) (α := α)).comp
      (translationToDifferenceHom (R := R) (α := α)) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [translationToDifferenceHom, differenceToTranslationHom]

/-- The exact algebra equivalence between difference and translation coordinates. -/
def differenceTranslationEquiv
    {R α : Type*} [CommRing R] :
    MvPolynomial α R ≃ₐ[R] MvPolynomial α R where
  toFun := differenceToTranslationHom
  invFun := translationToDifferenceHom
  left_inv P := by
    exact AlgHom.congr_fun translationToDifference_comp_differenceToTranslation P
  right_inv P := by
    exact AlgHom.congr_fun differenceToTranslation_comp_translationToDifference P
  map_mul' := map_mul differenceToTranslationHom
  map_add' := map_add differenceToTranslationHom
  commutes' := (differenceToTranslationHom).commutes

/-- A difference generator becomes `t_i - 1`. -/
@[simp] theorem differenceTranslationEquiv_X
    {R α : Type*} [CommRing R] (i : α) :
    differenceTranslationEquiv (R := R) (X i) = X i - 1 := by
  simp [differenceTranslationEquiv, differenceToTranslationHom]

/-- A translation generator becomes `x_i + 1` under the inverse coordinate change. -/
@[simp] theorem differenceTranslationEquiv_symm_X
    {R α : Type*} [CommRing R] (i : α) :
    (differenceTranslationEquiv (R := R)).symm (X i) = X i + 1 := by
  simp [differenceTranslationEquiv, translationToDifferenceHom]

end

end GaloisForLFunctions.HTGeometry
