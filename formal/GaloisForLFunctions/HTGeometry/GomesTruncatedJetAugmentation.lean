import GaloisForLFunctions.HTGeometry.GomesTruncatedJetOrderAlgebra
import GaloisForLFunctions.HTGeometry.GomesFiniteFockSymmetrySpectrum

/-!
# The scalar coordinate of every joint clock symmetry

Reading the first diagonal entry is an algebra homomorphism on the entire
joint algebra. It controls every diagonal entry, the determinant and the full
characteristic polynomial, without a choice of polynomial representative.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The actual first diagonal entry, as an algebra homomorphism on joint symmetries. -/
def gomesTruncatedJetAugmentation (n : ℕ) (z : ℂ) :
    gomesTruncatedJetJointAlgebra n z →ₐ[ℂ] ℂ where
  toFun E := E.val 0 0
  map_one' := by simp
  map_zero' := rfl
  map_add' E F := rfl
  map_mul' E F := by
    obtain ⟨p, hp⟩ := (gomesFiniteFock_commute_iff_polynomial (n + 1) E.val).mp
      ((gomesTruncatedJetJointAlgebra_mem_iff n z E.val).mp E.property).1
    obtain ⟨q, hq⟩ := (gomesFiniteFock_commute_iff_polynomial (n + 1) F.val).mp
      ((gomesTruncatedJetJointAlgebra_mem_iff n z F.val).mp F.property).1
    change (E.val * F.val) 0 0 = E.val 0 0 * F.val 0 0
    rw [← hp, ← hq, ← map_mul]
    simp only [gomesFiniteFockPolynomialHom_diagonal, Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.eval_mul]
  commutes' r := by simp [Matrix.algebraMap_eq_diagonal]

/-- The augmentation is a literal matrix observation. -/
theorem gomesTruncatedJetAugmentation_apply (n : ℕ) (z : ℂ)
    (E : gomesTruncatedJetJointAlgebra n z) :
    gomesTruncatedJetAugmentation n z E = E.val 0 0 := rfl

/-- Every diagonal entry of a joint symmetry equals its scalar coordinate. -/
theorem gomesTruncatedJetJointAlgebra_diagonal (n : ℕ) (z : ℂ)
    (E : gomesTruncatedJetJointAlgebra n z) (i : Fin (n + 1)) :
    E.val i i = gomesTruncatedJetAugmentation n z E := by
  obtain ⟨p, hp⟩ := (gomesFiniteFock_commute_iff_polynomial (n + 1) E.val).mp
    ((gomesTruncatedJetJointAlgebra_mem_iff n z E.val).mp E.property).1
  rw [gomesTruncatedJetAugmentation_apply, ← hp,
    gomesFiniteFockPolynomialHom_diagonal, gomesFiniteFockPolynomialHom_diagonal]

/-- The determinant of every joint symmetry is exactly the horizon power of its scalar coordinate. -/
theorem gomesTruncatedJetJointAlgebra_det (n : ℕ) (z : ℂ)
    (E : gomesTruncatedJetJointAlgebra n z) :
    E.val.det = gomesTruncatedJetAugmentation n z E ^ (n + 1) := by
  obtain ⟨p, hp⟩ := (gomesFiniteFock_commute_iff_polynomial (n + 1) E.val).mp
    ((gomesTruncatedJetJointAlgebra_mem_iff n z E.val).mp E.property).1
  rw [gomesTruncatedJetAugmentation_apply, ← hp,
    gomesFiniteFockPolynomialHom_det, gomesFiniteFockPolynomialHom_diagonal]

/-- Every joint symmetry has a single characteristic root with the full jet multiplicity. -/
theorem gomesTruncatedJetJointAlgebra_charpoly (n : ℕ) (z : ℂ)
    (E : gomesTruncatedJetJointAlgebra n z) :
    E.val.charpoly = (Polynomial.X - Polynomial.C (gomesTruncatedJetAugmentation n z E)) ^
      (n + 1) := by
  obtain ⟨p, hp⟩ := (gomesFiniteFock_commute_iff_polynomial (n + 1) E.val).mp
    ((gomesTruncatedJetJointAlgebra_mem_iff n z E.val).mp E.property).1
  rw [gomesTruncatedJetAugmentation_apply, ← hp,
    gomesFiniteFockPolynomialHom_charpoly, gomesFiniteFockPolynomialHom_diagonal]

/-- The scalar observation alone decides ambient invertibility of a joint symmetry. -/
theorem gomesTruncatedJetJointAlgebra_isUnit_iff (n : ℕ) (z : ℂ)
    (E : gomesTruncatedJetJointAlgebra n z) :
    IsUnit E.val ↔ gomesTruncatedJetAugmentation n z E ≠ 0 := by
  obtain ⟨p, hp⟩ := (gomesFiniteFock_commute_iff_polynomial (n + 1) E.val).mp
    ((gomesTruncatedJetJointAlgebra_mem_iff n z E.val).mp E.property).1
  rw [gomesTruncatedJetAugmentation_apply, ← hp,
    gomesFiniteFockPolynomialHom_isUnit_iff, gomesFiniteFockPolynomialHom_diagonal]

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
