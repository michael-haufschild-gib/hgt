import GaloisForLFunctions.HTGeometry.QNMFeshbachResponse
import GaloisForLFunctions.HTGeometry.AuxiliaryTorsionSchurComplement

/-!
# Coordinate covariance of Schur elimination and observable response

The split-coordinate mechanism of arXiv:2609.20367, Lemma 6.30 and
Lemma 8.5, applies to the corpus's Schur, QNM/Feshbach, and auxiliary-torsion
operators. Its algebraic part holds for arbitrary linear coordinate
equivalences. Transporting the source and observer with the blocks preserves
the scalar response, including the direct background and any inverse defect.

The candidate exterior inverse need not solve an inverse equation: its defect
is transported exactly. These identities make no positivity assertion.
-/

namespace GaloisForLFunctions.HTGeometry

variable {R F H F' H' : Type*} [CommRing R]
  [AddCommGroup F] [Module R F] [AddCommGroup H] [Module R H]
  [AddCommGroup F'] [Module R F'] [AddCommGroup H'] [Module R H']

/-- Elimination commutes with a split change of coordinates. -/
theorem schurComplement_coordinate_covariance
    (U : F ≃ₗ[R] F') (V : H ≃ₗ[R] H')
    (A : F →ₗ[R] F) (B : H →ₗ[R] F) (C : F →ₗ[R] H) (G : H →ₗ[R] H) :
    schurComplement (U.conj A) (LinearEquiv.arrowCongr V U B)
        (LinearEquiv.arrowCongr U V C) (V.conj G) =
      U.conj (schurComplement A B C G) := by
  ext x
  simp [schurComplement, map_sub]

/-- The full block operator undergoes the same split conjugation. -/
theorem schurBlockOperator_coordinate_covariance
    (U : F ≃ₗ[R] F') (V : H ≃ₗ[R] H')
    (A : F →ₗ[R] F) (B : H →ₗ[R] F) (C : F →ₗ[R] H) (D : H →ₗ[R] H) :
    schurBlockOperator (U.conj A) (LinearEquiv.arrowCongr V U B)
        (LinearEquiv.arrowCongr U V C) (V.conj D) =
      (U.prodCongr V).conj (schurBlockOperator A B C D) := by
  ext p <;> simp [schurBlockOperator]

/-- Both retained and eliminated components of a forced response transform
with their own coordinate frames. -/
theorem qnmFeshbachLift_coordinate_covariance
    (U : F ≃ₗ[R] F') (V : H ≃ₗ[R] H')
    (C : F →ₗ[R] H) (G : H →ₗ[R] H) (x : F) (g : H) :
    qnmFeshbachLift (LinearEquiv.arrowCongr U V C) (V.conj G) (U x) (V g) =
      (U.prodCongr V) (qnmFeshbachLift C G x g) := by
  simp [qnmFeshbachLift, ← map_sub]

/-- A coordinate change cannot hide the error of a candidate exterior inverse. -/
theorem qnmFeshbach_residual_coordinate_covariance
    (U : F ≃ₗ[R] F') (V : H ≃ₗ[R] H')
    (A : F →ₗ[R] F) (B : H →ₗ[R] F) (C : F →ₗ[R] H)
    (D G : H →ₗ[R] H) (x f : F) (g : H) :
    schurBlockOperator (U.conj A) (LinearEquiv.arrowCongr V U B)
        (LinearEquiv.arrowCongr U V C) (V.conj D)
        (qnmFeshbachLift (LinearEquiv.arrowCongr U V C) (V.conj G) (U x) (V g)) -
      (U f, V g) =
      (U (schurComplement A B C G x - (f - B (G g))),
        V ((D.comp G - (LinearMap.id : H →ₗ[R] H)) (g - C x))) := by
  rw [qnmFeshbach_residual, schurComplement_coordinate_covariance]
  simp [← map_sub]

/-- Transporting the two observer rows contragrediently preserves the complete
observable amplitude, with its direct-source background included. -/
theorem qnmFeshbach_observed_coordinate_covariance
    (U : F ≃ₗ[R] F') (V : H ≃ₗ[R] H')
    (C : F →ₗ[R] H) (G : H →ₗ[R] H)
    (O : F →ₗ[R] R) (P : H →ₗ[R] R) (x : F) (g : H) :
    (O.comp U.symm.toLinearMap)
        (qnmFeshbachLift (LinearEquiv.arrowCongr U V C) (V.conj G) (U x) (V g)).1 +
      (P.comp V.symm.toLinearMap)
        (qnmFeshbachLift (LinearEquiv.arrowCongr U V C) (V.conj G) (U x) (V g)).2 =
      (O - P ∘ₗ G ∘ₗ C) x + P (G g) := by
  rw [qnmFeshbachLift_coordinate_covariance]
  simpa using qnmFeshbach_observed C G O P x g

/-- The eliminated torsion contact coefficient is independent of both source
and auxiliary scalar coordinate choices. -/
theorem auxiliaryTorsionSchur_coordinate_invariance
    (U V : ℝ ≃ₗ[ℝ] ℝ) (logKappa source : ℝ) :
    schurComplement (U.conj 0)
        (LinearEquiv.arrowCongr V U (auxiliaryTorsionCoupling logKappa))
        (LinearEquiv.arrowCongr U V (auxiliaryTorsionCoupling logKappa))
        (V.conj auxiliaryTorsionBoundary) source = Real.exp logKappa * source := by
  rw [schurComplement_coordinate_covariance]
  change U (auxiliaryTorsionSchurComplement logKappa (U.symm source)) = _
  rw [auxiliaryTorsionSchurComplement_apply]
  simpa only [smul_eq_mul, U.apply_symm_apply] using
    U.map_smul (Real.exp logKappa) (U.symm source)

end GaloisForLFunctions.HTGeometry
