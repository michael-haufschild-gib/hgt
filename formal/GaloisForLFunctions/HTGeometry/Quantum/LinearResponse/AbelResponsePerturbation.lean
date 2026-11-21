import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelForwardFibers

/-!
# Perturbing the Abel response

The second resolvent identity expresses the change in a reading as
a response to the commutator with the Hamiltonian perturbation.
A second application gives an exact remainder in the linearization.
-/

open Matrix Set
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H K : Matrix ι ι ℂ}

/-- At positive width the response is a complex linear equivalence. -/
def abelResponseLinearEquiv (hH : H.IsHermitian) (ε : Ioi (0 : ℝ)) :
    Matrix ι ι ℂ ≃ₗ[ℂ] Matrix ι ι ℂ :=
  (show Matrix ι ι ℂ ≃ₗ[ℂ] Matrix ι ι ℂ from {
    toFun := hamiltonianAbelInverse H ε
    invFun := hamiltonianDampedGapResponse hH 0 ε
    left_inv := hamiltonianAbelInverse_rightInverse hH ε
    right_inv := hamiltonianAbelInverse_leftInverse hH ε
    map_add' := by
      intro X Y
      simp only [hamiltonianAbelInverse_eq_sub, Matrix.mul_add, Matrix.add_mul, smul_sub, smul_add]
      abel
    map_smul' := by
      intro c X
      simp only [hamiltonianAbelInverse_eq_sub, RingHom.id_apply, Matrix.mul_smul,
        Matrix.smul_mul, ← smul_sub c]
      rw [smul_comm (hamiltonianAbelShift ε)⁻¹ c, smul_sub c] }).symm

/-- The commutator forcing of a Hamiltonian perturbation on the original reading. -/
def abelPerturbationForcing (hH : H.IsHermitian) (ε : Ioi (0 : ℝ))
    (T X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  let Y := hamiltonianDampedGapResponse hH 0 ε X
  (hamiltonianAbelShift ε)⁻¹ • (T * Y - Y * T)

/-- The second resolvent identity at arbitrary Hermitian endpoints. -/
theorem abelResponse_sub (hH : H.IsHermitian) (hK : K.IsHermitian)
    (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) :
    hamiltonianDampedGapResponse hK 0 ε X - hamiltonianDampedGapResponse hH 0 ε X =
      hamiltonianDampedGapResponse hK 0 ε (abelPerturbationForcing hH ε (K - H) X) := by
  let Y := hamiltonianDampedGapResponse hH 0 ε X
  let F := abelPerturbationForcing hH ε (K - H) X
  have hsub (A B : Matrix ι ι ℂ) :
      hamiltonianAbelInverse K ε (A - B) =
        hamiltonianAbelInverse K ε A - hamiltonianAbelInverse K ε B :=
    (abelResponseLinearEquiv hK ε).symm.map_sub A B
  apply (hamiltonianAbelInverse_rightInverse hK ε).injective
  rw [hsub, hamiltonianAbelInverse_leftInverse hK ε X,
    hamiltonianAbelInverse_leftInverse hK ε F]
  have hY : hamiltonianAbelInverse H ε Y = X := hamiltonianAbelInverse_leftInverse hH ε X
  change X - hamiltonianAbelInverse K ε Y = F
  rw [← hY, hamiltonianAbelInverse_eq_sub, hamiltonianAbelInverse_eq_sub]
  dsimp only [F, abelPerturbationForcing]
  simp only [Matrix.sub_mul, Matrix.mul_sub, smul_sub]
  abel

/-- The linear response to the perturbation, evaluated at the original Hamiltonian. -/
def abelResponseVariation (hH : H.IsHermitian) (ε : Ioi (0 : ℝ))
    (T X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  hamiltonianDampedGapResponse hH 0 ε (abelPerturbationForcing hH ε T X)

/-- First variation is linear in the Hamiltonian direction. -/
def abelResponseVariationLinear (hH : H.IsHermitian) (ε : Ioi (0 : ℝ))
    (X : Matrix ι ι ℂ) : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ :=
  (abelResponseLinearEquiv hH ε).toLinearMap.comp
    (show Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ from {
      toFun := fun T => abelPerturbationForcing hH ε T X
      map_add' := by
        intro A B
        dsimp only [abelPerturbationForcing]
        rw [Matrix.add_mul, Matrix.mul_add, add_sub_add_comm, smul_add]
      map_smul' := by
        intro c T
        dsimp only [abelPerturbationForcing, RingHom.id_apply]
        rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub c, smul_comm (hamiltonianAbelShift ε)⁻¹ c] })

theorem abelResponseVariationLinear_apply (hH : H.IsHermitian) (ε : Ioi (0 : ℝ))
    (T X : Matrix ι ι ℂ) :
    abelResponseVariationLinear hH ε X T = abelResponseVariation hH ε T X := rfl

/-- The remainder has two commutator factors in the perturbation, with
the final response evaluated at the perturbed Hamiltonian. -/
theorem abelResponse_sub_variation (hH : H.IsHermitian) (hK : K.IsHermitian)
    (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) :
    hamiltonianDampedGapResponse hK 0 ε X - hamiltonianDampedGapResponse hH 0 ε X -
        abelResponseVariation hH ε (K - H) X =
      hamiltonianDampedGapResponse hK 0 ε
        (abelPerturbationForcing hH ε (K - H) (abelPerturbationForcing hH ε (K - H) X)) := by
  rw [abelResponse_sub hH hK ε X, abelResponseVariation]
  exact abelResponse_sub hH hK ε _

/-- Directions invisible to the first variation are precisely those
that commute with the original reading. -/
theorem abelResponseVariation_eq_zero_iff_commute (hH : H.IsHermitian)
    (ε : Ioi (0 : ℝ)) (T X : Matrix ι ι ℂ) :
    abelResponseVariation hH ε T X = 0 ↔
      Commute T (hamiltonianDampedGapResponse hH 0 ε X) := by
  rw [abelResponseVariation, dampedGapResponse_zero_eq_iff_abelInverse_eq,
    hamiltonianAbelInverse_eq_sub, Matrix.mul_zero, Matrix.zero_mul, sub_self, smul_zero,
    sub_self, abelPerturbationForcing]
  change _ ↔ T * hamiltonianDampedGapResponse hH 0 ε X =
    hamiltonianDampedGapResponse hH 0 ε X * T
  exact eq_comm.trans (smul_eq_zero.trans
    ((or_iff_right (inv_ne_zero (hamiltonianAbelShift_ne_zero ε))).trans sub_eq_zero))

/-- Vanishing of the first variation detects exact equality of readings
at arbitrary Hermitian endpoints. -/
theorem abelResponseVariation_sub_eq_zero_iff (hH : H.IsHermitian) (hK : K.IsHermitian)
    (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) :
    abelResponseVariation hH ε (H - K) X = 0 ↔
      hamiltonianDampedGapResponse hH 0 ε X = hamiltonianDampedGapResponse hK 0 ε X :=
  (abelResponseVariation_eq_zero_iff_commute hH ε (H - K) X).trans
    (abelForwardReading_eq_iff_commute hH hK ε X).symm

#print axioms abelResponse_sub
#print axioms abelResponse_sub_variation
#print axioms abelResponseVariation_sub_eq_zero_iff

end

end GaloisForLFunctions.HTGeometry
