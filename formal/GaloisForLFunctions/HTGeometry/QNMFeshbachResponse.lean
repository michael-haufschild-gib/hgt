import GaloisForLFunctions.HTGeometry.QNMLorentzAuxiliary

/-!
# Feshbach source and observer transport for QNM pencils

Morikawa, *Two Languages for the Same Resonance*, arXiv:2608.29806,
sections 5.3 and 10, separates effective-operator poles from the response selected
by a source and an observer. The identities below apply this distinction to the
corpus Schur block operator and the quadratic pencils of arXiv:2608.19774.

An arbitrary candidate exterior inverse is permitted: its exact inverse defect
is retained in the second block. No invertibility or solved-equation assumption
is required. In the Maxwell--Lorentz application of arXiv:2607.25133, this defect
records the material-pole compatibility condition that division would discard.
-/

namespace GaloisForLFunctions.HTGeometry
variable {R F H : Type*} [CommRing R] [AddCommGroup F] [Module R F]
  [AddCommGroup H] [Module R H]

/-- Reconstruct the exterior component from its source and a candidate inverse. -/
def qnmFeshbachLift (C : F →ₗ[R] H) (G : H →ₗ[R] H) (x : F) (g : H) : F × H :=
  (x, G (g - C x))

/-- Exact reduced-source residual together with the exterior inverse defect. -/
theorem qnmFeshbach_residual (A : F →ₗ[R] F) (B : H →ₗ[R] F)
    (C : F →ₗ[R] H) (D G : H →ₗ[R] H) (x f : F) (g : H) :
    schurBlockOperator A B C D (qnmFeshbachLift C G x g) - (f, g) =
      (schurComplement A B C G x - (f - B (G g)),
        (D.comp G - (LinearMap.id : H →ₗ[R] H)) (g - C x)) := by
  apply Prod.ext <;> simp [qnmFeshbachLift, schurComplement, map_sub] <;> abel

/-- Eliminating a channel dresses the observer and retains its direct background response. -/
theorem qnmFeshbach_observed (C : F →ₗ[R] H) (G : H →ₗ[R] H)
    (O : F →ₗ[R] R) (P : H →ₗ[R] R) (x : F) (g : H) :
    O (qnmFeshbachLift C G x g).1 + P (qnmFeshbachLift C G x g).2 =
      (O - P ∘ₗ G ∘ₗ C) x + P (G g) := by
  simp [qnmFeshbachLift, map_sub]
  ring

/-- The reduced equation is sufficient exactly when the retained inverse defect vanishes. -/
theorem qnmFeshbach_equation_iff (A : F →ₗ[R] F) (B : H →ₗ[R] F)
    (C : F →ₗ[R] H) (D G : H →ₗ[R] H) (x f : F) (g : H) :
    schurBlockOperator A B C D (qnmFeshbachLift C G x g) = (f, g) ↔
      schurComplement A B C G x = f - B (G g) ∧
        (D.comp G - (LinearMap.id : H →ₗ[R] H)) (g - C x) = 0 := by
  rw [← sub_eq_zero, qnmFeshbach_residual]
  simp only [Prod.mk_eq_zero, sub_eq_zero]

/-- Inhomogeneous companion reduction transports both components of the forcing. -/
theorem qnmCompanion_forced_residual (A B W : F →ₗ[R] F) (z : R)
    (x f g : F) :
    qnmCompanionLeft A B (x, z • x + f) -
        z • qnmCompanionMass W (x, z • x + f) - (f, g) =
      (0, qnmQuadraticPencil A B W z x - (g - (B - z • W) f)) := by
  apply Prod.ext
  · simp [qnmCompanionLeft, qnmCompanionMass]
  · simp [qnmCompanionLeft, qnmCompanionMass, qnmQuadraticPencil,
      map_add, smul_add, smul_smul, pow_two]
    module

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- Polarization elimination is exact off material poles; at a pole it retains `g • f = 0`. -/
theorem qnmLorentz_eliminated_residual (L1 L2 W : E →ₗ[ℂ] E)
    (g w d mu z : ℂ) (f : E) :
    qnmQuadraticPencil (qnmLorentzStiffness L1 g w)
      (qnmLorentzDamping L2 d) (qnmLorentzMass W mu) z
      (f, (z ^ (2 : ℕ) + d * z + w ^ (2 : ℕ))⁻¹ • (g • f)) =
      (qnmQuadraticPencil L1 L2 W z f -
          (z ^ (2 : ℕ) * mu * (z ^ (2 : ℕ) + d * z + w ^ (2 : ℕ))⁻¹ * g) • f,
        if z ^ (2 : ℕ) + d * z + w ^ (2 : ℕ) = 0 then g • f else 0) := by
  rw [qnmLorentzQuadratic_residual]
  apply Prod.ext
  · simp [qnmQuadraticPencil, smul_add, smul_smul]
    module
  · by_cases h : z ^ (2 : ℕ) + d * z + w ^ (2 : ℕ) = 0
    · simp [h]
    · simp [h, smul_smul]

end GaloisForLFunctions.HTGeometry
