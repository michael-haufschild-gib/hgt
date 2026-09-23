import GaloisForLFunctions.HTGeometry.ConservativeDissipativeOperator
import GaloisForLFunctions.HTGeometry.RankTwoFisherCutoffWard

set_option autoImplicit false

/-!
# Conservative–dissipative fisher laws

Applications of Schaffer–Exl, arXiv:2609.04530, to constructed operators
and the existing mathematical objects used below.
-/

open scoped InnerProductSpace
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The corpus Fisher connection produces a positive square damping operator. -/
theorem damping_pointedFisherConnection (psi chi : E) :
    damping (pointedFisherConnection psi chi) =
      pointedFisherConnection psi chi ∘L pointedFisherConnection psi chi := by
  rw [damping, pointedFisherConnection_selfAdjoint]

/-- Fisher damping resolves a precise coherent combination of source and tangent overlaps. -/
theorem fisher_generator_power (A : E →L[ℂ] E) (psi chi x : E) :
    RCLike.re ⟪x, generator A (pointedFisherConnection psi chi) x⟫_ℂ =
      -(1 / 2 : ℝ) * ‖⟪psi, x⟫_ℂ • chi + ⟪chi, x⟫_ℂ • psi‖ ^ (2 : ℕ) := by
  rw [generator_power, pointedFisherConnection]
  simp only [smul_apply, add_apply, InnerProductSpace.rankOne_apply]
  rw [norm_smul, mul_pow, invSqrtTwo_norm_sq]
  ring

/-- The exact dark sector includes coherent cancellation, not only separate orthogonality. -/
theorem fisher_generator_lossless_iff (A : E →L[ℂ] E) (psi chi x : E) :
    RCLike.re ⟪x, generator A (pointedFisherConnection psi chi) x⟫_ℂ = 0 ↔
      ⟪psi, x⟫_ℂ • chi + ⟪chi, x⟫_ℂ • psi = 0 := by
  rw [fisher_generator_power, mul_eq_zero]
  have h : -(1 / 2 : ℝ) ≠ 0 := by norm_num
  simp only [h, false_or, sq_eq_zero_iff, norm_eq_zero]

/-- Reversing the source tangent leaves damping unchanged. -/
theorem fisher_damping_tangent_reversal (psi chi : E) :
    damping (pointedFisherConnection psi (-chi)) = damping (pointedFisherConnection psi chi) := by
  have hf : pointedFisherConnection psi (-chi) = -pointedFisherConnection psi chi := by
    ext x
    simp [pointedFisherConnection, InnerProductSpace.rankOne_apply, smul_add, add_comm]
  rw [hf]
  simp [damping]

/-- Its energy loss is independent of the sign chosen for the tangent. -/
theorem fisher_power_tangent_reversal (A : E →L[ℂ] E) (psi chi x : E) :
    RCLike.re ⟪x, generator A (pointedFisherConnection psi (-chi)) x⟫_ℂ =
      RCLike.re ⟪x, generator A (pointedFisherConnection psi chi) x⟫_ℂ := by
  simp only [generator, fisher_damping_tangent_reversal]

end
end GaloisForLFunctions.HTGeometry.SchafferExl
