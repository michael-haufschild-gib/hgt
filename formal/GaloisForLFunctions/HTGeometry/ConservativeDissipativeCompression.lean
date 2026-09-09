import GaloisForLFunctions.HTGeometry.ConservativeDissipativeOperator
import Mathlib.Analysis.InnerProductSpace.Subspace

set_option autoImplicit false

/-!
# Conservative–dissipative compression laws

Applications of Schaffer–Exl, arXiv:2609.04530, to constructed operators
and the existing mathematical objects used below.
-/

open scoped InnerProductSpace
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section
variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- Congruence transports the conservative part through any linear feature map. -/
theorem conservative_congruence (A : E →L[𝕜] E) (C : F →L[𝕜] E) :
    conservative (C.adjoint ∘L A ∘L C) = C.adjoint ∘L conservative A ∘L C := by
  simp only [conservative, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]
  ext x
  simp

/-- Observation damping is closed under feature restriction, even when the map is singular. -/
theorem damping_comp (B : E →L[𝕜] G) (C : F →L[𝕜] E) :
    damping (B ∘L C) = C.adjoint ∘L damping B ∘L C := by
  simp only [damping, ContinuousLinearMap.adjoint_comp]
  rfl

/-- Exact reduced generator obtained by congruence, with its factorization preserved. -/
theorem generator_congruence (A : E →L[𝕜] E) (B : E →L[𝕜] G) (C : F →L[𝕜] E) :
    generator (C.adjoint ∘L A ∘L C) (B ∘L C) = C.adjoint ∘L generator A B ∘L C := by
  rw [generator, conservative_congruence, damping_comp]
  ext x
  simp [generator]

/-- Compressed dynamics dissipate the energy of the original observation of the lifted force. -/
theorem compressed_power (A : E →L[𝕜] E) (B : E →L[𝕜] G) (C : F →L[𝕜] E) (x : F) :
    RCLike.re ⟪x, (C.adjoint ∘L generator A B ∘L C) x⟫_𝕜 = -‖B (C x)‖ ^ 2 := by
  rw [← generator_congruence]
  exact generator_power _ _ _

/-- No injectivity or invertibility of the encoder is required for the sign law. -/
theorem compressed_power_nonpos (A : E →L[𝕜] E) (B : E →L[𝕜] G) (C : F →L[𝕜] E) (x : F) :
    RCLike.re ⟪x, (C.adjoint ∘L generator A B ∘L C) x⟫_𝕜 ≤ 0 := by
  rw [compressed_power]
  exact neg_nonpos.mpr (sq_nonneg _)

/-- Singular feature maps expose an exact larger lossless sector. -/
theorem compressed_lossless_iff (A : E →L[𝕜] E) (B : E →L[𝕜] G) (C : F →L[𝕜] E) (x : F) :
    RCLike.re ⟪x, (C.adjoint ∘L generator A B ∘L C) x⟫_𝕜 = 0 ↔ B (C x) = 0 := by
  rw [compressed_power, neg_eq_zero, sq_eq_zero_iff, norm_eq_zero]

/-- The rank-one observer removes precisely its squared overlap with the force. -/
theorem rankOne_observer_power (A : E →L[𝕜] E) (psi x : E) :
    RCLike.re ⟪x, generator A (innerSL 𝕜 psi) x⟫_𝕜 = -‖⟪psi, x⟫_𝕜‖ ^ 2 :=
  generator_power A (innerSL 𝕜 psi) x

/-- Its lossless sector is exactly the orthogonal complement of the observed line. -/
theorem rankOne_observer_lossless_iff (A : E →L[𝕜] E) (psi x : E) :
    RCLike.re ⟪x, generator A (innerSL 𝕜 psi) x⟫_𝕜 = 0 ↔ ⟪psi, x⟫_𝕜 = 0 :=
  generator_power_eq_zero_iff A (innerSL 𝕜 psi) x

end
end GaloisForLFunctions.HTGeometry.SchafferExl
