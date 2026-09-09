import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-!
# Constructed conservative–dissipative Hilbert operators

The operator factorization from Schaffer–Exl, arXiv:2609.04530,
Propositions 2–3 and §4.4, is realized as `J = A - A†`, `R = B†B`.
All sign and adjoint identities follow from the construction. Rectangular
observation maps and infinite-dimensional Hilbert spaces are allowed.
-/

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry.SchafferExl

noncomputable section

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Conservative operator constructed from an arbitrary bounded operator. -/
def conservative (A : E →L[𝕜] E) : E →L[𝕜] E := A - A.adjoint

/-- Dissipative operator constructed from a rectangular observation map. -/
def damping (B : E →L[𝕜] F) : E →L[𝕜] E := B.adjoint ∘L B

/-- The conservative–dissipative generator `(A - A†) - B†B`. -/
def generator (A : E →L[𝕜] E) (B : E →L[𝕜] F) : E →L[𝕜] E :=
  conservative A - damping B

theorem adjoint_conservative (A : E →L[𝕜] E) :
    (conservative A).adjoint = -conservative A := by
  simp [conservative, map_sub, neg_sub]

theorem adjoint_damping (B : E →L[𝕜] F) :
    (damping B).adjoint = damping B := by
  simp [damping, ContinuousLinearMap.adjoint_comp]

/-- Conservative motion contributes no real power. -/
theorem conservative_power (A : E →L[𝕜] E) (x : E) :
    RCLike.re ⟪x, conservative A x⟫_𝕜 = 0 := by
  simp only [conservative, sub_apply, inner_sub_right,
    ContinuousLinearMap.adjoint_inner_right, map_sub]
  rw [inner_re_symm x (A x), sub_self]

/-- Damping power is exactly observation energy. -/
theorem damping_power (B : E →L[𝕜] F) (x : E) :
    RCLike.re ⟪x, damping B x⟫_𝕜 = ‖B x‖ ^ 2 := by
  simp [damping, ContinuousLinearMap.adjoint_inner_right]

/-- Proposition 2's algebraic identity, valid on arbitrary Hilbert spaces. -/
theorem generator_power (A : E →L[𝕜] E) (B : E →L[𝕜] F) (x : E) :
    RCLike.re ⟪x, generator A B x⟫_𝕜 = -‖B x‖ ^ 2 := by
  simp [generator, inner_sub_right, conservative_power, damping_power]

theorem generator_power_nonpos (A : E →L[𝕜] E) (B : E →L[𝕜] F) (x : E) :
    RCLike.re ⟪x, generator A B x⟫_𝕜 ≤ 0 := by
  rw [generator_power]
  exact neg_nonpos.mpr (sq_nonneg _)

/-- Vanishing loss detects the observation kernel, not stationarity. -/
theorem generator_power_eq_zero_iff (A : E →L[𝕜] E) (B : E →L[𝕜] F) (x : E) :
    RCLike.re ⟪x, generator A B x⟫_𝕜 = 0 ↔ B x = 0 := by
  rw [generator_power, neg_eq_zero, sq_eq_zero_iff, norm_eq_zero]

/-- Exact equilibrium classification: the dissipative and conservative kernels intersect. -/
theorem generator_eq_zero_iff (A : E →L[𝕜] E) (B : E →L[𝕜] F) (x : E) :
    generator A B x = 0 ↔ B x = 0 ∧ conservative A x = 0 := by
  constructor
  · intro h
    have hB : B x = 0 := (generator_power_eq_zero_iff A B x).mp (by rw [h]; simp)
    refine ⟨hB, ?_⟩
    simpa [generator, damping, hB] using h
  · rintro ⟨hB, hA⟩
    simp [generator, damping, hB, hA]

/-- Adding unit damping removes every spurious stationary force. -/
def regularized (A : E →L[𝕜] E) (B : E →L[𝕜] F) : E →L[𝕜] E :=
  generator A B - ContinuousLinearMap.id 𝕜 E

theorem regularized_power (A : E →L[𝕜] E) (B : E →L[𝕜] F) (x : E) :
    RCLike.re ⟪x, regularized A B x⟫_𝕜 = -‖B x‖ ^ 2 - ‖x‖ ^ 2 := by
  simp [regularized, inner_sub_right, generator_power]

theorem regularized_eq_zero_iff (A : E →L[𝕜] E) (B : E →L[𝕜] F) (x : E) :
    regularized A B x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have he := regularized_power A B x
    rw [h, inner_zero_right, map_zero] at he
    have hx : ‖x‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖B x‖, sq_nonneg ‖x‖]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)
  · rintro rfl
    exact map_zero _

/-- The regularized generator is injective in infinite dimension as well. -/
theorem regularized_injective (A : E →L[𝕜] E) (B : E →L[𝕜] F) :
    Function.Injective (regularized A B) := by
  intro x y h
  apply sub_eq_zero.mp
  apply (regularized_eq_zero_iff A B (x - y)).mp
  rw [map_sub, h, sub_self]

end
end GaloisForLFunctions.HTGeometry.SchafferExl
