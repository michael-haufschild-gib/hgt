import Mathlib

/-!
# Why clock-reconstructed geometry does not by itself select Einstein dynamics

Suppose a complete clock network has reconstructed a metric and its Einstein tensor.  The
contracted Bianchi identity and metric compatibility make `G + Λ g` divergence-free.  If the
matter source has not been specified independently, one may always define

`T_eff = κ⁻¹ (G + Λ g)`.

Then `T_eff` is conserved and the Einstein equation holds identically.  Conservation plus
reconstructed geometry therefore cannot select a gravitational dynamics: it admits an effective
source for every geometric left-hand side.  A physical reconstruction theorem needs independent
source interventions or an equivalent response axiom.

This file formalizes only the dependency-closed linear-algebraic consequence.  A physical
application must separately supply the geometric Bianchi and metric-compatibility identities.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K Tensor Current : Type*} [Field K]
variable [AddCommGroup Tensor] [Module K Tensor]
variable [AddCommGroup Current] [Module K Current]

/-- Effective source obtained by moving an otherwise unrestricted geometric left-hand side to the
source side of an Einstein-form equation. -/
def effectiveStressTensor
    (κ Λ : K) (einstein metric : Tensor) : Tensor :=
  κ⁻¹ • (einstein + Λ • metric)

/-- Bianchi plus metric compatibility force the effective source to be conserved. -/
theorem effectiveStressTensor_conserved
    (divergence : Tensor →ₗ[K] Current)
    (κ Λ : K) (einstein metric : Tensor)
    (heinstein : divergence einstein = 0)
    (hmetric : divergence metric = 0) :
    divergence (effectiveStressTensor κ Λ einstein metric) = 0 := by
  simp [effectiveStressTensor, heinstein, hmetric]

/-- For nonzero coupling, the Einstein-form field equation with the effective source is an exact
identity for every geometric tensor and metric. -/
theorem einsteinEquation_effectiveStressTensor
    (κ Λ : K) (einstein metric : Tensor) (hκ : κ ≠ 0) :
    einstein + Λ • metric =
      κ • effectiveStressTensor κ Λ einstein metric := by
  simp [effectiveStressTensor, hκ]

/-- **Chronometric dynamics underdetermination.**  Every divergence-free geometric left-hand side
admits a conserved effective source satisfying an Einstein-form equation.  Geometry and source
conservation alone cannot identify the dynamics when the source is not independently fixed. -/
theorem exists_conserved_effectiveStressTensor
    (divergence : Tensor →ₗ[K] Current)
    (κ Λ : K) (einstein metric : Tensor)
    (hκ : κ ≠ 0)
    (heinstein : divergence einstein = 0)
    (hmetric : divergence metric = 0) :
    ∃ stress : Tensor,
      divergence stress = 0 ∧
        einstein + Λ • metric = κ • stress := by
  refine ⟨effectiveStressTensor κ Λ einstein metric, ?_, ?_⟩
  · exact effectiveStressTensor_conserved divergence κ Λ einstein metric heinstein hmetric
  · exact einsteinEquation_effectiveStressTensor κ Λ einstein metric hκ

end

end GaloisForLFunctions.HTGeometry
