import GaloisForLFunctions.RHTower.SoninCalkinNormBound

/-!
# Positive form action and compact resolvent

For a nonnegative self-adjoint generator `L`, put `S = (I + L)⁻¹ᐟ²`.  The closed form-action
sublevel of radius `R` is the closed image under `S` of the Hilbert ball of radius `sqrt R`, while
the resolvent is `S†S = (I + L)⁻¹`.  This bounded-transform presentation avoids any choice of an
unbounded-operator domain and states the paper theorem at its exact functional-analytic interface.

The capstone below is unconditional: for every bounded transform on every complex Hilbert space,
all form-action sublevels are compact exactly when its adjoint-square resolvent is compact.
-/

namespace GaloisForLFunctions.HTGeometry

open Set
open scoped NNReal InnerProduct

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Closed `R`-sublevel of the form action, in bounded-transform coordinates.  For
`S = (I + L)⁻¹ᐟ²`, this is precisely `{ξ | ‖ξ‖² + ‖L¹ᐟ²ξ‖² ≤ R}`. -/
def positiveFormActionSublevel (inverseSqrt : H →L[ℂ] H) (R : ℝ≥0) : Set H :=
  closure (inverseSqrt '' Metric.closedBall 0 (Real.sqrt (R : ℝ)))

/-- Resolvent represented by the inverse square-root transform. -/
def positiveFormResolvent (inverseSqrt : H →L[ℂ] H) : H →L[ℂ] H :=
  (inverseSqrt†) * inverseSqrt

/-- Compactness of every closed positive-form action sublevel is equivalent to compactness of the
resolvent.  No spectral, injectivity, or finite-dimensional hypothesis is imposed. -/
theorem positiveFormActionSublevel_compact_iff_compactResolvent
    (inverseSqrt : H →L[ℂ] H) :
    (∀ R : ℝ≥0, IsCompact (positiveFormActionSublevel inverseSqrt R)) ↔
      IsCompactOperator (positiveFormResolvent inverseSqrt) := by
  constructor
  · intro hall
    have hone := hall (1 : ℝ≥0)
    have hS : IsCompactOperator inverseSqrt := by
      change IsCompactOperator ⇑inverseSqrt.toLinearMap
      rw [isCompactOperator_iff_isCompact_closure_image_closedBall
        inverseSqrt.toLinearMap (by norm_num : (0 : ℝ) < 1)]
      simpa [positiveFormActionSublevel] using hone
    exact hS.clm_comp (inverseSqrt†)
  · intro hres R
    have hsq : RHTower.CompactOperatorEq ((inverseSqrt†) * inverseSqrt) 0 := by
      rw [RHTower.CompactOperatorEq, sub_zero]
      exact hres
    have hS : IsCompactOperator inverseSqrt :=
      RHTower.isCompactOperator_of_adjoint_mul_compactEq_zero inverseSqrt hsq
    exact hS.isCompact_closure_image_closedBall _

end

end GaloisForLFunctions.HTGeometry
