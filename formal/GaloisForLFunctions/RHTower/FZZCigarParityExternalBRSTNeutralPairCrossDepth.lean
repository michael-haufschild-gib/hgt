import GaloisForLFunctions.RHTower.FZZCigarParityExternalBRSTSingleBranchAngularNoGo
import GaloisForLFunctions.RHTower.FZZCigarNeutralRadialCrossDepthCoherence

/-!
# FZZ-P neutral external-BRST pair preserves cross-depth orientation

An isolated charged external-BRST branch is killed by compact-circle orthogonality.  The literal
charge-neutral `W⁺W⁻` branch pair is different: its opposite holonomy characters multiply to one
pointwise.  Therefore the compact angular integral of this bare pair preserves the literal
cross-depth radial covariance exactly, including its nonzero imaginary part away from phase
nodes.

This discharges the narrow FZZ-P premise

`charge-neutral external-BRST compact branch pair → compact integration retains cross-depth
orientation`.

It does not derive the full physical source.  In particular, fractional screening, both
counterterms, external OPE coefficients, normalization, and the source-fixed coupling to the
mixed replica--momentum Ward identity remain open.
-/

open MeasureTheory

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Compact angular factor of the literal neutral external `W⁺W⁻` branch pair. -/
def fzzCigarExternalBRSTNeutralAngularPairKernel
    (k : ℝ) (j : ℂ) (p ν : ℤ) (s : ℝ) : ℂ :=
  fzzCigarExternalBRSTPlusAngularBranchKernel k j p ν s *
    fzzCigarExternalBRSTMinusAngularBranchKernel k j p ν s

/-- Opposite external branch charges neutralize their compact holonomy pointwise. -/
theorem fzzCigarExternalBRSTNeutralAngularPairKernel_eq_one
    (k : ℝ) (j : ℂ) (p ν : ℤ) (s : ℝ) :
    fzzCigarExternalBRSTNeutralAngularPairKernel k j p ν s = 1 := by
  unfold fzzCigarExternalBRSTNeutralAngularPairKernel
    fzzCigarExternalBRSTPlusAngularBranchKernel
    fzzCigarExternalBRSTMinusAngularBranchKernel
  rw [RHTower.fzzTorusHolonomyCharacter_mul]
  simp

/-- Compact integration of the neutral external pair against literal cross-depth covariance. -/
def fzzCigarExternalBRSTNeutralCrossDepthCompactIntegral
    (k : ℝ) (j : ℂ) (p ν : ℤ) (u₁ u₂ v : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..1,
    fzzCigarExternalBRSTNeutralAngularPairKernel k j p ν s *
      fzzRadialCouplingCrossDepthCoherence u₁ u₂ v (p : ℝ)

/-- The neutral external pair preserves the literal cross-depth carrier through compact
integration exactly. -/
theorem fzzCigarExternalBRSTNeutralCrossDepthCompactIntegral_eq
    (k : ℝ) (j : ℂ) (p ν : ℤ) (u₁ u₂ v : ℝ) :
    fzzCigarExternalBRSTNeutralCrossDepthCompactIntegral k j p ν u₁ u₂ v =
      fzzRadialCouplingCrossDepthCoherence u₁ u₂ v (p : ℝ) := by
  unfold fzzCigarExternalBRSTNeutralCrossDepthCompactIntegral
  calc
    (∫ s in (0 : ℝ)..1,
      fzzCigarExternalBRSTNeutralAngularPairKernel k j p ν s *
        fzzRadialCouplingCrossDepthCoherence u₁ u₂ v (p : ℝ)) =
        ∫ _s in (0 : ℝ)..1,
          fzzRadialCouplingCrossDepthCoherence u₁ u₂ v (p : ℝ) := by
            apply intervalIntegral.integral_congr
            intro s _
            change fzzCigarExternalBRSTNeutralAngularPairKernel k j p ν s *
              fzzRadialCouplingCrossDepthCoherence u₁ u₂ v (p : ℝ) =
                fzzRadialCouplingCrossDepthCoherence u₁ u₂ v (p : ℝ)
            rw [fzzCigarExternalBRSTNeutralAngularPairKernel_eq_one]
            ring
    _ = _ := by simp

/-- The compactly integrated neutral external pair retains nonzero orientation at every literal
off-node phase. -/
theorem fzzCigarExternalBRSTNeutralCrossDepthCompactIntegral_im_ne_zero
    {k : ℝ} {j : ℂ} {p ν : ℤ} {u₁ u₂ v : ℝ}
    (hphase : Real.sin ((p : ℝ) * (u₁ - u₂) / Real.exp v) ≠ 0) :
    (fzzCigarExternalBRSTNeutralCrossDepthCompactIntegral k j p ν u₁ u₂ v).im ≠ 0 := by
  rw [fzzCigarExternalBRSTNeutralCrossDepthCompactIntegral_eq]
  exact fzzRadialCouplingCrossDepthCoherence_im_ne_zero hphase

end

end GaloisForLFunctions.RHTower
