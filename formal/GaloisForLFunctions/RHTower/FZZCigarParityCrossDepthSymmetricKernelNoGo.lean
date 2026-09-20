import GaloisForLFunctions.RHTower.FZZCigarNeutralRadialCrossDepthCoherence

/-!
# FZZ-P symmetric real cross-depth kernel no-go

The literal neutral cross-depth covariance is complex, but a real depth kernel can preserve its
orientation only by breaking exchange symmetry.  This file classifies the complete finite real
symmetric-kernel class: its contribution is fixed by complex conjugation and has zero imaginary
part.  It then constructs the sharp algebraic survivor, the two-depth exchange difference, whose
imaginary part is nonzero at every literal off-node phase.

This kills the FZZ-P subroute

`literal cross-depth covariance → finite real exchange-symmetric source kernel → oriented Ward
term`.

The remaining physical premise is now precise: the literal worldsheet source must derive a
nonzero exchange-antisymmetric ordered depth kernel (or a genuinely complex kernel).  This file
does not assert that the physical source does so.
-/

open Complex
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- A finite real depth-kernel accumulation of literal cross-depth covariance. -/
def fzzRadialCouplingFiniteRealKernel
    (S : Finset ℝ) (K : ℝ → ℝ → ℝ) (v p : ℝ) : ℂ :=
  ∑ u₁ ∈ S, ∑ u₂ ∈ S,
    (K u₁ u₂ : ℂ) * fzzRadialCouplingCrossDepthCoherence u₁ u₂ v p

/-- Exchanging depth arguments conjugates the literal neutral covariance. -/
theorem star_fzzRadialCouplingCrossDepthCoherence
    (u₁ u₂ v p : ℝ) :
    star (fzzRadialCouplingCrossDepthCoherence u₁ u₂ v p) =
      fzzRadialCouplingCrossDepthCoherence u₂ u₁ v p := by
  unfold fzzRadialCouplingCrossDepthCoherence
  change (starRingEnd ℂ)
    (fzzRadialCouplingCharacteristic u₁ v p *
      (starRingEnd ℂ) (fzzRadialCouplingCharacteristic u₂ v p)) = _
  rw [map_mul]
  simp only [starRingEnd_apply, star_star]
  ring

/-- A finite real exchange-symmetric kernel fixes its accumulation under conjugation. -/
theorem star_fzzRadialCouplingFiniteRealKernel
    (S : Finset ℝ) (K : ℝ → ℝ → ℝ) (v p : ℝ)
    (hK : ∀ u₁ u₂, K u₁ u₂ = K u₂ u₁) :
    star (fzzRadialCouplingFiniteRealKernel S K v p) =
      fzzRadialCouplingFiniteRealKernel S K v p := by
  unfold fzzRadialCouplingFiniteRealKernel
  change (starRingEnd ℂ) (∑ u₁ ∈ S, ∑ u₂ ∈ S,
    (K u₁ u₂ : ℂ) * fzzRadialCouplingCrossDepthCoherence u₁ u₂ v p) = _
  have hreal (a : ℝ) : star (a : ℂ) = (a : ℂ) := by
    rw [← starRingEnd_apply, Complex.conj_ofReal]
  simp only [map_sum, map_mul, starRingEnd_apply,
    star_fzzRadialCouplingCrossDepthCoherence]
  simp only [hreal]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u₁ hu₁
  apply Finset.sum_congr rfl
  intro u₂ hu₂
  rw [hK]

/-- **FZZ-P symmetric-kernel no-go.** A finite real exchange-symmetric source kernel cannot
retain imaginary Ward orientation from the literal covariance. -/
theorem fzzRadialCouplingFiniteRealKernel_im
    (S : Finset ℝ) (K : ℝ → ℝ → ℝ) (v p : ℝ)
    (hK : ∀ u₁ u₂, K u₁ u₂ = K u₂ u₁) :
    (fzzRadialCouplingFiniteRealKernel S K v p).im = 0 := by
  have h := congrArg Complex.im
    (star_fzzRadialCouplingFiniteRealKernel S K v p hK)
  change -(fzzRadialCouplingFiniteRealKernel S K v p).im =
    (fzzRadialCouplingFiniteRealKernel S K v p).im at h
  linarith

/-- The minimal ordered survivor: subtract the exchanged literal covariance. -/
def fzzRadialCouplingCrossDepthExchangeOrientation
    (u₁ u₂ v p : ℝ) : ℂ :=
  fzzRadialCouplingCrossDepthCoherence u₁ u₂ v p -
    fzzRadialCouplingCrossDepthCoherence u₂ u₁ v p

/-- The exchange survivor isolates twice the imaginary part of literal cross-depth coherence. -/
theorem fzzRadialCouplingCrossDepthExchangeOrientation_im
    (u₁ u₂ v p : ℝ) :
    (fzzRadialCouplingCrossDepthExchangeOrientation u₁ u₂ v p).im =
      2 * (fzzRadialCouplingCrossDepthCoherence u₁ u₂ v p).im := by
  unfold fzzRadialCouplingCrossDepthExchangeOrientation
  have hstar : fzzRadialCouplingCrossDepthCoherence u₂ u₁ v p =
      star (fzzRadialCouplingCrossDepthCoherence u₁ u₂ v p) := by
    symm
    exact star_fzzRadialCouplingCrossDepthCoherence u₁ u₂ v p
  rw [hstar]
  change (fzzRadialCouplingCrossDepthCoherence u₁ u₂ v p).im -
      -(fzzRadialCouplingCrossDepthCoherence u₁ u₂ v p).im =
    2 * (fzzRadialCouplingCrossDepthCoherence u₁ u₂ v p).im
  ring

/-- The minimal exchange-antisymmetric survivor is oriented at every literal off-node phase. -/
theorem fzzRadialCouplingCrossDepthExchangeOrientation_im_ne_zero
    {u₁ u₂ v p : ℝ}
    (hphase : Real.sin (p * (u₁ - u₂) / Real.exp v) ≠ 0) :
    (fzzRadialCouplingCrossDepthExchangeOrientation u₁ u₂ v p).im ≠ 0 := by
  rw [fzzRadialCouplingCrossDepthExchangeOrientation_im]
  exact mul_ne_zero (by norm_num)
    (fzzRadialCouplingCrossDepthCoherence_im_ne_zero hphase)

end

end GaloisForLFunctions.RHTower
