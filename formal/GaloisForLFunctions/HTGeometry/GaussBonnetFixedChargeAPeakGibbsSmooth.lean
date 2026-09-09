import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAAlignedAngularJets
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Smoothness of the actual aligned Gibbs potential at every state

The exact force equals the quartic-profile derivative plus phase
asymmetry times the proved smooth angular correction. The physical
Gibbs derivative identity then gives smoothness of the actual energy.
-/
noncomputable section
open Real Filter Set
open scoped Topology ContDiff
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAPeakNormalizedGibbsForce_decomposition (w φ τ l ψ : ℝ) :
    egbFixedChargeAPeakNormalizedGibbsForce w φ τ l ψ = -4 * sin ψ * cos ψ ^ 3 +
      egbCoexistenceASymmetricRatio τ * egbFixedChargeAAlignedAngularCorrection w φ (egbFixedChargeAAlignedForceState w φ τ l) ψ := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have h := egbFixedChargeAPeakNormalizedGibbsForce_correction_formula w φ τ l ψ
  change (egbFixedChargeAPeakNormalizedGibbsForce w φ τ l ψ + 4 * sin ψ * cos ψ ^ 3) / egbCoexistenceASymmetricRatio τ =
    egbFixedChargeAAlignedAngularCorrection w φ (egbFixedChargeAAlignedForceState w φ τ l) ψ at h
  have he := (div_eq_iff hd.ne').mp h
  nlinarith

theorem egbFixedChargeAPeakNormalizedGibbsForce_contDiff (w φ τ l : ℝ) :
    ContDiff ℝ ∞ (egbFixedChargeAPeakNormalizedGibbsForce w φ τ l) := by
  have hf : egbFixedChargeAPeakNormalizedGibbsForce w φ τ l = fun ψ => -4 * sin ψ * cos ψ ^ 3 +
      egbCoexistenceASymmetricRatio τ * egbFixedChargeAAlignedAngularCorrection w φ (egbFixedChargeAAlignedForceState w φ τ l) ψ :=
    funext (egbFixedChargeAPeakNormalizedGibbsForce_decomposition w φ τ l)
  rw [hf]
  have hc := egbFixedChargeAAlignedAngularCorrection_actual_contDiff w φ τ l
  fun_prop

theorem egbFixedChargeAPeakNormalizedGibbs_contDiff (w φ τ l₁ l₂ : ℝ) :
    ContDiff ℝ ∞ (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) := by
  apply contDiff_infty_iff_deriv.mpr
  constructor
  · intro ψ
    exact (egbFixedChargeAPeakNormalizedGibbs_hasDerivAt w φ τ l₁ l₂ ψ).differentiableAt
  · have hf : deriv (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) = egbFixedChargeAPeakNormalizedGibbsForce w φ τ l₂ :=
      funext (egbFixedChargeAPeakNormalizedGibbs_derivative w φ τ l₁ l₂)
    rw [hf]
    exact egbFixedChargeAPeakNormalizedGibbsForce_contDiff w φ τ l₂

theorem egbFixedChargeAQuarticProfile_hasDerivAt (ψ : ℝ) :
    HasDerivAt (fun x : ℝ => cos x ^ 4) (-4 * sin ψ * cos ψ ^ 3) ψ := by
  have h := (hasDerivAt_cos ψ).pow 4
  apply h.congr_deriv
  norm_num only [Nat.reduceSub, Nat.cast_ofNat, Pi.pow_apply]
  ring

end GaloisForLFunctions.HTGeometry
