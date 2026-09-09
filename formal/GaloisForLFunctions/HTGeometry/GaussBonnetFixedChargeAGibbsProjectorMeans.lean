import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsPeriodicMeans
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsHarmonicProjectors

/-!
# Exact mean separation of the actual Gibbs differential projectors

The nonconstant differential projectors have zero angular mean at
every actual coexistence state. The constant projector preserves the
full Gibbs mean exactly. These identities strengthen their uniform
critical limits with exact finite-state integral relations.
-/
noncomputable section
open Real Filter Set MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAGibbsPositiveLinearJet_mean_zero (w φ τ l₁ l₂ a b c : ℝ) (j k m : ℕ) :
    (∫ ψ, egbFixedChargeALinearJetObservable a b c (j + 1) (k + 1) (m + 1)
      (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ ∂QuantumAlg.unifAngle) = 0 := by
  have hj := (egbFixedChargeAGibbsAngleJet_integrable w φ τ l₁ l₂ (j + 1)).const_mul a
  have hk := (egbFixedChargeAGibbsAngleJet_integrable w φ τ l₁ l₂ (k + 1)).const_mul b
  have hm := (egbFixedChargeAGibbsAngleJet_integrable w φ τ l₁ l₂ (m + 1)).const_mul c
  have ha := integral_add (hj.add hk) hm
  simp only [Pi.add_apply] at ha
  unfold egbFixedChargeALinearJetObservable
  rw [ha, integral_add hj hk,
    integral_const_mul, integral_const_mul, integral_const_mul,
    egbFixedChargeAGibbsAngleJet_mean_zero, egbFixedChargeAGibbsAngleJet_mean_zero,
    egbFixedChargeAGibbsAngleJet_mean_zero]
  ring

theorem egbFixedChargeAGibbsLinearJet_mean_formula (w φ τ l₁ l₂ a b c : ℝ) (j k : ℕ) :
    (∫ ψ, egbFixedChargeALinearJetObservable a b c 0 (j + 1) (k + 1)
      (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ ∂QuantumAlg.unifAngle) =
      a * egbFixedChargeAGibbsAngleMean w φ τ l₁ l₂ := by
  have h₀ := (egbFixedChargeAGibbsAngleJet_integrable w φ τ l₁ l₂ 0).const_mul a
  have hj := (egbFixedChargeAGibbsAngleJet_integrable w φ τ l₁ l₂ (j + 1)).const_mul b
  have hk := (egbFixedChargeAGibbsAngleJet_integrable w φ τ l₁ l₂ (k + 1)).const_mul c
  have ha := integral_add (h₀.add hj) hk
  simp only [Pi.add_apply] at ha
  unfold egbFixedChargeALinearJetObservable
  rw [ha, integral_add h₀ hj,
    integral_const_mul, integral_const_mul, integral_const_mul,
    egbFixedChargeAGibbsAngleJet_mean_zero, egbFixedChargeAGibbsAngleJet_mean_zero]
  simp only [iteratedDeriv_zero, mul_zero, add_zero, egbFixedChargeAGibbsAngleMean]

theorem egbFixedChargeASecondHarmonicProjector_mean_zero (w φ τ l₁ l₂ : ℝ) :
    (∫ ψ, egbFixedChargeASecondHarmonicProjector
      (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ ∂QuantumAlg.unifAngle) = 0 := by
  simpa only [egbFixedChargeASecondHarmonicProjector, zero_mul] using
    egbFixedChargeAGibbsLinearJet_mean_formula w φ τ l₁ l₂ 0 (-2 / 3) (-1 / 24) 1 3

theorem egbFixedChargeAFourthHarmonicProjector_mean_zero (w φ τ l₁ l₂ : ℝ) :
    (∫ ψ, egbFixedChargeAFourthHarmonicProjector
      (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ ∂QuantumAlg.unifAngle) = 0 := by
  simpa only [egbFixedChargeAFourthHarmonicProjector, zero_mul] using
    egbFixedChargeAGibbsLinearJet_mean_formula w φ τ l₁ l₂ 0 (1 / 6) (1 / 24) 1 3

theorem egbFixedChargeAConstantHarmonicProjector_mean_identity (w φ τ l₁ l₂ : ℝ) :
    (∫ ψ, egbFixedChargeAConstantHarmonicProjector
      (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ ∂QuantumAlg.unifAngle) =
      egbFixedChargeAGibbsAngleMean w φ τ l₁ l₂ := by
  simpa only [egbFixedChargeAConstantHarmonicProjector, one_mul] using
    egbFixedChargeAGibbsLinearJet_mean_formula w φ τ l₁ l₂ 1 (5 / 16) (1 / 64) 1 3

end GaloisForLFunctions.HTGeometry
