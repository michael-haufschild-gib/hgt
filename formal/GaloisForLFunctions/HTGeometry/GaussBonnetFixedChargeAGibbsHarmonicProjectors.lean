import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeALinearJetObservables

/-!
# Differential recovery of the actual Gibbs critical harmonics

Second and fourth derivatives extract the two nonconstant harmonics
of the critical Gibbs profile. A third combination extracts its
constant term. The exact critical formulas transfer to the actual
normalized Gibbs potential uniformly with vanishing first correction.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAQuarticProfile_second_harmonics (ψ : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => cos x ^ 4) ψ = -2 * cos (2 * ψ) - 2 * cos (4 * ψ) := by
  have h := egbFixedChargeAQuarticProfile_harmonic_jet 1 ψ
  rw [show 1 + 1 = 0 + 2 by omega, egbFixedChargeAQuarticMode_two_step,
    egbFixedChargeAQuarticMode_two_step] at h
  simp only [iteratedDeriv_zero] at h
  convert h using 1 <;> ring

theorem egbFixedChargeAQuarticProfile_fourth_harmonics (ψ : ℝ) :
    iteratedDeriv 4 (fun x : ℝ => cos x ^ 4) ψ = 8 * cos (2 * ψ) + 32 * cos (4 * ψ) := by
  have h := egbFixedChargeAQuarticProfile_harmonic_jet 3 ψ
  rw [show 3 + 1 = 0 + 4 by omega, egbFixedChargeAQuarticMode_four_step,
    egbFixedChargeAQuarticMode_four_step] at h
  simp only [iteratedDeriv_zero] at h
  convert h using 1 <;> ring

def egbFixedChargeASecondHarmonicProjector (f : ℝ → ℝ) (ψ : ℝ) : ℝ :=
  egbFixedChargeALinearJetObservable 0 (-2 / 3) (-1 / 24) 0 2 4 f ψ

def egbFixedChargeAFourthHarmonicProjector (f : ℝ → ℝ) (ψ : ℝ) : ℝ :=
  egbFixedChargeALinearJetObservable 0 (1 / 6) (1 / 24) 0 2 4 f ψ

def egbFixedChargeAConstantHarmonicProjector (f : ℝ → ℝ) (ψ : ℝ) : ℝ :=
  egbFixedChargeALinearJetObservable 1 (5 / 16) (1 / 64) 0 2 4 f ψ

theorem egbFixedChargeASecondHarmonicProjector_critical (ψ : ℝ) :
    egbFixedChargeASecondHarmonicProjector (fun x : ℝ => cos x ^ 4) ψ = cos (2 * ψ) := by
  unfold egbFixedChargeASecondHarmonicProjector egbFixedChargeALinearJetObservable
  rw [iteratedDeriv_zero, egbFixedChargeAQuarticProfile_second_harmonics,
    egbFixedChargeAQuarticProfile_fourth_harmonics, egbFixedChargeAQuarticProfile_harmonic_decomposition]
  ring

theorem egbFixedChargeASecondHarmonicProjector_uniform_first_zero_limit (w φ l₁ l₂ : ℝ) :
    TendstoUniformly (fun τ ψ =>
      (egbFixedChargeASecondHarmonicProjector (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ - cos (2 * ψ)) /
        egbCoexistenceASymmetricRatio τ) (fun _ => (0 : ℝ)) atBot := by
  have h := egbFixedChargeALinearJetObservable_uniform_first_zero_limit w φ l₁ l₂ 0 (-2 / 3) (-1 / 24) 0 2 4
  change TendstoUniformly (fun τ ψ =>
      (egbFixedChargeASecondHarmonicProjector (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ -
       egbFixedChargeASecondHarmonicProjector (fun x : ℝ => cos x ^ 4) ψ) / egbCoexistenceASymmetricRatio τ)
      (fun _ => (0 : ℝ)) atBot at h
  simpa only [egbFixedChargeASecondHarmonicProjector_critical] using h

theorem egbFixedChargeASecondHarmonicProjector_uniform_limit (w φ l₁ l₂ : ℝ) :
    TendstoUniformly (fun τ ψ =>
      egbFixedChargeASecondHarmonicProjector (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ)
      (fun ψ => cos (2 * ψ)) atBot := by
  have h := egbFixedChargeALinearJetObservable_uniform_limit w φ l₁ l₂ 0 (-2 / 3) (-1 / 24) 0 2 4
  change TendstoUniformly (fun τ ψ =>
      egbFixedChargeASecondHarmonicProjector (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ)
      (fun ψ => egbFixedChargeASecondHarmonicProjector (fun x : ℝ => cos x ^ 4) ψ) atBot at h
  simpa only [egbFixedChargeASecondHarmonicProjector_critical] using h

theorem egbFixedChargeAFourthHarmonicProjector_critical (ψ : ℝ) :
    egbFixedChargeAFourthHarmonicProjector (fun x : ℝ => cos x ^ 4) ψ = cos (4 * ψ) := by
  unfold egbFixedChargeAFourthHarmonicProjector egbFixedChargeALinearJetObservable
  rw [iteratedDeriv_zero, egbFixedChargeAQuarticProfile_second_harmonics,
    egbFixedChargeAQuarticProfile_fourth_harmonics, egbFixedChargeAQuarticProfile_harmonic_decomposition]
  ring

theorem egbFixedChargeAFourthHarmonicProjector_uniform_first_zero_limit (w φ l₁ l₂ : ℝ) :
    TendstoUniformly (fun τ ψ =>
      (egbFixedChargeAFourthHarmonicProjector (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ - cos (4 * ψ)) /
        egbCoexistenceASymmetricRatio τ) (fun _ => (0 : ℝ)) atBot := by
  have h := egbFixedChargeALinearJetObservable_uniform_first_zero_limit w φ l₁ l₂ 0 (1 / 6) (1 / 24) 0 2 4
  change TendstoUniformly (fun τ ψ =>
      (egbFixedChargeAFourthHarmonicProjector (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ -
       egbFixedChargeAFourthHarmonicProjector (fun x : ℝ => cos x ^ 4) ψ) / egbCoexistenceASymmetricRatio τ)
      (fun _ => (0 : ℝ)) atBot at h
  simpa only [egbFixedChargeAFourthHarmonicProjector_critical] using h

theorem egbFixedChargeAFourthHarmonicProjector_uniform_limit (w φ l₁ l₂ : ℝ) :
    TendstoUniformly (fun τ ψ =>
      egbFixedChargeAFourthHarmonicProjector (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ)
      (fun ψ => cos (4 * ψ)) atBot := by
  have h := egbFixedChargeALinearJetObservable_uniform_limit w φ l₁ l₂ 0 (1 / 6) (1 / 24) 0 2 4
  change TendstoUniformly (fun τ ψ =>
      egbFixedChargeAFourthHarmonicProjector (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ)
      (fun ψ => egbFixedChargeAFourthHarmonicProjector (fun x : ℝ => cos x ^ 4) ψ) atBot at h
  simpa only [egbFixedChargeAFourthHarmonicProjector_critical] using h

theorem egbFixedChargeAConstantHarmonicProjector_critical (ψ : ℝ) :
    egbFixedChargeAConstantHarmonicProjector (fun x : ℝ => cos x ^ 4) ψ = (3 / 8 : ℝ) := by
  unfold egbFixedChargeAConstantHarmonicProjector egbFixedChargeALinearJetObservable
  rw [iteratedDeriv_zero, egbFixedChargeAQuarticProfile_second_harmonics,
    egbFixedChargeAQuarticProfile_fourth_harmonics, egbFixedChargeAQuarticProfile_harmonic_decomposition]
  ring

theorem egbFixedChargeAConstantHarmonicProjector_uniform_first_zero_limit (w φ l₁ l₂ : ℝ) :
    TendstoUniformly (fun τ ψ =>
      (egbFixedChargeAConstantHarmonicProjector (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ - (3 / 8 : ℝ)) /
        egbCoexistenceASymmetricRatio τ) (fun _ => (0 : ℝ)) atBot := by
  have h := egbFixedChargeALinearJetObservable_uniform_first_zero_limit w φ l₁ l₂ 1 (5 / 16) (1 / 64) 0 2 4
  change TendstoUniformly (fun τ ψ =>
      (egbFixedChargeAConstantHarmonicProjector (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ -
       egbFixedChargeAConstantHarmonicProjector (fun x : ℝ => cos x ^ 4) ψ) / egbCoexistenceASymmetricRatio τ)
      (fun _ => (0 : ℝ)) atBot at h
  simpa only [egbFixedChargeAConstantHarmonicProjector_critical] using h

theorem egbFixedChargeAConstantHarmonicProjector_uniform_limit (w φ l₁ l₂ : ℝ) :
    TendstoUniformly (fun τ ψ =>
      egbFixedChargeAConstantHarmonicProjector (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ)
      (fun _ => (3 / 8 : ℝ)) atBot := by
  have h := egbFixedChargeALinearJetObservable_uniform_limit w φ l₁ l₂ 1 (5 / 16) (1 / 64) 0 2 4
  change TendstoUniformly (fun τ ψ =>
      egbFixedChargeAConstantHarmonicProjector (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ)
      (fun ψ => egbFixedChargeAConstantHarmonicProjector (fun x : ℝ => cos x ^ 4) ψ) atBot at h
  simpa only [egbFixedChargeAConstantHarmonicProjector_critical] using h

end GaloisForLFunctions.HTGeometry
