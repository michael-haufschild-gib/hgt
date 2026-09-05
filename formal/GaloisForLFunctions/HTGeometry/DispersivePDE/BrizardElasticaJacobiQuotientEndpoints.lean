import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaJacobiAlternativeCurvature
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaJacobiEndpoints
import Mathlib.Tactic

/-!
# Endpoint degenerations of the Jacobi quotient branches

At `m=0`, `sc` becomes tangent while `sd` becomes sine.  At `m=1`, both quotients become
hyperbolic sine.  The associated curvature coefficients show which alternatives collapse and
which develop poles.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

theorem jacobiZeroSc_eq_tan (x : ℝ) :
    jacobiSc jacobiZeroSystem x = Real.tan x := by
  rw [jacobiSc, jacobiZeroSystem, Real.tan_eq_sin_div_cos]

theorem jacobiZeroScVelocity_eq (x : ℝ) :
    jacobiScVelocity jacobiZeroSystem x = 1 / Real.cos x ^ 2 := by
  rw [jacobiScVelocity, jacobiZeroSystem]

theorem jacobiZeroSd_eq_sin (x : ℝ) :
    jacobiSd jacobiZeroSystem x = Real.sin x := by
  rw [jacobiSd, jacobiZeroSystem]
  ring

theorem jacobiZeroSdVelocity_eq_cos (x : ℝ) :
    jacobiSdVelocity jacobiZeroSystem x = Real.cos x := by
  rw [jacobiSdVelocity, jacobiZeroSystem]
  ring

theorem jacobiOneSc_eq_sinh (x : ℝ) :
    jacobiSc jacobiOneSystem x = Real.sinh x := by
  change solitonT x / solitonA x = Real.sinh x
  rw [solitonT, solitonA, Real.tanh_eq_sinh_div_cosh]
  field_simp [ne_of_gt (Real.cosh_pos x)]

theorem jacobiOneSd_eq_sinh (x : ℝ) :
    jacobiSd jacobiOneSystem x = Real.sinh x := by
  change solitonT x / solitonA x = Real.sinh x
  rw [solitonT, solitonA, Real.tanh_eq_sinh_div_cosh]
  field_simp [ne_of_gt (Real.cosh_pos x)]

theorem jacobiOneScVelocity_eq_cosh (x : ℝ) :
    jacobiScVelocity jacobiOneSystem x = Real.cosh x := by
  change solitonA x / solitonA x ^ 2 = Real.cosh x
  rw [solitonA]
  field_simp [ne_of_gt (Real.cosh_pos x)]

theorem jacobiOneSdVelocity_eq_cosh (x : ℝ) :
    jacobiSdVelocity jacobiOneSystem x = Real.cosh x := by
  change solitonA x / solitonA x ^ 2 = Real.cosh x
  rw [solitonA]
  field_simp [ne_of_gt (Real.cosh_pos x)]

/-- At `m=0`, the `sd` curvature branch collapses to constant curvature. -/
theorem zeroSdSquaredCurvature_eq (q₀ : ℝˣ) (x : ℝ) :
    sdSquaredCurvature q₀ jacobiZeroSystem x = (q₀ : ℝ) := by
  rw [sdSquaredCurvature]
  ring

/-- At `m=1`, the `sc` branch also collapses to constant curvature. -/
theorem oneScSquaredCurvature_eq (q₀ : ℝˣ) (x : ℝ) :
    scSquaredCurvature q₀ jacobiOneSystem x = (q₀ : ℝ) := by
  rw [scSquaredCurvature]
  ring

/-- At `m=1`, the `sd` branch collapses at the same endpoint. -/
theorem oneSdSquaredCurvature_eq (q₀ : ℝˣ) (x : ℝ) :
    sdSquaredCurvature q₀ jacobiOneSystem x = (q₀ : ℝ) := by
  rw [sdSquaredCurvature]
  ring

/-- Positive scale and modulus at most one, the standard real `sc` regime. -/
structure ClassicalScParameters where
  modulus : ℝ
  q₀ : ℝˣ
  modulus_le_one : modulus ≤ 1
  q₀_pos : 0 < (q₀ : ℝ)

theorem classicalSc_gammaSq_neg (P : ClassicalScParameters) :
    scGammaSq P.modulus P.q₀ < 0 := by
  rw [scGammaSq]
  have hnum : P.modulus - 2 < 0 := by linarith [P.modulus_le_one]
  have hdiv := div_neg_of_neg_of_pos hnum P.q₀_pos
  linarith

/-- Thus the standard real `sc` branch cannot carry a real traveling-wave speed. -/
theorem classicalSc_no_real_gamma (P : ClassicalScParameters) :
    ¬ ∃ γ : ℝ, γ ^ 2 = scGammaSq P.modulus P.q₀ := by
  rintro ⟨γ, hγ⟩
  have hneg := classicalSc_gammaSq_neg P
  nlinarith [sq_nonneg γ]

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
