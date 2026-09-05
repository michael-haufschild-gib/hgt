import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaJacobiQuotients
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaJacobiSystem
import Mathlib.Tactic

/-!
# Alternative Jacobi curvature branches

The `sc` and `sd` cases listed after the paper's quartic reduction are promoted from polynomial
templates to actual local squared-curvature solutions.  Canonical squared speed and torsion
parameters are reconstructed for each branch, and no cancellation by the leading coefficient is
used, so singular endpoint moduli remain covered.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

noncomputable def scGammaSq (m : ℝ) (q₀ : ℝˣ) : ℝ :=
  (m - 2) / (q₀ : ℝ) - 3

noncomputable def scNuSq (m : ℝ) (q₀ : ℝˣ) : ℝ :=
  2 + scGammaSq m q₀ - (1 - m) / (q₀ : ℝ) ^ 2

noncomputable def scSquaredCurvature
    (q₀ : ℝˣ) {m : ℝ} (J : JacobiEllipticSystem m) (x : ℝ) : ℝ :=
  (q₀ : ℝ) - (1 - m) * jacobiSc J x ^ 2

noncomputable def scSquaredCurvatureVelocity
    {m : ℝ} (J : JacobiEllipticSystem m) (x : ℝ) : ℝ :=
  -2 * (1 - m) * jacobiSc J x * jacobiScVelocity J x

theorem scSquaredCurvature_hasDerivAt
    (q₀ : ℝˣ) {m : ℝ} (J : JacobiEllipticSystem m)
    (x : JacobiCnRegularPoint J) :
    HasDerivAt (scSquaredCurvature q₀ J)
      (scSquaredCurvatureVelocity J x.val) x.val := by
  have hsq := (jacobiSc_hasDerivAt J x).fun_pow 2
  norm_num at hsq
  have hmul := HasDerivAt.const_mul (1 - m) hsq
  have h := HasDerivAt.const_sub (q₀ : ℝ) hmul
  have hderiv :
      -((1 - m) *
          (2 * jacobiSc J x.val * jacobiScVelocity J x.val)) =
        scSquaredCurvatureVelocity J x.val := by
    rw [scSquaredCurvatureVelocity]
    ring
  change HasDerivAt
    (fun y => (q₀ : ℝ) - (1 - m) * jacobiSc J y ^ 2)
    (scSquaredCurvatureVelocity J x.val) x.val
  exact h.congr_deriv hderiv

theorem scSquaredCurvature_zero
    (q₀ : ℝˣ) {m : ℝ} (J : JacobiEllipticSystem m) :
    scSquaredCurvature q₀ J 0 = (q₀ : ℝ) := by
  rw [scSquaredCurvature, jacobiSc_zero]
  ring

theorem scSquaredCurvatureVelocity_zero
    {m : ℝ} (J : JacobiEllipticSystem m) :
    scSquaredCurvatureVelocity J 0 = 0 := by
  rw [scSquaredCurvatureVelocity, jacobiSc_zero]
  ring

theorem scSquaredCurvature_equation
    (q₀ : ℝˣ) {m : ℝ} (J : JacobiEllipticSystem m)
    (x : JacobiCnRegularPoint J) :
    scSquaredCurvatureVelocity J x.val ^ 2 =
      dimensionlessCurvatureRHSWithSquares (q₀ : ℝ)
        (scGammaSq m q₀) (scNuSq m q₀)
        (scSquaredCurvature q₀ J x.val) := by
  have hfirst := jacobiSc_firstIntegral J x
  have hres := curvatureSubstitution_residual_withSquares
    (1 - m) (q₀ : ℝ) (scGammaSq m q₀) (scNuSq m q₀)
    (jacobiSc J x.val) (jacobiScVelocity J x.val)
  have hcleared :
      clearedJacobiResidual (1 - m) (q₀ : ℝ)
        (scGammaSq m q₀) (scNuSq m q₀)
        (jacobiSc J x.val) (jacobiScVelocity J x.val) = 0 := by
    rw [clearedJacobiResidual, scNuSq, scGammaSq]
    field_simp [q₀.ne_zero]
    rw [hfirst]
    ring
  rw [hcleared, mul_zero] at hres
  rw [scSquaredCurvatureVelocity, scSquaredCurvature]
  linarith

noncomputable def sdGammaSq (m : ℝ) (q₀ : ℝˣ) : ℝ :=
  (1 - 2 * m) / (q₀ : ℝ) - 3

noncomputable def sdNuSq (m : ℝ) (q₀ : ℝˣ) : ℝ :=
  2 + sdGammaSq m q₀ - (-m * (1 - m)) / (q₀ : ℝ) ^ 2

noncomputable def sdSquaredCurvature
    (q₀ : ℝˣ) {m : ℝ} (J : JacobiEllipticSystem m) (x : ℝ) : ℝ :=
  (q₀ : ℝ) - (-m * (1 - m)) * jacobiSd J x ^ 2

noncomputable def sdSquaredCurvatureVelocity
    {m : ℝ} (J : JacobiEllipticSystem m) (x : ℝ) : ℝ :=
  -2 * (-m * (1 - m)) * jacobiSd J x * jacobiSdVelocity J x

theorem sdSquaredCurvature_hasDerivAt
    (q₀ : ℝˣ) {m : ℝ} (J : JacobiEllipticSystem m)
    (x : JacobiDnRegularPoint J) :
    HasDerivAt (sdSquaredCurvature q₀ J)
      (sdSquaredCurvatureVelocity J x.val) x.val := by
  have hsq := (jacobiSd_hasDerivAt J x).fun_pow 2
  norm_num at hsq
  have hmul := HasDerivAt.const_mul (-m * (1 - m)) hsq
  have h := HasDerivAt.const_sub (q₀ : ℝ) hmul
  have hderiv :
      -((-m * (1 - m)) *
          (2 * jacobiSd J x.val * jacobiSdVelocity J x.val)) =
        sdSquaredCurvatureVelocity J x.val := by
    rw [sdSquaredCurvatureVelocity]
    ring
  change HasDerivAt
    (fun y => (q₀ : ℝ) - (-m * (1 - m)) * jacobiSd J y ^ 2)
    (sdSquaredCurvatureVelocity J x.val) x.val
  exact h.congr_deriv hderiv

theorem sdSquaredCurvature_zero
    (q₀ : ℝˣ) {m : ℝ} (J : JacobiEllipticSystem m) :
    sdSquaredCurvature q₀ J 0 = (q₀ : ℝ) := by
  rw [sdSquaredCurvature, jacobiSd_zero]
  ring

theorem sdSquaredCurvatureVelocity_zero
    {m : ℝ} (J : JacobiEllipticSystem m) :
    sdSquaredCurvatureVelocity J 0 = 0 := by
  rw [sdSquaredCurvatureVelocity, jacobiSd_zero]
  ring

theorem sdSquaredCurvature_equation
    (q₀ : ℝˣ) {m : ℝ} (J : JacobiEllipticSystem m)
    (x : JacobiDnRegularPoint J) :
    sdSquaredCurvatureVelocity J x.val ^ 2 =
      dimensionlessCurvatureRHSWithSquares (q₀ : ℝ)
        (sdGammaSq m q₀) (sdNuSq m q₀)
        (sdSquaredCurvature q₀ J x.val) := by
  have hfirst := jacobiSd_firstIntegral J x
  have hres := curvatureSubstitution_residual_withSquares
    (-m * (1 - m)) (q₀ : ℝ) (sdGammaSq m q₀) (sdNuSq m q₀)
    (jacobiSd J x.val) (jacobiSdVelocity J x.val)
  have hcleared :
      clearedJacobiResidual (-m * (1 - m)) (q₀ : ℝ)
        (sdGammaSq m q₀) (sdNuSq m q₀)
        (jacobiSd J x.val) (jacobiSdVelocity J x.val) = 0 := by
    rw [clearedJacobiResidual, sdNuSq, sdGammaSq]
    field_simp [q₀.ne_zero]
    rw [hfirst]
    ring
  rw [hcleared, mul_zero] at hres
  rw [sdSquaredCurvatureVelocity, sdSquaredCurvature]
  linarith

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
