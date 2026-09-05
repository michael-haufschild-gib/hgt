import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaAlgebra
import Mathlib.Tactic

/-!
# Algebraic Jacobi-quartic reduction in arXiv:2607.21750

Paper equations (64)--(66) replace the squared-curvature cubic by a quartic first integral after
`q = q₀ - aP²`.  Cancellation by `aP²` is not valid at a turning point, including the prescribed
initial point `P(0)=0`.  This module keeps the exact residual factor before cancellation, proves the
three Jacobi polynomial forms (`sn`, `sc`, and `sd`), and shows that Brizard's parameter formulas
select the `sn` polynomial globally.  Nonzero modulus is packaged when cancellation is required.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Factored right side of paper equation (64). -/
def dimensionlessCurvatureRHS (q₀ γ ν q : ℝ) : ℝ :=
  4 * (q₀ - q) * (q ^ 2 + (1 + γ ^ 2) * q₀ * q - q₀ ^ 2 * ν ^ 2)

/-- Equation (66), cleared of division by the quartic leading coefficient `a`. -/
def clearedJacobiResidual (a q₀ γsq νsq X Y : ℝ) : ℝ :=
  a * Y ^ 2 -
    (a ^ 2 * X ^ 4 - a * (3 + γsq) * q₀ * X ^ 2 +
      (2 + γsq - νsq) * q₀ ^ 2)

/-- Exact pre-cancellation identity behind the cubic-to-quartic substitution. -/
theorem curvatureSubstitution_residual (a q₀ γ ν X Y : ℝ) :
    (-2 * a * X * Y) ^ 2 -
        dimensionlessCurvatureRHS q₀ γ ν (q₀ - a * X ^ 2) =
      4 * a * X ^ 2 * clearedJacobiResidual a q₀ (γ ^ 2) (ν ^ 2) X Y := by
  rw [dimensionlessCurvatureRHS, clearedJacobiResidual]
  ring

/-- Standard `sn` first-integral polynomial. -/
theorem jacobiSnPolynomial (m X : ℝ) :
    (1 - X ^ 2) * (1 - m * X ^ 2) =
      m * X ^ 4 - (1 + m) * X ^ 2 + 1 := by
  ring

/-- Standard `sc` first-integral polynomial. -/
theorem jacobiScPolynomial (m X : ℝ) :
    (1 + X ^ 2) * (1 + (1 - m) * X ^ 2) =
      (1 - m) * X ^ 4 + (2 - m) * X ^ 2 + 1 := by
  ring

/-- Standard `sd` first-integral polynomial. -/
theorem jacobiSdPolynomial (m X : ℝ) :
    (1 - (1 - m) * X ^ 2) * (1 + m * X ^ 2) =
      -m * (1 - m) * X ^ 4 + (2 * m - 1) * X ^ 2 + 1 := by
  ring

/-- Case (i) coefficient choice in the paragraph following paper equation (66). -/
theorem jacobiCaseSn (m X : ℝ) :
    m * X ^ 4 - (1 + m) * X ^ 2 + 1 =
      (1 - X ^ 2) * (1 - m * X ^ 2) := by
  rw [jacobiSnPolynomial]

/-- Case (ii) coefficient choice in the paragraph following paper equation (66). -/
theorem jacobiCaseSc (m X : ℝ) :
    (1 - m) * X ^ 4 + (2 - m) * X ^ 2 + 1 =
      (1 + X ^ 2) * (1 + (1 - m) * X ^ 2) := by
  rw [jacobiScPolynomial]

/-- Case (iii) coefficient choice in the paragraph following paper equation (66). -/
theorem jacobiCaseSd (m X : ℝ) :
    -m * (1 - m) * X ^ 4 + (2 * m - 1) * X ^ 2 + 1 =
      (1 - (1 - m) * X ^ 2) * (1 + m * X ^ 2) := by
  rw [jacobiSdPolynomial]

/-- Brizard's parameter formulas make the cleared quartic exactly `m` times the `sn` law. -/
theorem parameterJacobiResidual_factor (P : Parameters) (X Y : ℝ) :
    clearedJacobiResidual P.modulus (P.q₀ : ℝ) (gammaSq P) (nuSq P) X Y =
      P.modulus * (Y ^ 2 - (1 - X ^ 2) * (1 - P.modulus * X ^ 2)) := by
  have h₁ := modulus_eq_q₀_mul_gammaSq P
  have h₂ := modulus_eq_q₀_sq_mul_gammaSq_sub_nuSq P
  have hc₁ : (3 + gammaSq P) * (P.q₀ : ℝ) = 1 + P.modulus := by
    calc
      (3 + gammaSq P) * (P.q₀ : ℝ) =
          (P.q₀ : ℝ) * (3 + gammaSq P) := by ring
      _ = 1 + P.modulus := by linarith
  have hc₂ : (2 + gammaSq P - nuSq P) * (P.q₀ : ℝ) ^ 2 = P.modulus := by
    calc
      (2 + gammaSq P - nuSq P) * (P.q₀ : ℝ) ^ 2 =
          (P.q₀ : ℝ) ^ 2 * (2 + gammaSq P - nuSq P) := by ring
      _ = P.modulus := h₂.symm
  have hmiddle :
      P.modulus * (3 + gammaSq P) * (P.q₀ : ℝ) =
        P.modulus * (1 + P.modulus) := by
    calc
      P.modulus * (3 + gammaSq P) * (P.q₀ : ℝ) =
          P.modulus * ((3 + gammaSq P) * (P.q₀ : ℝ)) := by ring
      _ = P.modulus * (1 + P.modulus) := by rw [hc₁]
  rw [clearedJacobiResidual]
  rw [hmiddle, hc₂]
  ring

/-- The prescribed initial data `P=0`, `P'=1` satisfy the cleared quartic for every parameter. -/
theorem parameterJacobiResidual_initial (P : Parameters) :
    clearedJacobiResidual P.modulus (P.q₀ : ℝ) (gammaSq P) (nuSq P) 0 1 = 0 := by
  rw [parameterJacobiResidual_factor]
  ring

/-- Parameter data on which the quartic cancellation by the modulus is legitimate. -/
abbrev NonzeroModulusParameters := {P : Parameters // P.modulus ≠ 0}

/-- Away from the singular modulus, Brizard's quartic is equivalent to the `sn` first integral. -/
theorem parameterJacobiResidual_eq_zero_iff (P : NonzeroModulusParameters) (X Y : ℝ) :
    clearedJacobiResidual P.val.modulus (P.val.q₀ : ℝ)
        (gammaSq P.val) (nuSq P.val) X Y = 0 ↔
      Y ^ 2 = (1 - X ^ 2) * (1 - P.val.modulus * X ^ 2) := by
  rw [parameterJacobiResidual_factor, mul_eq_zero]
  simp only [P.property, false_or]
  exact sub_eq_zero

/-- At `m=0` the cleared equation vanishes identically, exposing the forbidden cancellation. -/
theorem zeroModulusJacobiResidual (q₀ : ℝˣ) (X Y : ℝ) :
    clearedJacobiResidual 0 (q₀ : ℝ)
        (gammaSq { modulus := 0, q₀ := q₀ })
        (nuSq { modulus := 0, q₀ := q₀ }) X Y = 0 := by
  simpa using parameterJacobiResidual_factor
    ({ modulus := 0, q₀ := q₀ } : Parameters) X Y

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
