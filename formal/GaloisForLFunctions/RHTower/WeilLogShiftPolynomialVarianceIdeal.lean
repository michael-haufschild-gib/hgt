import GaloisForLFunctions.RHTower.WeilLogShiftPolynomialVarianceKernel
import GaloisForLFunctions.HTGeometry.BinaryPolynomialDiagonalNormalForm

/-! The limiting polynomial variance kernel is constants plus the variable-difference ideal. -/

open MeasureTheory ProbabilityTheory Filter Topology GaloisForLFunctions.HTGeometry
local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "P₂" => MvPolynomial (Fin 2) ℝ
local notation "Δ" => (MvPolynomial.X (0 : Fin 2) - MvPolynomial.X (1 : Fin 2) : P₂)
local notation "ρ" => MvPolynomial.rename (R := ℝ) (fun _ : Fin 2 => (1 : Fin 2))

namespace RHTower

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_polynomial_variance_zero_iff_dvd
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2}) (p : P₂) :
    Tendsto (fun r => variance (fun z : E => MvPolynomial.eval (fun i => z i) p)
      (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure E))
      atTop (𝓝 0) ↔ Δ ∣ p - MvPolynomial.C (MvPolynomial.eval (fun _ => 0) p) := by
  rw [tendsto_finiteWeilCanonicalJointQuadraticTilt_polynomial_variance_zero_iff]
  exact binaryPolynomial_diagonal_constant_iff_dvd p

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_polynomial_variance_zero_iff_unique_factor
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2}) (p : P₂) :
    Tendsto (fun r => variance (fun z : E => MvPolynomial.eval (fun i => z i) p)
      (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure E))
      atTop (𝓝 0) ↔
        ∃! q : P₂, p = MvPolynomial.C (MvPolynomial.eval (fun _ => 0) p) + Δ * q := by
  rw [tendsto_finiteWeilCanonicalJointQuadraticTilt_polynomial_variance_zero_iff]
  exact binaryPolynomial_diagonal_constant_iff_existsUnique p

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_polynomial_diagonal_defect_variance_zero
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2}) (p : P₂) :
    Tendsto (fun r => variance (fun z : E => MvPolynomial.eval (fun i => z i) (p - ρ p))
      (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure E))
      atTop (𝓝 0) := by
  apply (tendsto_finiteWeilCanonicalJointQuadraticTilt_polynomial_variance_zero_iff
    t a b d (p - ρ p)).mpr
  intro x
  simp only [map_sub, MvPolynomial.eval_rename, Function.comp_def, sub_self]

end RHTower
