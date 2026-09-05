import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaEllipticIntegralOrder
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaNegativeOneUniformization
import Mathlib.Tactic

/-!
# Exact closure transport between `m=-1` and `m=1/2`

The paper singles out `m=-1 ↔ n=1/2` as its simplest extended/classical Jacobi pair.  The corpus
already identifies both parameters with the same lemniscatic Weierstrass class.  Here the new
complete-integral infrastructure identifies their periods and vertical-closure equations exactly,
without the paper's decimal evaluations.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- The classical lemniscatic Jacobi parameter. -/
noncomputable def halfClassicalModulus : ClassicalModulus :=
  ⟨1 / 2, by norm_num⟩

theorem negativeOne_to_halfClassical :
    extendedToClassical negativeOneModulus = halfClassicalModulus := by
  apply Subtype.ext
  norm_num [negativeOneModulus, halfClassicalModulus, extendedToClassical]

/-- First-kind period scaling for the `-1 ↔ 1/2` pair. -/
theorem completeEllipticK_negativeOne :
    completeEllipticK (-1) =
      (Real.sqrt 2)⁻¹ * completeEllipticK (1 / 2) := by
  have h := completeEllipticK_negative_transform_raw negativeOneModulus
  rw [negativeOne_to_halfClassical] at h
  convert h using 1 <;> norm_num [negativeOneModulus, halfClassicalModulus]

/-- Second-kind period scaling for the `-1 ↔ 1/2` pair. -/
theorem completeEllipticE_negativeOne :
    completeEllipticE (-1) =
      Real.sqrt 2 * completeEllipticE (1 / 2) := by
  have h := completeEllipticE_negative_transform_raw negativeOneModulus
  rw [negativeOne_to_halfClassical] at h
  convert h using 1 <;> norm_num [negativeOneModulus, halfClassicalModulus]

theorem closureQ_negativeOne_transform :
    closureQ (-1) =
      2 * (2 * completeEllipticE (1 / 2) /
        completeEllipticK (1 / 2) - 1) := by
  have h := closureQ_negative_transform negativeOneModulus
  rw [negativeOne_to_halfClassical] at h
  convert h using 1 <;>
    norm_num [negativeOneModulus, halfClassicalModulus, classicalClosureCore]

/-- Exact closure-root equivalence at the paper's illustrative Jacobi pair. -/
theorem closureQ_negativeOne_eq_zero_iff :
    closureQ (-1) = 0 ↔
      2 * completeEllipticE (1 / 2) = completeEllipticK (1 / 2) := by
  have h := closureQ_negative_eq_zero_iff negativeOneModulus
  rw [negativeOne_to_halfClassical] at h
  simpa [negativeOneModulus, halfClassicalModulus] using h

/-- The extended zero condition is the classical torsionless condition at `m=1/2`. -/
theorem closureQ_negativeOne_zero_iff_half_torsionless :
    closureQ (-1) = 0 ↔ closureQ (1 / 2) = 1 / 2 := by
  have h := closureQ_negative_zero_iff_classical_torsionless negativeOneModulus
  rw [negativeOne_to_halfClassical] at h
  simpa [negativeOneModulus, halfClassicalModulus] using h

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
