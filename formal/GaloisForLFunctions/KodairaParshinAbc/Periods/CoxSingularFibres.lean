import GaloisForLFunctions.GaloisTheoryOfZeros.Probability.FiniteGammaCoxLaw
import GaloisForLFunctions.KodairaParshinAbc.Periods.CubicMirrorCurve

/-!
# Gamma–Cox detection of singular cubic-mirror fibres

The discriminant factorization gives an explicit detector for the two finite
singular parameters. Its binary output detects their presence, not their unequal
orders of vanishing in the discriminant.
-/

open scoped Classical
open Filter Topology
open GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox
namespace GaloisForLFunctions.KodairaParshinAbc.CubicMirror
noncomputable section

/-- The real cubic-mirror pencil has precisely two finite singular parameters. -/
theorem real_discriminant_zero_iff (t : ℝ) :
    (curve t).Δ = 0 ↔ t = 0 ∨ t = 1 / 27 := by
  rw [discriminant]
  have h : 1 - 27 * t = 0 ↔ t = 1 / 27 := by constructor <;> intro ht <;> linarith
  simp only [mul_eq_zero, pow_eq_zero_iff (by norm_num : 3 ≠ 0), h]
  norm_num

/-- Discriminant detection converges to the exact singular-parameter indicator. -/
theorem cox_singular_fibre (t : ℝ) :
    Tendsto (fun K => detection K (curve t).Δ) atTop
      (𝓝 (if t = 0 ∨ t = 1 / 27 then 1 else 0)) := by
  simpa only [real_discriminant_zero_iff] using tendsto_detection (curve t).Δ

/-- Every fibre in a finite parameter list is classified simultaneously. -/
theorem cox_singular_fibre_family {ι : Type*} [Fintype ι] (t : ι → ℝ) :
    Tendsto (fun K => (binaryLaw K (fun i => (curve (t i)).Δ)).real
      {b | b ≠ fun i => decide (t i = 0 ∨ t i = 1 / 27)}) atTop (𝓝 0) := by
  simpa only [zeroPattern, real_discriminant_zero_iff] using
    tendsto_binaryLaw_error (fun i => (curve (t i)).Δ)

end
end GaloisForLFunctions.KodairaParshinAbc.CubicMirror

#print axioms GaloisForLFunctions.KodairaParshinAbc.CubicMirror.real_discriminant_zero_iff
#print axioms GaloisForLFunctions.KodairaParshinAbc.CubicMirror.cox_singular_fibre
#print axioms GaloisForLFunctions.KodairaParshinAbc.CubicMirror.cox_singular_fibre_family
