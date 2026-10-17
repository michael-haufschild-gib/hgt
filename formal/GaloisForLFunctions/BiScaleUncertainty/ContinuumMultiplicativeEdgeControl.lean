import GaloisForLFunctions.BiScaleUncertainty.ContinuumShearDirichlet
import GaloisForLFunctions.BiScaleUncertainty.CoprimeShearAndMultiplicativeGraphUncertainty

/-!
# Multiplicative edges controlled by physical additive energy

For states constructed from an arbitrary continuous logarithmic velocity, the edge
from `x` to `x + log (n+1)` has resistance `n * exp x`. Its squared jump and its
opposite-sign nodal pairing are bounded by that resistance times the additive
Dirichlet energy along the edge. Finite nonnegative weighted edge families inherit
the bound. These statements concern the actual continuum endpoints, not integer
samples; infinite weighted graph-domain admission is a separate question.
-/

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory

namespace GaloisForLFunctions.BiScaleUncertainty.ContinuumShear

set_option autoImplicit false

/-- Multiplication by `n+1` in the physical coordinate. -/
def multiplicativeJump (q : C(ℝ, ℝ)) (n : ℕ) (x : ℝ) : ℝ :=
  primitive q (x + Real.log (n+1 : ℝ)) - primitive q x

/-- Additive energy along a multiplicative edge. -/
def edgeEnergy (q : C(ℝ, ℝ)) (n : ℕ) (x : ℝ) : ℝ :=
  ∫ y in x..(x + Real.log (n+1 : ℝ)), Real.exp (-y) * (deriv (primitive q) y)^2

/-- Exact physical resistance of the logarithmic edge. -/
theorem multiplicativeJump_sq_le (q : C(ℝ, ℝ)) (n : ℕ) (x : ℝ) :
    (multiplicativeJump q n x)^2 ≤ (n : ℝ) * Real.exp x * edgeEnergy q n x := by
  have he : Real.exp (x + Real.log (n+1 : ℝ)) = Real.exp x + (n : ℝ) * Real.exp x := by
    rw [Real.exp_add, Real.exp_log (by positivity)]
    ring
  unfold multiplicativeJump edgeEnergy
  rw [← logarithmicEnergy_eq_derivative]
  have h := logarithmic_increment_sq_le q x
    ⟨Real.log (n+1 : ℝ), Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])⟩
  change (primitive q (x + Real.log (n+1 : ℝ)) - primitive q x)^2 ≤
    (Real.exp (x + Real.log (n+1 : ℝ)) - Real.exp x) *
      logarithmicEnergy q x (x + Real.log (n+1 : ℝ)) at h
  rw [he, add_sub_cancel_left] at h
  exact h

/-- Nonnegative weighted finite multiplicative graph edges inherit the continuum bound. -/
theorem weighted_multiplicativeJump_sq_le (q : C(ℝ, ℝ)) (s : Finset ℕ)
    (w : ℕ → ℝ≥0) (x : ℝ) :
    (∑ n ∈ s, (w n : ℝ) * (multiplicativeJump q n x)^2) ≤
      ∑ n ∈ s, (w n : ℝ) * ((n : ℝ) * Real.exp x * edgeEnergy q n x) := by
  exact Finset.sum_le_sum fun n _ =>
    mul_le_mul_of_nonneg_left (multiplicativeJump_sq_le q n x) (w n).coe_nonneg

/-- Opposite-sign endpoint pairing of a multiplicative edge. -/
def nodalPairing (q : C(ℝ, ℝ)) (c : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  max (c + primitive q (x + Real.log (n+1 : ℝ))) 0 * max (-(c + primitive q x)) 0 +
  max (-(c + primitive q (x + Real.log (n+1 : ℝ)))) 0 * max (c + primitive q x) 0

/-- The discrete nodal identity holds on the actual continuum multiplicative edge. -/
theorem multiplicativeJump_nodal_decomposition (q : C(ℝ, ℝ)) (c : ℝ) (n : ℕ) (x : ℝ) :
    (multiplicativeJump q n x)^2 =
      (|c + primitive q (x + Real.log (n+1 : ℝ))| - |c + primitive q x|)^2 +
        4 * nodalPairing q c n x := by
  have h := nodal_mulJump_sq_decomp
    (fun j : ℕ => c + primitive q (x + Real.log (j : ℝ))) (n+1) 1
  simpa [mulJump, seqPos, seqNeg, multiplicativeJump, nodalPairing] using h

/-- Additive continuum regularity controls opposite-sign multiplicative attraction. -/
theorem four_nodalPairing_le_energy (q : C(ℝ, ℝ)) (c : ℝ) (n : ℕ) (x : ℝ) :
    4 * nodalPairing q c n x ≤ (n : ℝ) * Real.exp x * edgeEnergy q n x := by
  have hj := multiplicativeJump_sq_le q n x
  have hd := multiplicativeJump_nodal_decomposition q c n x
  have hs := sq_nonneg (|c + primitive q (x + Real.log (n+1 : ℝ))| - |c + primitive q x|)
  linarith

theorem weighted_nodalPairing_le_energy (q : C(ℝ, ℝ)) (c : ℝ) (s : Finset ℕ)
    (w : ℕ → ℝ≥0) (x : ℝ) :
    (∑ n ∈ s, (w n : ℝ) * (4 * nodalPairing q c n x)) ≤
      ∑ n ∈ s, (w n : ℝ) * ((n : ℝ) * Real.exp x * edgeEnergy q n x) := by
  exact Finset.sum_le_sum fun n _ =>
    mul_le_mul_of_nonneg_left (four_nodalPairing_le_energy q c n x) (w n).coe_nonneg

end GaloisForLFunctions.BiScaleUncertainty.ContinuumShear
