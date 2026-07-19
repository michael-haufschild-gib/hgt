import GaloisForLFunctions.HTGeometry.InfinityLeafAtoms
import GaloisForLFunctions.HTGeometry.CarriedAtomic

/-!
# The leaf as a function of the parameter

The per-parameter existence statements assemble into a single map `OnePoint ℝ → ProbabilityMeasure ℝ`
by choice, and each of its defining properties transfers termwise.

This supplies every field of `ClassicalNevanlinnaExtremalFamily` except weak continuity in the
parameter.
-/

open scoped BigOperators
open MeasureTheory OnePoint
open scoped OnePoint

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **The N-extremal leaf of each parameter.** -/
noncomputable def nevLeaf (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    (t : OnePoint ℝ) : ProbabilityMeasure ℝ :=
  t.elim (exists_leaf_infinity_atoms h h0b h0).choose
    (fun x => (exists_leaf_atoms h h0b h0 x).choose)

@[simp] theorem nevLeaf_infty (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) :
    nevLeaf h h0b h0 ∞ = (exists_leaf_infinity_atoms h h0b h0).choose := rfl

@[simp] theorem nevLeaf_coe (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    (x : ℝ) :
    nevLeaf h h0b h0 (x : OnePoint ℝ) = (exists_leaf_atoms h h0b h0 x).choose := rfl

/-- **Every leaf represents the moment sequence.**  This is the `leaf_moments` field. -/
theorem nevLeaf_hasHamburgerMoments (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) (t : OnePoint ℝ) :
    GaloisForLFunctions.HTGeometry.HasHamburgerMoments s
      (nevLeaf h h0b h0 t : Measure ℝ) := by
  induction t using OnePoint.rec with
  | infty => exact (exists_leaf_infinity_atoms h h0b h0).choose_spec.1
  | coe x => exact (exists_leaf_atoms h h0b h0 x).choose_spec.1

/-- **The `finite_carried` field.** -/
theorem nevLeaf_finite_carried (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) (tau : ℝ) :
    (nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ)
        ((nevMatrixDataInf h h0b).finiteDenominatorFiber tau)ᶜ = 0 :=
  (exists_leaf_atoms h h0b h0 tau).choose_spec.2.1

/-- **The `infinity_carried` field.** -/
theorem nevLeaf_infinity_carried (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) :
    (nevLeaf h h0b h0 ∞ : Measure ℝ)
        (nevMatrixDataInf h h0b).infinityDenominatorFiberᶜ = 0 :=
  (exists_leaf_infinity_atoms h h0b h0).choose_spec.2.1

/-- **The weights of a finite-parameter leaf are the Christoffel limits.** -/
theorem nevLeaf_atoms (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    (tau : ℝ) {ξ : ℝ} (hξ : ξ ∈ (nevMatrixDataInf h h0b).finiteDenominatorFiber tau) :
    (nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ) {ξ}
      = ENNReal.ofReal (christoffelLimit s ξ) :=
  (exists_leaf_atoms h h0b h0 tau).choose_spec.2.2 ξ hξ

/-- **The weights of the leaf at infinity are the Christoffel limits.** -/
theorem nevLeaf_infinity_atoms (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) {ξ : ℝ}
    (hξ : ξ ∈ (nevMatrixDataInf h h0b).infinityDenominatorFiber) :
    (nevLeaf h h0b h0 ∞ : Measure ℝ) {ξ} = ENNReal.ofReal (christoffelLimit s ξ) :=
  (exists_leaf_infinity_atoms h h0b h0).choose_spec.2.2 ξ hξ

/-- **Every leaf is its own atomic part on its carrier.**  Combining the carriedness with the
countability of the fiber, the leaf is the explicit weighted Dirac family with weights `λ`. -/
theorem nevLeaf_eq_fiberMeasure (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) (tau : ℝ) :
    (nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ)
      = fiberMeasure (fun x => christoffelLimit s x)
          ((nevMatrixDataInf h h0b).finiteDenominatorFiber tau) := by
  have hcar := nevLeaf_finite_carried h h0b h0 tau
  have hbase := measure_eq_fiberMeasure_of_carried
    (nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ)
    (countable_finiteDenominatorFiber h h0b tau)
    (isClosed_finiteDenominatorFiber h h0b tau).measurableSet hcar
  rw [hbase, fiberMeasure, fiberMeasure]
  refine congrArg Measure.sum (funext fun p => ?_)
  rw [nevLeaf_atoms h h0b h0 tau p.2, ENNReal.toReal_ofReal (christoffelLimit_nonneg h _)]

end HTGeometry
