import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryPauliHybridEuclideanMeasure
import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryHaarProductNullTransfer

/-!
# Product hybrid Euclidean coordinate measure for finite gate assignments

Taking the finite product of the globally centred local hybrid-coordinate
measure gives the coordinate law needed for a complete finite architecture.
-/

open MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Independent globally centred hybrid Euclidean-coordinate measures for a
finite tuple of two-qubit gates. -/
def boolTwoQubitHybridEuclideanProductMeasure
    (κ : Type*) [Fintype κ] (N : ℕ) (r : ℝ) :
    Measure (κ → Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :=
  Measure.pi fun _ => boolTwoQubitHybridEuclideanMeasure N r

/-- The total mass of the gate-assignment hybrid-coordinate measure is the
finite product of its one-gate masses. -/
theorem boolTwoQubitHybridEuclideanProductMeasure_apply_univ
    (κ : Type*) [Fintype κ] (N : ℕ) (r : ℝ) :
    boolTwoQubitHybridEuclideanProductMeasure κ N r Set.univ =
      ∏ _ : κ, boolTwoQubitHybridEuclideanMeasure N r Set.univ := by
  unfold boolTwoQubitHybridEuclideanProductMeasure
  exact Measure.pi_univ _

/-- Every positive-radius local hybrid-coordinate product has positive total
mass, including the empty gate tuple. -/
theorem boolTwoQubitHybridEuclideanProductMeasure_univ_pos
    (κ : Type*) [Fintype κ] (N : ℕ) {r : ℝ} (hr : 0 < r) :
    0 < boolTwoQubitHybridEuclideanProductMeasure κ N r Set.univ := by
  rw [boolTwoQubitHybridEuclideanProductMeasure_apply_univ]
  exact CanonicallyOrderedAdd.prod_pos.mpr fun _ _ =>
    boolTwoQubitHybridEuclideanMeasure_univ_pos N hr

/-- The finite product of local hybrid-coordinate measures is finite. -/
noncomputable instance boolTwoQubitHybridEuclideanProductMeasure_isFinite
    (κ : Type*) [Fintype κ] (N : ℕ) (r : ℝ) :
    IsFiniteMeasure (boolTwoQubitHybridEuclideanProductMeasure κ N r) := by
  unfold boolTwoQubitHybridEuclideanProductMeasure
  infer_instance

/-- Concrete architecture-level `SU(4)` Haar-null transfer for the product
global hybrid Euclidean-coordinate measure. -/
theorem finiteSpecialUnitaryHaarProduct_eq_zero_of_hybridEuclidean_translates_null
    {κ : Type*} [Fintype κ] (N : ℕ) {r : ℝ} (hr : 0 < r)
    {s : Set (κ → Matrix.specialUnitaryGroup (Bool × Bool) ℂ)}
    (hs : MeasurableSet s)
    (htrans : ∀ U : κ → Matrix.specialUnitaryGroup (Bool × Bool) ℂ,
      boolTwoQubitHybridEuclideanProductMeasure κ N r
        ((fun V => U * V) ⁻¹' s) = 0) :
    finiteSpecialUnitaryHaarProduct κ (Bool × Bool) s = 0 :=
  finiteSpecialUnitaryHaarProduct_eq_zero_of_all_left_translates_null
    (boolTwoQubitHybridEuclideanProductMeasure κ N r) hs
    (boolTwoQubitHybridEuclideanProductMeasure_univ_pos κ N hr) htrans

end

end GaloisForLFunctions.HTGeometry
