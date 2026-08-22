import GaloisForLFunctions.HTGeometry.FiniteUnitaryHaarMeasureLaw

/-!
# Normalized Haar probability on finite special unitary groups

The circuit ensemble in Haferkamp--Faist--Kothakonda--Eisert--Yunger Halpern
(2022) draws every two-qubit gate from `SU(4)`.  Mathlib supplies the
algebraic special-unitary group but not its compact topological-group and
normalized-Haar interfaces for finite complex matrices.  This module closes
that foundational gap without introducing assumptions or axioms.
-/

open MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

instance finiteSpecialUnitaryIsTopologicalGroup
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    IsTopologicalGroup (Matrix.specialUnitaryGroup ι ℂ) where
  continuous_mul := continuous_mul
  continuous_inv := by
    apply continuous_induced_rng.2
    change Continuous (fun U : Matrix.specialUnitaryGroup ι ℂ =>
      star (U.1 : Matrix ι ι ℂ))
    fun_prop

noncomputable instance finiteSpecialUnitaryCompactSpace
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    CompactSpace (Matrix.specialUnitaryGroup ι ℂ) := by
  refine isCompact_iff_compactSpace.mp ?_
  have hclosed : IsClosed
      {A : Matrix ι ι ℂ | A * star A = 1 ∧ A.det = 1} :=
    (isClosed_eq
      (by fun_prop :
        Continuous (fun A : Matrix ι ι ℂ => A * star A))
      continuous_const).and
    (isClosed_eq
      (by simpa using continuous_id.matrix_det :
        Continuous (fun A : Matrix ι ι ℂ => A.det))
      continuous_const)
  have hK : IsCompact
      ((Metric.closedBall (0 : ℂ) 1).matrix :
        Set (Matrix ι ι ℂ)) :=
    (isCompact_closedBall (0 : ℂ) 1).matrix
  have hcarrier :
      (↑(Matrix.specialUnitaryGroup ι ℂ) :
        Set (Matrix ι ι ℂ)) =
        {A | A * star A = 1 ∧ A.det = 1} := by
    ext A
    change A ∈ Matrix.specialUnitaryGroup ι ℂ ↔
      A * star A = 1 ∧ A.det = 1
    rw [Matrix.mem_specialUnitaryGroup_iff,
      Matrix.mem_unitaryGroup_iff]
  rw [hcarrier]
  apply hK.of_isClosed_subset hclosed
  intro A hA
  rw [Set.mem_matrix]
  intro i j
  rw [Metric.mem_closedBall, dist_zero_right]
  exact entry_norm_bound_of_unitary
    (Matrix.mem_unitaryGroup_iff.mpr hA.1) i j

noncomputable instance finiteSpecialUnitaryMeasurableSpace
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    MeasurableSpace (Matrix.specialUnitaryGroup ι ℂ) :=
  borel _

instance finiteSpecialUnitaryBorelSpace
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    BorelSpace (Matrix.specialUnitaryGroup ι ℂ) :=
  ⟨rfl⟩

/-- Finite special-unitary matrix groups inherit second countability from
their finite-dimensional complex matrix ambient space. -/
noncomputable instance finiteSpecialUnitarySecondCountableTopology
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    SecondCountableTopology (Matrix.specialUnitaryGroup ι ℂ) := by
  letI : Finite ι := Fintype.finite inferInstance
  letI : Countable ι := Finite.to_countable
  letI : SecondCountableTopology (Matrix ι ι ℂ) := by
    change SecondCountableTopology (ι → ι → ℂ)
    infer_instance
  exact Topology.IsInducing.subtypeVal.secondCountableTopology

/-- Haar measure normalized on the entire finite special unitary group. -/
def finiteSpecialUnitaryHaar
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Measure (Matrix.specialUnitaryGroup ι ℂ) :=
  haarMeasure
    (⟨⟨Set.univ, isCompact_univ⟩, by simp⟩ :
      PositiveCompacts (Matrix.specialUnitaryGroup ι ℂ))

/-- The normalized finite-special-unitary Haar measure is a probability
measure. -/
theorem finiteSpecialUnitaryHaar_apply_univ
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    finiteSpecialUnitaryHaar ι Set.univ = 1 := by
  exact haarMeasure_self

/-- Normalized Haar measure on a finite special unitary group is a
probability measure. -/
noncomputable instance finiteSpecialUnitaryHaarIsProbabilityMeasure
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    IsProbabilityMeasure (finiteSpecialUnitaryHaar ι) where
  measure_univ := finiteSpecialUnitaryHaar_apply_univ ι

/-- Left multiplication preserves every normalized finite-special-unitary
Haar integral. -/
theorem integral_finiteSpecialUnitaryHaar_mul_left
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : Matrix.specialUnitaryGroup ι ℂ → ℝ)
    (V : Matrix.specialUnitaryGroup ι ℂ) :
    (∫ U, f (V * U) ∂finiteSpecialUnitaryHaar ι) =
      ∫ U, f U ∂finiteSpecialUnitaryHaar ι := by
  unfold finiteSpecialUnitaryHaar
  exact integral_mul_left_eq_self f V

end

end GaloisForLFunctions.HTGeometry
