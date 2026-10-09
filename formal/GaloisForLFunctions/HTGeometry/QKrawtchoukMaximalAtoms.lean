import GaloisForLFunctions.HTGeometry.QKrawtchoukEdgeIndeterminacy
import GaloisForLFunctions.HTGeometry.ChristoffelLimitFormula

/-!
# Attaining the inverse-q Hermite maximal atom

Proposition 5.1 of arXiv:2609.24149 applies to the concrete edge moment
sequence: at every prescribed real point there is a probability realization
whose atom is the reciprocal orthogonal-polynomial kernel sum. Every other
realization has an atom no larger. The maximizing measure is selected by the
projective denominator label of the constructed Nevanlinna family.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace HTGeometry

/-- The extremal probability measure selected by a prescribed atom location. -/
def inverseQHermiteAtomMeasure (t u x : ℝ) : ProbabilityMeasure ℝ :=
  (inverseQHermiteNevanlinnaFamily t u).leaf
    ((inverseQHermiteNevanlinnaFamily t u).matrix.projectiveLabel x)

theorem inverseQHermiteAtomMeasure_moments (t u x : ℝ) :
    GaloisForLFunctions.HTGeometry.HasHamburgerMoments (inverseQHermiteMoment t u)
      (inverseQHermiteAtomMeasure t u x : Measure ℝ) :=
  (inverseQHermiteNevanlinnaFamily t u).leaf_moments _

/-- The selected leaf attains the positive Christoffel atom bound. -/
theorem inverseQHermiteAtomMeasure_atom (t u x : ℝ) :
    (inverseQHermiteAtomMeasure t u x : Measure ℝ) {x} =
      ENNReal.ofReal (christoffelLimit (inverseQHermiteMoment t u) x) := by
  let h := inverseQHermiteMoment_positive t u
  let hb := inverseQHermiteMoment_boundedKernel t u 0
  let h0 := inverseQHermiteMoment_zero t u
  change (nevLeaf h hb h0 ((nevMatrixDataInf h hb).projectiveLabel x) : Measure ℝ) {x} = _
  by_cases hx : (nevMatrixDataInf h hb).B x = 0
  · rw [GaloisForLFunctions.HTGeometry.ClassicalNevanlinnaMatrixData.projectiveLabel,
      if_pos hx]
    exact nevLeaf_infinity_atoms h hb h0 hx
  · rw [GaloisForLFunctions.HTGeometry.ClassicalNevanlinnaMatrixData.projectiveLabel,
      if_neg hx]
    apply nevLeaf_atoms h hb h0
    change (nevMatrixDataInf h hb).B x *
      ((nevMatrixDataInf h hb).D x / (nevMatrixDataInf h hb).B x) -
        (nevMatrixDataInf h hb).D x = 0
    field_simp
    ring

theorem inverseQHermiteAtomMeasure_atom_real (t u x : ℝ) :
    (inverseQHermiteAtomMeasure t u x : Measure ℝ).real {x} =
      christoffelLimit (inverseQHermiteMoment t u) x := by
  rw [Measure.real, inverseQHermiteAtomMeasure_atom,
    ENNReal.toReal_ofReal (inverseQHermiteMoment_christoffel_pos t u x).le]

/-- The paper's infinite reciprocal-square formula is valid for the concrete
edge recurrence; summability follows from the proved kernel bound. -/
theorem inverseQHermiteMoment_christoffel_formula (t u x : ℝ) :
    christoffelLimit (inverseQHermiteMoment t u) x =
      (∑' k, ((monicOrtho (inverseQHermiteMoment t u) k).eval x) ^ 2 /
        monicOrthoNormSq (inverseQHermiteMoment t u) k)⁻¹ := by
  apply christoffelLimit_eq_inv_tsum (inverseQHermiteMoment_positive t u) x
  have hs := summable_of_boundedKernel (inverseQHermiteMoment_positive t u)
    (inverseQHermiteMoment_boundedKernel t u (x : ℂ))
  simpa only [normSq_monicOrthoC_ofReal] using hs

/-- An attained maximum over every probability measure with these moments,
including non-extremal realizations. All moment and bounded-kernel inputs
are discharged for the inverse-q Hermite edge. -/
theorem inverseQHermite_maximal_atom (t u x : ℝ) :
    (inverseQHermiteAtomMeasure t u x : Measure ℝ).real {x} =
      (∑' k, ((monicOrtho (inverseQHermiteMoment t u) k).eval x) ^ 2 /
        monicOrthoNormSq (inverseQHermiteMoment t u) k)⁻¹ ∧
      ∀ ν : ProbabilityMeasure ℝ,
        GaloisForLFunctions.HTGeometry.HasHamburgerMoments (inverseQHermiteMoment t u)
          (ν : Measure ℝ) →
        (ν : Measure ℝ).real {x} ≤
          (inverseQHermiteAtomMeasure t u x : Measure ℝ).real {x} := by
  rw [inverseQHermiteAtomMeasure_atom_real]
  exact ⟨inverseQHermiteMoment_christoffel_formula t u x, fun ν hν =>
    measureReal_singleton_le_christoffelLimit_of_hasMoments
      (inverseQHermiteMoment_positive t u) hν x⟩

end HTGeometry
