import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Complex.Basic

/-!
# The Haar probability measure of a compact abelian group

A compact Hausdorff abelian topological group carries a translation-invariant Borel probability
measure: normalize Haar measure so that the whole group has mass one.  This file records that
measure together with the translation and reflection invariance of its integral, which is all the
harmonic analysis on the phase carrier will need from measure theory.
-/

open MeasureTheory TopologicalSpace

namespace GaloisForLFunctions

namespace CompactAbelian

noncomputable section

variable (G : Type*) [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- The Haar probability measure of a compact abelian group. -/
def haarProb : Measure G := Measure.addHaarMeasure ⊤

instance : Measure.IsAddHaarMeasure (haarProb G) := by
  unfold haarProb
  infer_instance

instance : IsProbabilityMeasure (haarProb G) := by
  constructor
  have h := Measure.addHaarMeasure_self (G := G) (K₀ := ⊤)
  simpa [haarProb] using h

instance : (haarProb G).IsAddLeftInvariant := by
  unfold haarProb
  infer_instance

instance : (haarProb G).IsAddRightInvariant := by
  unfold haarProb
  infer_instance

variable {G}

omit [T2Space G] in
theorem integral_add_right (F : G → ℂ) (a : G) :
    ∫ x, F (x + a) ∂(haarProb G) = ∫ x, F x ∂(haarProb G) :=
  integral_add_right_eq_self F a

omit [T2Space G] in
theorem integral_add_left (F : G → ℂ) (a : G) :
    ∫ x, F (a + x) ∂(haarProb G) = ∫ x, F x ∂(haarProb G) := by
  simpa [add_comm] using integral_add_right F a

omit [T2Space G] in
theorem integral_sub_left (F : G → ℂ) (a : G) :
    ∫ x, F (a - x) ∂(haarProb G) = ∫ x, F x ∂(haarProb G) := by
  have hneg : ∫ x, F (a + -x) ∂(haarProb G) = ∫ x, F (a + x) ∂(haarProb G) :=
    integral_neg_eq_self (fun x => F (a + x)) (μ := haarProb G)
  simpa [sub_eq_add_neg, integral_add_left] using hneg

end

end CompactAbelian

end GaloisForLFunctions
