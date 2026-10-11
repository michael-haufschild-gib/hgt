import GaloisForLFunctions.RHTower.WeilLogShiftObservableLaw
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-! The normalized index and correction define one Euclidean probability law. -/

open MeasureTheory
open scoped BigOperators

noncomputable section
namespace RHTower

def finiteWeilCanonicalFluctuationPoint (r k : ℕ) (i : Fin (r + 1)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![
    (((i : ℕ) : ℝ) - finiteWeilCanonicalEdgeIndexMean r k) / Real.sqrt ((r + 1 : ℕ) : ℝ),
    (((r + 1 : ℕ) : ℝ) *
      (finiteWeilCanonicalEdgeLogCorrection r k i - finiteWeilCanonicalLogTransportCorrection r k)) /
      Real.sqrt ((r + 1 : ℕ) : ℝ)]

theorem finiteWeilCanonicalFluctuationPoint_inner (r k : ℕ) (i : Fin (r + 1))
    (v : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (finiteWeilCanonicalFluctuationPoint r k i) v =
      (v 0 * (((i : ℕ) : ℝ) - finiteWeilCanonicalEdgeIndexMean r k) +
        v 1 * (((r + 1 : ℕ) : ℝ) *
          (finiteWeilCanonicalEdgeLogCorrection r k i - finiteWeilCanonicalLogTransportCorrection r k))) /
      Real.sqrt ((r + 1 : ℕ) : ℝ) := by
  simp only [finiteWeilCanonicalFluctuationPoint, PiLp.inner_apply, Fin.sum_univ_two,
    Real.inner_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

def finiteWeilCanonicalJointProbabilityLaw (r k : ℕ) : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)) :=
  finiteWeilCanonicalObservableLaw r k (finiteWeilCanonicalFluctuationPoint r k)

theorem finiteWeilCanonicalJointProbabilityLaw_charFun (r k : ℕ) (v : EuclideanSpace ℝ (Fin 2)) :
    charFun (finiteWeilCanonicalJointProbabilityLaw r k : Measure (EuclideanSpace ℝ (Fin 2))) v =
      finiteWeilCanonicalJointCharacteristic r k (v 0) (v 1) := by
  rw [finiteWeilCanonicalJointProbabilityLaw, charFun_apply,
    finiteWeilCanonicalObservableLaw_integral_complex]
  simp only [finiteWeilCanonicalFluctuationPoint_inner, finiteWeilCanonicalJointCharacteristic, finiteWeilPhase]

end RHTower
