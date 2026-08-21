import GaloisForLFunctions.RHTower.CCMActualHeadMatchedPhaseDiskCofinalGaugeNoGo
import GaloisForLFunctions.HilbertMetric.GaussianJetPositivity
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Scratch: trace-free CCM phase disks as one coherent Fock packet
-/

open Complex MeasureTheory Set
open scoped BigOperators ComplexConjugate RealInnerProductSpace

noncomputable section
namespace RHTower

abbrev CCMActualHeadMatchedPhaseBlochSpace := EuclideanSpace ℝ (Fin 2)

/-- Trace-free Bloch coordinate of the matched phase Gram matrix. -/
def ccmActualHeadMatchedPhaseBlochFeature (n : ℕ) (xi : ℝ) :
    CCMActualHeadMatchedPhaseBlochSpace :=
  !₂[ccmActualHeadMatchedCosinePhaseProfile n xi - criticalMellinAtomWeight n,
    ccmActualHeadMatchedSinePhaseProfile n xi]

@[simp] theorem ccmActualHeadMatchedPhaseBlochFeature_apply_zero (n : ℕ) (xi : ℝ) :
    ccmActualHeadMatchedPhaseBlochFeature n xi 0 =
      ccmActualHeadMatchedCosinePhaseProfile n xi - criticalMellinAtomWeight n := rfl

@[simp] theorem ccmActualHeadMatchedPhaseBlochFeature_apply_one (n : ℕ) (xi : ℝ) :
    ccmActualHeadMatchedPhaseBlochFeature n xi 1 =
      ccmActualHeadMatchedSinePhaseProfile n xi := rfl

theorem ccmActualHeadMatchedPhaseBlochFeature_norm_sq_le (n : ℕ) (xi : ℝ) :
    ‖ccmActualHeadMatchedPhaseBlochFeature n xi‖ ^ 2 ≤
      criticalMellinAtomWeight n ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  simpa [Real.norm_eq_abs, sq_abs] using
    ccmActualHeadMatchedPhaseProfile_mem_weightDisk n xi

/-- Fixed tomography anchors plus an arbitrary finite packet of arithmetic atoms. -/
inductive CCMActualHeadMatchedPhaseFockIndex (ι : Type*)
  | cosineAnchor
  | sineAnchor
  | atom (i : ι)
  deriving DecidableEq, Fintype

namespace CCMActualHeadMatchedPhaseFockIndex

def feature {ι : Type*} (n : ι → ℕ) (xi : ℝ) :
    CCMActualHeadMatchedPhaseFockIndex ι → CCMActualHeadMatchedPhaseBlochSpace
  | cosineAnchor => !₂[1, 0]
  | sineAnchor => !₂[0, 1]
  | atom i => ccmActualHeadMatchedPhaseBlochFeature (n i) xi

end CCMActualHeadMatchedPhaseFockIndex

/-- One coherent exponential-inner-product packet containing all arithmetic Bloch vectors and
both fixed coordinate anchors. -/
def ccmActualHeadMatchedPhaseFockMatrix {ι : Type*}
    (n : ι → ℕ) (xi : ℝ) :
    Matrix (CCMActualHeadMatchedPhaseFockIndex ι)
      (CCMActualHeadMatchedPhaseFockIndex ι) ℝ :=
  GaloisForLFunctions.HilbertMetric.hilbertExponentialInnerMatrix
    (CCMActualHeadMatchedPhaseFockIndex.feature n xi) (1 / 2)

theorem ccmActualHeadMatchedPhaseFockMatrix_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ι → ℕ) (xi : ℝ) :
    (ccmActualHeadMatchedPhaseFockMatrix n xi).PosSemidef := by
  exact GaloisForLFunctions.HilbertMetric.hilbertExponentialInnerMatrix_posSemidef
    (CCMActualHeadMatchedPhaseFockIndex.feature n xi) (1 / 2) (by norm_num)

theorem ccmActualHeadMatchedPhaseFockMatrix_atom_cosineAnchor
    {ι : Type*} (n : ι → ℕ) (xi : ℝ) (i : ι) :
    ccmActualHeadMatchedPhaseFockMatrix n xi
        (.atom i) (.cosineAnchor) =
      Real.exp (ccmActualHeadMatchedCosinePhaseProfile (n i) xi -
        criticalMellinAtomWeight (n i)) := by
  simp [ccmActualHeadMatchedPhaseFockMatrix,
    GaloisForLFunctions.HilbertMetric.hilbertExponentialInnerMatrix,
    CCMActualHeadMatchedPhaseFockIndex.feature, PiLp.inner_apply, Fin.sum_univ_two]

theorem ccmActualHeadMatchedPhaseFockMatrix_atom_sineAnchor
    {ι : Type*} (n : ι → ℕ) (xi : ℝ) (i : ι) :
    ccmActualHeadMatchedPhaseFockMatrix n xi
        (.atom i) (.sineAnchor) =
      Real.exp (ccmActualHeadMatchedSinePhaseProfile (n i) xi) := by
  simp [ccmActualHeadMatchedPhaseFockMatrix,
    GaloisForLFunctions.HilbertMetric.hilbertExponentialInnerMatrix,
    CCMActualHeadMatchedPhaseFockIndex.feature, PiLp.inner_apply, Fin.sum_univ_two]

theorem log_ccmActualHeadMatchedPhaseFockMatrix_atom_cosineAnchor
    {ι : Type*} (n : ι → ℕ) (xi : ℝ) (i : ι) :
    Real.log (ccmActualHeadMatchedPhaseFockMatrix n xi
        (.atom i) (.cosineAnchor)) =
      ccmActualHeadMatchedCosinePhaseProfile (n i) xi -
        criticalMellinAtomWeight (n i) := by
  rw [ccmActualHeadMatchedPhaseFockMatrix_atom_cosineAnchor, Real.log_exp]

theorem log_ccmActualHeadMatchedPhaseFockMatrix_atom_sineAnchor
    {ι : Type*} (n : ι → ℕ) (xi : ℝ) (i : ι) :
    Real.log (ccmActualHeadMatchedPhaseFockMatrix n xi
        (.atom i) (.sineAnchor)) =
      ccmActualHeadMatchedSinePhaseProfile (n i) xi := by
  rw [ccmActualHeadMatchedPhaseFockMatrix_atom_sineAnchor, Real.log_exp]

/-- Nonlinear tomography reporter of the intact oriented CCM phase symbol from two entries of the
single positive Fock packet. -/
def ccmActualHeadMatchedPhaseFockTomographyReporter {ι : Type*}
    (n : ι → ℕ) (xi : ℝ) (i : ι) : ℝ :=
  let theta := 2 * Real.pi * Real.log (n i) * xi
  criticalMellinAtomWeight (n i) * Real.cos theta +
    Real.cos theta * Real.log (ccmActualHeadMatchedPhaseFockMatrix n xi
      (.atom i) (.cosineAnchor)) +
    Real.sin theta * Real.log (ccmActualHeadMatchedPhaseFockMatrix n xi
      (.atom i) (.sineAnchor))

theorem ccmActualHeadMatchedPhaseFockTomographyReporter_eq_orientedPhaseSymbol_re
    {ι : Type*} (n : ι → ℕ) (xi : ℝ) (i : ι) :
    ccmActualHeadMatchedPhaseFockTomographyReporter n xi i =
      (ccmActualHeadMatchedOrientedPhaseSymbol (n i) xi).re := by
  rw [ccmActualHeadMatchedOrientedPhaseSymbol_re,
    ccmActualHeadMatchedPhaseFockTomographyReporter,
    log_ccmActualHeadMatchedPhaseFockMatrix_atom_cosineAnchor,
    log_ccmActualHeadMatchedPhaseFockMatrix_atom_sineAnchor]
  ring

theorem ccmActualHeadMatchedPhaseFockMatrix_atom_atom
    {ι : Type*} (n : ι → ℕ) (xi : ℝ) (i : ι) :
    ccmActualHeadMatchedPhaseFockMatrix n xi (.atom i) (.atom i) =
      Real.exp (‖ccmActualHeadMatchedPhaseBlochFeature (n i) xi‖ ^ 2) := by
  simp [ccmActualHeadMatchedPhaseFockMatrix,
    GaloisForLFunctions.HilbertMetric.hilbertExponentialInnerMatrix,
    CCMActualHeadMatchedPhaseFockIndex.feature]

theorem ccmActualHeadMatchedPhaseFockMatrix_atom_atom_le_weightDisk
    {ι : Type*} (n : ι → ℕ) (xi : ℝ) (i : ι) :
    ccmActualHeadMatchedPhaseFockMatrix n xi (.atom i) (.atom i) ≤
      Real.exp (criticalMellinAtomWeight (n i) ^ 2) := by
  rw [ccmActualHeadMatchedPhaseFockMatrix_atom_atom]
  exact Real.exp_le_exp.mpr
    (ccmActualHeadMatchedPhaseBlochFeature_norm_sq_le (n i) xi)

end RHTower
