import GaloisForLFunctions.RHTower.CCMActualHeadMatchedPhaseDiskCofinalGaugeNoGo
import GaloisForLFunctions.HilbertMetric.GaussianJetPositivity
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Trace-free coherent-Fock tomography of matched CCM phase disks

Primewise Schur completion fails globally because every local phase disk contributes a
nonsummable positive scalar trace.  This module removes that trace before positivity.  The two
remaining Bloch coordinates are inserted, together with two fixed tomography anchors, into one
HilbertMetric exponential-inner-product Gram packet.

Every finite arithmetic packet is positive semidefinite by the corpus's Gaussian-Fock theorem.
Taking real logarithms of the atom--anchor entries recovers the matched cosine and sine channels
exactly.  The literal oriented CCM symbol, including its critical Mellin coefficient, is therefore
a nonlinear reporter of one positive cross-prime kernel.  Cross-atom entries are forced by the
anchor entries through an exact rank-two logarithmic covariance identity; no target-fitted
off-diagonal completion is introduced.

Finally, every finite actual matched prime--polar block is identified with the spectral integral
of this tomography reporter.  This is an unconditional source-faithful carrier, not an RH proof:
the remaining problem is a nonlocal cofinal limit or compactness principle for the coherent
kernel that preserves the logarithmic reporter.
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
    ‖ccmActualHeadMatchedPhaseBlochFeature n xi‖ ^ (2 : ℕ) ≤
      criticalMellinAtomWeight n ^ (2 : ℕ) := by
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
      Real.exp (‖ccmActualHeadMatchedPhaseBlochFeature (n i) xi‖ ^ (2 : ℕ)) := by
  simp [ccmActualHeadMatchedPhaseFockMatrix,
    GaloisForLFunctions.HilbertMetric.hilbertExponentialInnerMatrix,
    CCMActualHeadMatchedPhaseFockIndex.feature]

theorem ccmActualHeadMatchedPhaseFockMatrix_atom_atom_cross
    {ι : Type*} (n : ι → ℕ) (xi : ℝ) (i j : ι) :
    ccmActualHeadMatchedPhaseFockMatrix n xi (.atom i) (.atom j) =
      Real.exp (inner ℝ
        (ccmActualHeadMatchedPhaseBlochFeature (n i) xi)
        (ccmActualHeadMatchedPhaseBlochFeature (n j) xi)) := by
  simp [ccmActualHeadMatchedPhaseFockMatrix,
    GaloisForLFunctions.HilbertMetric.hilbertExponentialInnerMatrix,
    CCMActualHeadMatchedPhaseFockIndex.feature]

/-- Cross-prime logarithmic covariance is forced by the two anchor reporters; no free
off-diagonal completion is inserted. -/
theorem log_ccmActualHeadMatchedPhaseFockMatrix_atom_atom_eq_anchor_products
    {ι : Type*} (n : ι → ℕ) (xi : ℝ) (i j : ι) :
    Real.log (ccmActualHeadMatchedPhaseFockMatrix n xi (.atom i) (.atom j)) =
      Real.log (ccmActualHeadMatchedPhaseFockMatrix n xi
          (.atom i) (.cosineAnchor)) *
        Real.log (ccmActualHeadMatchedPhaseFockMatrix n xi
          (.atom j) (.cosineAnchor)) +
      Real.log (ccmActualHeadMatchedPhaseFockMatrix n xi
          (.atom i) (.sineAnchor)) *
        Real.log (ccmActualHeadMatchedPhaseFockMatrix n xi
          (.atom j) (.sineAnchor)) := by
  rw [ccmActualHeadMatchedPhaseFockMatrix_atom_atom_cross, Real.log_exp,
    log_ccmActualHeadMatchedPhaseFockMatrix_atom_cosineAnchor,
    log_ccmActualHeadMatchedPhaseFockMatrix_atom_cosineAnchor,
    log_ccmActualHeadMatchedPhaseFockMatrix_atom_sineAnchor,
    log_ccmActualHeadMatchedPhaseFockMatrix_atom_sineAnchor]
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp only [ccmActualHeadMatchedPhaseBlochFeature_apply_zero,
    ccmActualHeadMatchedPhaseBlochFeature_apply_one, RCLike.inner_apply,
    starRingEnd_apply, star_trivial]
  ring

theorem ccmActualHeadMatchedPhaseFockMatrix_atom_atom_le_weightDisk
    {ι : Type*} (n : ι → ℕ) (xi : ℝ) (i : ι) :
    ccmActualHeadMatchedPhaseFockMatrix n xi (.atom i) (.atom i) ≤
      Real.exp (criticalMellinAtomWeight (n i) ^ (2 : ℕ)) := by
  rw [ccmActualHeadMatchedPhaseFockMatrix_atom_atom]
  exact Real.exp_le_exp.mpr
    (ccmActualHeadMatchedPhaseBlochFeature_norm_sq_le (n i) xi)

/-- Finite matched source reporter read from one coherent atom--anchor packet. -/
def ccmActualHeadMatchedPhaseFiniteFockTomographyReporter
    (F : Finset ℕ) (xi : ℝ) : ℝ :=
  ∑ i : ↥F,
    ccmActualHeadMatchedPhaseFockTomographyReporter
      (fun j : ↥F => (j : ℕ)) xi i

theorem ccmActualHeadMatchedPhaseFiniteFockTomographyReporter_eq_orientedFiniteSymbol_re
    (F : Finset ℕ) (xi : ℝ) :
    ccmActualHeadMatchedPhaseFiniteFockTomographyReporter F xi =
      (ccmActualHeadMatchedOrientedPhaseFiniteSymbol F xi).re := by
  unfold ccmActualHeadMatchedPhaseFiniteFockTomographyReporter
    ccmActualHeadMatchedOrientedPhaseFiniteSymbol
  rw [Complex.re_sum]
  rw [Finset.sum_subtype F (fun i => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro i hi
  exact ccmActualHeadMatchedPhaseFockTomographyReporter_eq_orientedPhaseSymbol_re
    (fun j : ↥F => (j : ℕ)) xi i

/-- Every finite actual matched prime--polar block is an exact nonlinear reporter of one
positive-semidefinite coherent Fock matrix. -/
theorem ccmActualHeadMatchedPrimePolarFiniteBlock_eq_phaseFockTomography
    (F : Finset ℕ) (f : SoninL2) :
    ccmActualHeadMatchedPrimePolarFiniteBlock F f =
      -2 * ∫ xi : ℝ,
        ccmActualHeadMatchedPhaseFiniteFockTomographyReporter F xi *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ) := by
  rw [ccmActualHeadMatchedPrimePolarFiniteBlock_eq_orientedPhaseFiniteSymbol]
  congr 2
  funext xi
  rw [ccmActualHeadMatchedPhaseFiniteFockTomographyReporter_eq_orientedFiniteSymbol_re]

end RHTower
