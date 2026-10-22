import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedPhaseProjectiveGaugeChiralNodalLine

/-!
# Actual matched CCM source as an exact chiral determinant crossing

A fixed Hermitian shear of the two anchor coordinates evaluates on the canonical atomwise null
line as a positive gauge square times the signed matched source. The determinant of the sheared
Hermitian compression is exactly linear in crossing time with the opposite coefficient. Thus the
source orientation is literal determinant-line spectral-flow orientation.
-/

open Complex Matrix
open scoped BigOperators Matrix ComplexConjugate InnerProductSpace

noncomputable section
namespace RHTower

/-- Fixed Hermitian shear coupling the weight and source anchor coordinates. -/
def ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceShear :
    Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 1, 0; 1, 0, 0; 0, 0, 0]

theorem ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceShear_isHermitian :
    ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceShear.IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceShear]

/-- Krein crossing form of the fixed source shear on the canonical nodal line. -/
def ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingForm
    (xi : ℝ) (n : ℕ) : ℝ :=
  (star (ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalVector xi n) ⬝ᵥ
    (ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceShear *ᵥ
      ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalVector xi n)).re

theorem ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingForm_eq
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingForm xi n =
      2 * ccmActualHeadMatchedPhaseProjectiveGauge n ^ (2 : ℕ) *
        (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re := by
  simp [ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingForm,
    ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceShear,
    ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalVector,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- Affine Hermitian family crossing the chiral nodal wall in the fixed source-shear direction. -/
def ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily
    (xi : ℝ) (n : ℕ) (t : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ccmActualHeadMatchedPhaseProjectiveGaugeAtomHermitianOrientationCompression xi n +
    (t : ℂ) • ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceShear

theorem ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily_isHermitian
    (xi : ℝ) (n : ℕ) (t : ℝ) :
    (ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily xi n t).IsHermitian := by
  apply Matrix.IsHermitian.add
  · exact
      ccmActualHeadMatchedPhaseProjectiveGaugeAtomHermitianOrientationCompression_isHermitian
        xi n
  · apply Matrix.IsHermitian.smul
    · exact ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceShear_isHermitian
    · rw [isSelfAdjoint_iff]
      simp

theorem det_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily
    (xi : ℝ) (n : ℕ) (t : ℝ) :
    (ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily xi n t).det =
      (-(2 * t * ccmActualHeadMatchedPhaseProjectiveGauge n ^ (2 : ℕ) *
        (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re) : ℝ) := by
  simp [ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily,
    ccmActualHeadMatchedPhaseProjectiveGaugeAtomHermitianOrientationCompression,
    ccmActualHeadMatchedPhaseProjectiveGaugeAtomChiralCompression,
    ccmActualHeadMatchedPhaseProjectiveGaugeAtomFrameIndex,
    ccmActualHeadMatchedPhaseProjectiveGaugeChiralKernel,
    ccmActualHeadMatchedPhaseProjectiveGaugeWeightFeature,
    ccmActualHeadMatchedPhaseProjectiveGaugeSourceFeature,
    ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceShear,
    Matrix.det_fin_three]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem hasDerivAt_det_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily
    (xi : ℝ) (n : ℕ) :
    HasDerivAt
      (fun t : ℝ =>
        (ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily xi n t).det.re)
      (-2 * ccmActualHeadMatchedPhaseProjectiveGauge n ^ (2 : ℕ) *
        (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re) 0 := by
  have hfun :
      (fun t : ℝ =>
        (ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily xi n t).det.re) =
      fun t : ℝ =>
        (-2 * ccmActualHeadMatchedPhaseProjectiveGauge n ^ (2 : ℕ) *
          (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re) * t := by
    funext t
    rw [det_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily]
    norm_cast
    norm_num
    ring
  rw [hfun]
  have hbase := (hasDerivAt_id (0 : ℝ)).const_mul
    (-2 * ccmActualHeadMatchedPhaseProjectiveGauge n ^ (2 : ℕ) *
      (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re)
  have hbase' :
      HasDerivAt
        (fun t : ℝ =>
          (-2 * ccmActualHeadMatchedPhaseProjectiveGauge n ^ (2 : ℕ) *
            (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re) * id t)
        (-2 * ccmActualHeadMatchedPhaseProjectiveGauge n ^ (2 : ℕ) *
          (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re) 0 := by
    exact hbase.congr_deriv (by ring)
  refine hbase'.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun t => by
    dsimp [id]

theorem det_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily_one
    (xi : ℝ) (n : ℕ) :
    (ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily xi n 1).det =
      -ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingForm xi n := by
  rw [det_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily,
    ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingForm_eq]
  push_cast
  ring

theorem ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingForm_pos_iff
    (xi : ℝ) (n : ℕ) (hweight : criticalMellinAtomWeight n ≠ 0) :
    0 < ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingForm xi n ↔
      0 < (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re := by
  rw [ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingForm_eq]
  have hgauge :=
    ccmActualHeadMatchedPhaseProjectiveGauge_ne_zero_of_criticalMellinAtomWeight_ne_zero
      n hweight
  have hsquare : 0 < ccmActualHeadMatchedPhaseProjectiveGauge n ^ (2 : ℕ) := sq_pos_of_ne_zero hgauge
  constructor <;> intro h <;> nlinarith

theorem det_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily_one_neg_iff
    (xi : ℝ) (n : ℕ) (hweight : criticalMellinAtomWeight n ≠ 0) :
    (ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily xi n 1).det.re < 0 ↔
      0 < (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re := by
  rw [det_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily_one]
  simp only [Complex.neg_re, neg_lt_zero]
  exact ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingForm_pos_iff
    xi n hweight

/-- Total normalized determinant-crossing reporter. -/
def ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingReporter
    (xi : ℝ) (n : ℕ) : ℝ :=
  if criticalMellinAtomWeight n = 0 then 0
  else ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingForm xi n /
    (2 * ccmActualHeadMatchedPhaseProjectiveGauge n ^ (2 : ℕ))

theorem ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingReporter_eq
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingReporter xi n =
      (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re := by
  unfold ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingReporter
  split_ifs with hweight
  · have hreporter := ccmActualHeadMatchedPhaseProjectiveGaugeReporter_eq xi n
    rw [ccmActualHeadMatchedPhaseProjectiveGaugeReporter, if_pos hweight] at hreporter
    exact hreporter
  · rw [ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingForm_eq]
    have hgauge :=
      ccmActualHeadMatchedPhaseProjectiveGauge_ne_zero_of_criticalMellinAtomWeight_ne_zero
        n hweight
    field_simp

def ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFiniteReporter
    (F : Finset ℕ) (xi : ℝ) : ℝ :=
  ∑ n ∈ F, ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingReporter xi n

theorem ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFiniteReporter_eq
    (F : Finset ℕ) (xi : ℝ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFiniteReporter F xi =
      (ccmActualHeadMatchedOrientedPhaseFiniteSymbol F xi).re := by
  unfold ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFiniteReporter
    ccmActualHeadMatchedOrientedPhaseFiniteSymbol
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingReporter_eq xi n

theorem ccmActualHeadMatchedPrimePolarFiniteBlock_eq_nodalSourceCrossing
    (F : Finset ℕ) (f : SoninL2) :
    ccmActualHeadMatchedPrimePolarFiniteBlock F f =
      -2 * ∫ xi : ℝ,
        ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFiniteReporter F xi *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ) := by
  rw [ccmActualHeadMatchedPrimePolarFiniteBlock_eq_orientedPhaseFiniteSymbol]
  congr 2
  funext xi
  rw [ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFiniteReporter_eq]

end RHTower
