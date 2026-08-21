import GaloisForLFunctions.RHTower.CCMActualHeadMatchedPhaseProjectiveGaugeChiralOperator
import GaloisForLFunctions.HTGeometry.SourceOrderedPairComplexStructure

/-!
# Actual matched CCM source as a chiral nodal line

The fixed anchor compression of the actual matched chiral Schatten operator is exactly the
ordered-source complex structure. Adjoining one arithmetic atom produces a Hermitian `3 × 3`
compression with a canonically normalized zero eigenvector. Its full kernel is one projective
line, and its first two coordinates retain the signed matched source. Consequently every finite
actual matched prime--polar block is a spectral integral of projective coordinates of these
operator-derived nodal lines.
-/

open Complex Matrix
open scoped Matrix ComplexConjugate InnerProductSpace

noncomputable section
namespace RHTower

def ccmActualHeadMatchedPhaseProjectiveGaugeAnchorIndex :
    Fin 2 → CCMActualHeadMatchedPhaseProjectiveGaugeIndex :=
  ![.weightAnchor, .sourceAnchor]

def ccmActualHeadMatchedPhaseProjectiveGaugeChiralAnchorCompression (xi : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => ccmActualHeadMatchedPhaseProjectiveGaugeChiralKernel xi
    (ccmActualHeadMatchedPhaseProjectiveGaugeAnchorIndex i)
    (ccmActualHeadMatchedPhaseProjectiveGaugeAnchorIndex j)

theorem ccmActualHeadMatchedPhaseProjectiveGaugeChiralAnchorCompression_eq_sourceOrderedPair
    (xi : ℝ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeChiralAnchorCompression xi =
      GaloisForLFunctions.HTGeometry.sourceOrderedPairComplexStructure := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ccmActualHeadMatchedPhaseProjectiveGaugeChiralAnchorCompression,
      ccmActualHeadMatchedPhaseProjectiveGaugeAnchorIndex,
      ccmActualHeadMatchedPhaseProjectiveGaugeChiralKernel,
      ccmActualHeadMatchedPhaseProjectiveGaugeWeightFeature,
      ccmActualHeadMatchedPhaseProjectiveGaugeSourceFeature,
      GaloisForLFunctions.HTGeometry.sourceOrderedPairComplexStructure,
      GaloisForLFunctions.HTGeometry.recordPolarityMatrix,
      GaloisForLFunctions.HTGeometry.pairRecordMatrix,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem ccmActualHeadMatchedPhaseProjectiveGaugeChiralAnchorCompression_sq
    (xi : ℝ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeChiralAnchorCompression xi *
        ccmActualHeadMatchedPhaseProjectiveGaugeChiralAnchorCompression xi = -1 := by
  rw [ccmActualHeadMatchedPhaseProjectiveGaugeChiralAnchorCompression_eq_sourceOrderedPair]
  exact GaloisForLFunctions.HTGeometry.sourceOrderedPairComplexStructure_sq

def ccmActualHeadMatchedPhaseProjectiveGaugeAtomFrameIndex (n : ℕ) :
    Fin 3 → CCMActualHeadMatchedPhaseProjectiveGaugeIndex :=
  ![.weightAnchor, .sourceAnchor, .atom n]

def ccmActualHeadMatchedPhaseProjectiveGaugeAtomChiralCompression
    (xi : ℝ) (n : ℕ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => ccmActualHeadMatchedPhaseProjectiveGaugeChiralKernel xi
    (ccmActualHeadMatchedPhaseProjectiveGaugeAtomFrameIndex n i)
    (ccmActualHeadMatchedPhaseProjectiveGaugeAtomFrameIndex n j)

def ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalVector
    (xi : ℝ) (n : ℕ) : Fin 3 → ℂ :=
  ![(ccmActualHeadMatchedPhaseProjectiveGauge n : ℂ),
    (ccmActualHeadMatchedPhaseProjectiveGauge n *
      (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re : ℝ),
    -1]

theorem ccmActualHeadMatchedPhaseProjectiveGaugeAtomChiralCompression_mulVec_nodal
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeAtomChiralCompression xi n *ᵥ
        ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalVector xi n = 0 := by
  funext i
  fin_cases i <;>
    simp [ccmActualHeadMatchedPhaseProjectiveGaugeAtomChiralCompression,
      ccmActualHeadMatchedPhaseProjectiveGaugeAtomFrameIndex,
      ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalVector,
      ccmActualHeadMatchedPhaseProjectiveGaugeChiralKernel,
      ccmActualHeadMatchedPhaseProjectiveGaugeWeightFeature,
      ccmActualHeadMatchedPhaseProjectiveGaugeSourceFeature,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem ccmActualHeadMatchedPhaseProjectiveGaugeAtomChiralCompression_eq_operatorMatrix
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeAtomChiralCompression xi n =
      fun i j => inner ℂ
        (lp.single 2
          (ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode
            (ccmActualHeadMatchedPhaseProjectiveGaugeAtomFrameIndex n i)) 1)
        ((ccmActualHeadMatchedPhaseProjectiveGaugeChiralOperator xi :
          CCMActualHeadMatchedPhaseProjectiveGaugeL2 →L[ℂ]
            CCMActualHeadMatchedPhaseProjectiveGaugeL2)
          (lp.single 2
            (ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode
              (ccmActualHeadMatchedPhaseProjectiveGaugeAtomFrameIndex n j)) 1)) := by
  ext i j
  exact (ccmActualHeadMatchedPhaseProjectiveGaugeChiralOperator_matrix xi _ _).symm

/-- Self-adjoint local orientation matrix obtained from the chiral compression. -/
def ccmActualHeadMatchedPhaseProjectiveGaugeAtomHermitianOrientationCompression
    (xi : ℝ) (n : ℕ) : Matrix (Fin 3) (Fin 3) ℂ :=
  I • ccmActualHeadMatchedPhaseProjectiveGaugeAtomChiralCompression xi n

theorem ccmActualHeadMatchedPhaseProjectiveGaugeAtomHermitianOrientationCompression_eq_operatorMatrix
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeAtomHermitianOrientationCompression xi n =
      fun i j => inner ℂ
        (lp.single 2
          (ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode
            (ccmActualHeadMatchedPhaseProjectiveGaugeAtomFrameIndex n i)) 1)
        ((ccmActualHeadMatchedPhaseProjectiveGaugeHermitianOrientationOperator xi :
          CCMActualHeadMatchedPhaseProjectiveGaugeL2 →L[ℂ]
            CCMActualHeadMatchedPhaseProjectiveGaugeL2)
          (lp.single 2
            (ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode
              (ccmActualHeadMatchedPhaseProjectiveGaugeAtomFrameIndex n j)) 1)) := by
  ext i j
  simp [ccmActualHeadMatchedPhaseProjectiveGaugeAtomHermitianOrientationCompression,
    ccmActualHeadMatchedPhaseProjectiveGaugeAtomChiralCompression,
    ccmActualHeadMatchedPhaseProjectiveGaugeHermitianOrientationOperator_matrix]

theorem ccmActualHeadMatchedPhaseProjectiveGaugeAtomHermitianOrientationCompression_isHermitian
    (xi : ℝ) (n : ℕ) :
    (ccmActualHeadMatchedPhaseProjectiveGaugeAtomHermitianOrientationCompression xi n).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ccmActualHeadMatchedPhaseProjectiveGaugeAtomHermitianOrientationCompression,
      ccmActualHeadMatchedPhaseProjectiveGaugeAtomChiralCompression,
      ccmActualHeadMatchedPhaseProjectiveGaugeAtomFrameIndex,
      ccmActualHeadMatchedPhaseProjectiveGaugeChiralKernel,
      ccmActualHeadMatchedPhaseProjectiveGaugeWeightFeature,
      ccmActualHeadMatchedPhaseProjectiveGaugeSourceFeature]
  all_goals ring

theorem ccmActualHeadMatchedPhaseProjectiveGaugeAtomHermitianOrientationCompression_mulVec_nodal
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeAtomHermitianOrientationCompression xi n *ᵥ
        ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalVector xi n = 0 := by
  rw [ccmActualHeadMatchedPhaseProjectiveGaugeAtomHermitianOrientationCompression,
    Matrix.smul_mulVec,
    ccmActualHeadMatchedPhaseProjectiveGaugeAtomChiralCompression_mulVec_nodal,
    smul_zero]

theorem ccmActualHeadMatchedPhaseProjectiveGaugeAtomChiralCompression_mulVec_eq_zero_iff
    (xi : ℝ) (n : ℕ) (z : Fin 3 → ℂ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeAtomChiralCompression xi n *ᵥ z = 0 ↔
      z = (-z 2) •
        ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalVector xi n := by
  constructor
  · intro hz
    have h0 := congrFun hz (0 : Fin 3)
    have h1 := congrFun hz (1 : Fin 3)
    simp [ccmActualHeadMatchedPhaseProjectiveGaugeAtomChiralCompression,
      ccmActualHeadMatchedPhaseProjectiveGaugeAtomFrameIndex,
      ccmActualHeadMatchedPhaseProjectiveGaugeChiralKernel,
      ccmActualHeadMatchedPhaseProjectiveGaugeWeightFeature,
      ccmActualHeadMatchedPhaseProjectiveGaugeSourceFeature,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1
    funext i
    fin_cases i
    · simp [ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalVector]
      linear_combination -h1
    · simp [ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalVector]
      linear_combination h0
    · simp [ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalVector]
  · intro hz
    have hmul := congrArg
      (fun w : Fin 3 → ℂ =>
        ccmActualHeadMatchedPhaseProjectiveGaugeAtomChiralCompression xi n *ᵥ w) hz
    rw [Matrix.mulVec_smul,
      ccmActualHeadMatchedPhaseProjectiveGaugeAtomChiralCompression_mulVec_nodal,
      smul_zero] at hmul
    exact hmul

theorem ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalVector_last
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalVector xi n 2 = -1 := by
  simp [ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalVector]

theorem ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalVector_source_incidence
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalVector xi n 1 =
      ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalVector xi n 0 *
        (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re := by
  simp [ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalVector]

theorem ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalVector_unique_normalized
    (xi : ℝ) (n : ℕ) (z : Fin 3 → ℂ)
    (hz : ccmActualHeadMatchedPhaseProjectiveGaugeAtomChiralCompression xi n *ᵥ z = 0)
    (hlast : z 2 = -1) :
    z = ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalVector xi n := by
  rw [ccmActualHeadMatchedPhaseProjectiveGaugeAtomChiralCompression_mulVec_eq_zero_iff]
    at hz
  rw [hlast] at hz
  simpa using hz

theorem ccmActualHeadMatchedPhaseProjectiveGauge_ne_zero_of_criticalMellinAtomWeight_ne_zero
    (n : ℕ) (hweight : criticalMellinAtomWeight n ≠ 0) :
    ccmActualHeadMatchedPhaseProjectiveGauge n ≠ 0 := by
  intro hgauge
  have hsquare := ccmActualHeadMatchedPhaseProjectiveGauge_sq n
  rw [hgauge] at hsquare
  norm_num at hsquare
  exact (div_ne_zero (pow_ne_zero 2 hweight) (Real.exp_ne_zero _)) hsquare.symm

theorem ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalVector_ratio
    (xi : ℝ) (n : ℕ) (hweight : criticalMellinAtomWeight n ≠ 0) :
    ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalVector xi n 1 /
        ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalVector xi n 0 =
      ((ccmActualHeadMatchedOrientedPhaseSymbol n xi).re : ℂ) := by
  rw [div_eq_iff]
  · simp [ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalVector]
    ring
  · have hgauge :=
      ccmActualHeadMatchedPhaseProjectiveGauge_ne_zero_of_criticalMellinAtomWeight_ne_zero
        n hweight
    simp [ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalVector]
    exact_mod_cast hgauge

def ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalReporter
    (xi : ℝ) (n : ℕ) : ℝ :=
  if criticalMellinAtomWeight n = 0 then 0
  else
    (ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalVector xi n 1 /
      ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalVector xi n 0).re

theorem ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalReporter_eq
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalReporter xi n =
      (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re := by
  unfold ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalReporter
  split_ifs with hweight
  · have hreporter := ccmActualHeadMatchedPhaseProjectiveGaugeReporter_eq xi n
    rw [ccmActualHeadMatchedPhaseProjectiveGaugeReporter, if_pos hweight] at hreporter
    exact hreporter
  · rw [ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalVector_ratio xi n hweight]
    simp

def ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalFiniteReporter
    (F : Finset ℕ) (xi : ℝ) : ℝ :=
  ∑ n ∈ F, ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalReporter xi n

theorem ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalFiniteReporter_eq
    (F : Finset ℕ) (xi : ℝ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalFiniteReporter F xi =
      (ccmActualHeadMatchedOrientedPhaseFiniteSymbol F xi).re := by
  unfold ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalFiniteReporter
    ccmActualHeadMatchedOrientedPhaseFiniteSymbol
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalReporter_eq xi n

theorem ccmActualHeadMatchedPrimePolarFiniteBlock_eq_chiralNodalLine
    (F : Finset ℕ) (f : SoninL2) :
    ccmActualHeadMatchedPrimePolarFiniteBlock F f =
      -2 * ∫ xi : ℝ,
        ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalFiniteReporter F xi *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2 := by
  rw [ccmActualHeadMatchedPrimePolarFiniteBlock_eq_orientedPhaseFiniteSymbol]
  congr 2
  funext xi
  rw [ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalFiniteReporter_eq]

end RHTower
