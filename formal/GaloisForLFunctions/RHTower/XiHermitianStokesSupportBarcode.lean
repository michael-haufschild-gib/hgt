import GaloisForLFunctions.HTGeometry.StokesEnhancedEpigraphConvolution
import GaloisForLFunctions.HTGeometry.StokesAnalyticWallRealization
import GaloisForLFunctions.RHTower.RiemannBoundaryGreenFractureLaw
import GaloisForLFunctions.RHTower.RouteRHarmonicQuantumGapCriterion
import GaloisForLFunctions.RHTower.CentralReciprocalMoments

/-!
# Xi Hermitian Stokes support barcode

This module applies the enhanced exponential support model to the actual Xi
source-inverse and Hermitian-adjoint depth-successor factors. It computes their
marked support mismatch, identifies its width with the existing boundary
fracture and reflected prime-tail entropy, and states the resulting exact RH
consumer criterion. It does not assume or prove barcode emptiness.
-/

open Complex Set

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.IrregularStokes.EnhancedEpigraph
open GaloisForLFunctions.IrregularStokes.AnalyticWall

noncomputable section

/-- Order-one Stokes phase of the source-inverse Xi nearby-pole factor. -/
def xiSourceInverseStokesPhase (rho : ℂ) : ℝ → ℝ :=
  fun theta =>
    liftedStokesPhase
      (depthSuccessorNearbyPole (-(rho - 1 / 2))) 1 theta

/-- Order-one Stokes phase of the Hermitian-adjoint Xi nearby-pole factor. -/
def xiHermitianAdjointStokesPhase (rho : ℂ) : ℝ → ℝ :=
  fun theta =>
    liftedStokesPhase
      (depthSuccessorNearbyPole
        (starRingEnd ℂ (rho - 1 / 2))) 1 theta

/-- Enhanced exponential support of the source-inverse factor. -/
def xiSourceInverseStokesSupport (rho : ℂ) : Set (ℝ × ℝ) :=
  exponentialEpigraph (xiSourceInverseStokesPhase rho)

/-- Enhanced exponential support of the Hermitian-adjoint factor. -/
def xiHermitianAdjointStokesSupport (rho : ℂ) : Set (ℝ × ℝ) :=
  exponentialEpigraph (xiHermitianAdjointStokesPhase rho)

/-- Symmetric-difference barcode on the marked radial fiber `theta = 0`. -/
def xiHermitianStokesRadialBarcode (rho : ℂ) : Set ℝ :=
  {t |
    ((0, t) ∈ xiSourceInverseStokesSupport rho ∧
        (0, t) ∉ xiHermitianAdjointStokesSupport rho) ∨
      ((0, t) ∈ xiHermitianAdjointStokesSupport rho ∧
        (0, t) ∉ xiSourceInverseStokesSupport rho)}

@[simp]
theorem xiSourceInverseStokesPhase_zero (rho : ℂ) :
    xiSourceInverseStokesPhase rho 0 = rho.re - 1 / 2 := by
  simp [xiSourceInverseStokesPhase, liftedStokesPhase,
    depthSuccessorNearbyPole]

@[simp]
theorem xiHermitianAdjointStokesPhase_zero (rho : ℂ) :
    xiHermitianAdjointStokesPhase rho 0 = -(rho.re - 1 / 2) := by
  simp [xiHermitianAdjointStokesPhase, liftedStokesPhase,
    depthSuccessorNearbyPole]

@[simp]
theorem mem_xiSourceInverseStokesSupport_zero (rho : ℂ) (t : ℝ) :
    (0, t) ∈ xiSourceInverseStokesSupport rho ↔
      -(rho.re - 1 / 2) ≤ t := by
  change 0 ≤ t + xiSourceInverseStokesPhase rho 0 ↔ _
  rw [xiSourceInverseStokesPhase_zero]
  constructor <;> intro h <;> linarith

@[simp]
theorem mem_xiHermitianAdjointStokesSupport_zero (rho : ℂ) (t : ℝ) :
    (0, t) ∈ xiHermitianAdjointStokesSupport rho ↔
      rho.re - 1 / 2 ≤ t := by
  change 0 ≤ t + xiHermitianAdjointStokesPhase rho 0 ↔ _
  rw [xiHermitianAdjointStokesPhase_zero]
  constructor <;> intro h <;> linarith

/-- The complete marked support mismatch is the interval cut out by horizontal
displacement from the critical line. -/
theorem xiHermitianStokesRadialBarcode_eq_Ico (rho : ℂ) :
    xiHermitianStokesRadialBarcode rho =
      Set.Ico (-|rho.re - 1 / 2|) |rho.re - 1 / 2| := by
  ext t
  simp only [xiHermitianStokesRadialBarcode, Set.mem_setOf_eq,
    mem_xiSourceInverseStokesSupport_zero,
    mem_xiHermitianAdjointStokesSupport_zero, Set.mem_Ico]
  by_cases hx : 0 ≤ rho.re - 1 / 2
  · rw [abs_of_nonneg hx]
    constructor
    · rintro (⟨hlo, hhi⟩ | ⟨hlo, hhi⟩)
      · exact ⟨hlo, lt_of_not_ge hhi⟩
      · exfalso
        exact hhi (le_trans (neg_le_self hx) hlo)
    · rintro ⟨hlo, hhi⟩
      exact Or.inl ⟨hlo, not_le.mpr hhi⟩
  · have hx' : rho.re - 1 / 2 ≤ 0 := le_of_not_ge hx
    rw [abs_of_nonpos hx']
    constructor
    · rintro (⟨hlo, hhi⟩ | ⟨hlo, hhi⟩)
      · exfalso
        apply hhi
        linarith
      · constructor
        · linarith
        · exact lt_of_not_ge hhi
    · rintro ⟨hlo, hhi⟩
      apply Or.inr
      constructor
      · linarith
      · exact not_le.mpr (by linarith)

/-- Full enhanced exponential supports agree exactly at Hermitian fixed
factors, equivalently on the critical line. -/
theorem xiSourceInverseStokesSupport_eq_hermitianAdjoint_iff (rho : ℂ) :
    xiSourceInverseStokesSupport rho =
        xiHermitianAdjointStokesSupport rho ↔
      rho.re = 1 / 2 := by
  constructor
  · intro hsupport
    have hphase :
        xiSourceInverseStokesPhase rho =
          xiHermitianAdjointStokesPhase rho :=
      exponentialEpigraph_injective hsupport
    have hzero := congrFun hphase 0
    simp only [xiSourceInverseStokesPhase_zero,
      xiHermitianAdjointStokesPhase_zero] at hzero
    linarith
  · intro hre
    have hcoeff :
        depthSuccessorNearbyPole (-(rho - 1 / 2)) =
          depthSuccessorNearbyPole
            (starRingEnd ℂ (rho - 1 / 2)) := by
      apply Complex.ext
      · simp [depthSuccessorNearbyPole, hre]
      · simp [depthSuccessorNearbyPole]
    unfold xiSourceInverseStokesSupport
      xiHermitianAdjointStokesSupport
      xiSourceInverseStokesPhase
      xiHermitianAdjointStokesPhase
    rw [hcoeff]

/-- Endpoint distance of the marked Hermitian Stokes barcode. -/
def xiHermitianStokesRadialBarcodeWidth (rho : ℂ) : ℝ :=
  2 * |rho.re - 1 / 2|

/-- Barcode width is the norm of the source-inverse/analytic-adjoint boundary
fracture. -/
theorem xiHermitianStokesRadialBarcodeWidth_eq_norm_boundaryFracture
    (rho : ℂ) :
    xiHermitianStokesRadialBarcodeWidth rho =
      ‖xiNearbyPoleDualityAdjunctionFracture rho‖ := by
  rw [xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
  change 2 * |rho.re - 1 / 2| =
    ‖((2 * (rho.re - 1 / 2) : ℝ) : ℂ)‖
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
  norm_num

/-- Barcode width is the absolute reflected prime-tail entropy of the actual
Riemann source. -/
theorem xiHermitianStokesRadialBarcodeWidth_eq_abs_reflectedSourceEntropy
    (rho : ℂ) :
    xiHermitianStokesRadialBarcodeWidth rho =
      |riemannReflectedSourceEntropy rho| := by
  rw [xiHermitianStokesRadialBarcodeWidth_eq_norm_boundaryFracture,
    xiNearbyPoleDualityAdjunctionFracture_eq_neg_reflectedSourceEntropy]
  simp

/-- The marked support mismatch vanishes exactly on the critical line. -/
theorem xiHermitianStokesRadialBarcode_eq_empty_iff (rho : ℂ) :
    xiHermitianStokesRadialBarcode rho = ∅ ↔
      rho.re = 1 / 2 := by
  rw [xiHermitianStokesRadialBarcode_eq_Ico]
  constructor
  · intro hempty
    by_contra hne
    have hpos : 0 < |rho.re - 1 / 2| :=
      abs_pos.mpr (sub_ne_zero.mpr hne)
    have hzero :
        0 ∈ Set.Ico (-|rho.re - 1 / 2|) |rho.re - 1 / 2| := by
      constructor <;> linarith
    rw [hempty] at hzero
    exact hzero
  · intro hre
    ext t
    simp [hre]

/-- RH is exactly emptiness of every actual Xi-divisor Hermitian Stokes
barcode. This is a consumer criterion; it does not prove emptiness. -/
theorem riemannHypothesis_iff_forall_xiHermitianStokesRadialBarcode_eq_empty :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport,
        xiHermitianStokesRadialBarcode (rho : ℂ) = ∅ := by
  constructor
  · intro hRH rho
    exact (xiHermitianStokesRadialBarcode_eq_empty_iff (rho : ℂ)).2
      (xi_divisor_support_re_eq_half_of_rh hRH rho)
  · intro hbarcode
    apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
    intro rho
    exact (xiHermitianStokesRadialBarcode_eq_empty_iff (rho : ℂ)).1
      (hbarcode rho)

end

end RHTower
