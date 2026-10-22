import GaloisForLFunctions.RHTower.Deninger.DeningerOneSidedFramedMateCurvatureTransgression
import GaloisForLFunctions.RHTower.RiemannCenteredFlowCapacityIntertwining

/-!
# Centered-flow countercharacter erasure and relative Deninger curvature

The canonical centered-flow source countercharacter is exactly the inverse
of the Deninger half-density mate gain at every integer clock.  Applying that
countercharacter absolutely therefore flattens the one-sided framed
transport for every spectral parameter, including off-critical Xi divisor
fibres where the actual Gamma boundary coefficient is nonzero.

The detector is not lost before quotienting: the difference between raw and
countertransported reduced curvatures is a relative class, and its
source/reflection polarization is exactly the Deninger tensor-square mate
curvature.  At degree six this is the literal ordered `(2,3)`
Gamma/Calderon--Witt boundary coefficient up to the existing positive
calibration.

Thus absolute covariant normalization cannot be the missing conservative
Stokes annihilator.  Any surviving construction must retain the relative
raw-to-flat class in a mapping cone before the covariant quotient.
-/

open Complex
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## Source countercharacter at an integer clock -/

/-- Centered-flow source countercharacter sampled at integer clock `n`. -/
def deningerCenteredFlowClockCountercharacter (n : ℕ) (s : ℂ) : ℝ :=
  Real.exp (riemannReflectedSourceEntropy s * Real.log n)

/-- On an actual Xi divisor fibre this is literally the existing
centered-flow source countercharacter at time `log n`. -/
theorem deningerCenteredFlowClockCountercharacter_eq_xi
    (n : ℕ) (rho : XiDivisorSupport) :
    deningerCenteredFlowClockCountercharacter n (rho : ℂ) =
      xiCenteredFlowSourceCountercharacter rho (Real.log n) :=
  rfl

/-- The centered-flow countercharacter is exactly the inverse of the
Deninger half-density mate gain. -/
theorem deningerCenteredFlowClockCountercharacter_eq_mateGain_inv
    (n : ℕ) (s : ℂ) :
    deningerCenteredFlowClockCountercharacter n s =
      (deningerHalfDensityMateGain n s)⁻¹ := by
  rw [deningerCenteredFlowClockCountercharacter,
    deningerHalfDensityMateGain,
    riemannReflectedSourceEntropy_eq_neg_sourceCayleyRate]
  have hrate :
      -sourceCayleyTransverseRate 1 s = -(2 * s.re - 1) := by
    simp only [sourceCayleyTransverseRate, Complex.sub_re, Complex.one_re]
    ring
  rw [hrate]
  rw [show -(2 * s.re - 1) * Real.log n =
      -((2 * s.re - 1) * Real.log n) by ring]
  exact Real.exp_neg _

/-- Critical reflection inverts the source countercharacter. -/
theorem deningerCenteredFlowClockCountercharacter_reflection
    (n : ℕ) (s : ℂ) :
    deningerCenteredFlowClockCountercharacter n (1 - star s) =
      (deningerCenteredFlowClockCountercharacter n s)⁻¹ := by
  rw [deningerCenteredFlowClockCountercharacter,
    deningerCenteredFlowClockCountercharacter,
    riemannReflectedSourceEntropy_reflection]
  rw [show -riemannReflectedSourceEntropy s * Real.log n =
      -(riemannReflectedSourceEntropy s * Real.log n) by ring]
  exact Real.exp_neg _

/-- Critical reflection also inverts the Deninger mate gain. -/
theorem deningerHalfDensityMateGain_reflection
    (n : ℕ) (s : ℂ) :
    deningerHalfDensityMateGain n (1 - star s) =
      (deningerHalfDensityMateGain n s)⁻¹ := by
  rw [deningerHalfDensityMateGain, deningerHalfDensityMateGain]
  have hstar : (star s).re = s.re := by simp
  have hreflect :
      2 * (1 - star s).re - 1 = -(2 * s.re - 1) := by
    rw [Complex.sub_re, Complex.one_re, hstar]
    ring
  rw [hreflect]
  rw [show -(2 * s.re - 1) * Real.log n =
      -((2 * s.re - 1) * Real.log n) by ring]
  exact Real.exp_neg _

/-! ## Absolute countertransport is flat -/

/-- Gain after applying the canonical centered-flow source
countercharacter. -/
def deningerCenteredFlowCountertransportedGain (n : ℕ) (s : ℂ) : ℝ :=
  deningerCenteredFlowClockCountercharacter n s *
    deningerHalfDensityMateGain n s

/-- Covariant countertransport trivializes the mate gain at every spectral
parameter, not only on the critical line. -/
@[simp]
theorem deningerCenteredFlowCountertransportedGain_eq_one
    (n : ℕ) (s : ℂ) :
    deningerCenteredFlowCountertransportedGain n s = 1 := by
  rw [deningerCenteredFlowCountertransportedGain,
    deningerCenteredFlowClockCountercharacter_eq_mateGain_inv]
  exact inv_mul_cancel₀ (deningerHalfDensityMateGain_pos n s).ne'

/-- One-sided framed transport after absolute centered-flow
countertransport. -/
def deningerCenteredFlowCountertransportedFramedTransport
    (s : ℂ) (n : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  deningerOneSidedFramedTransport
    (fun k => deningerCenteredFlowCountertransportedGain k s) n

/-- The countertransported framed transport is the original flat affine
top-conormal transport. -/
theorem deningerCenteredFlowCountertransportedFramedTransport_eq_affine
    (s : ℂ) (n : ℕ) :
    deningerCenteredFlowCountertransportedFramedTransport s n =
      deningerTopConormalAffineTransport n := by
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [deningerCenteredFlowCountertransportedFramedTransport,
    deningerOneSidedFramedTransport,
    deningerTopConormalAffineTransport]

/-- **Absolute curvature-erasure no-go.**  Canonical centered-flow
countertransport makes the complete framed composition curvature zero for
all clocks and every spectral parameter. -/
theorem deningerCenteredFlowCountertransportedFramedCurvature_eq_zero
    (s : ℂ) (m n : ℕ) :
    deningerFramedCompositionCurvature
        (deningerCenteredFlowCountertransportedFramedTransport s) m n = 0 := by
  rw [deningerFramedCompositionCurvature,
    deningerCenteredFlowCountertransportedFramedTransport_eq_affine,
    deningerCenteredFlowCountertransportedFramedTransport_eq_affine,
    deningerCenteredFlowCountertransportedFramedTransport_eq_affine,
    deningerTopConormalAffineTransport_mul,
    sub_self]

/-! ## The actual detector survives relatively -/

/-- Raw-to-countertransported relative reduced curvature. -/
def deningerCenteredFlowRelativeReducedCurvature
    (s : ℂ) (n : ℕ) : ℝ :=
  deningerOneSidedReducedCurvature
      (fun k => deningerHalfDensityMateGain k s) n -
    deningerOneSidedReducedCurvature
      (fun k => deningerCenteredFlowCountertransportedGain k s) n

/-- The relative class retains exactly the raw reduced curvature. -/
theorem deningerCenteredFlowRelativeReducedCurvature_eq
    (s : ℂ) (n : ℕ) :
    deningerCenteredFlowRelativeReducedCurvature s n =
      1 - deningerHalfDensityMateGain n s := by
  simp [deningerCenteredFlowRelativeReducedCurvature,
    deningerOneSidedReducedCurvature]

/-- **Relative mate recovery.**  Source/reflection polarization of the
raw-to-flat relative curvature is exactly the Deninger tensor-square mate
curvature. -/
theorem
    deningerCenteredFlowRelativeReducedCurvature_reflection_sub_source
    {n : ℕ} (hn : 0 < n) (s : ℂ) :
    deningerCenteredFlowRelativeReducedCurvature (1 - star s) n -
        deningerCenteredFlowRelativeReducedCurvature s n =
      deningerTensorSquareRadialMateCurvature n s := by
  rw [deningerCenteredFlowRelativeReducedCurvature_eq,
    deningerCenteredFlowRelativeReducedCurvature_eq,
    deningerHalfDensityMateGain_reflection,
    ← deningerHalfDensityMateGain_sub_inv_eq_mateCurvature hn s]
  ring

/-- The actual ordered `(2,3)` Gamma boundary is the positive calibration
of the relative raw-to-countertransported curvature polarization. -/
theorem
    deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_relativeCountertransportCurvature
    (r : XiZeroCopy) :
    deningerCalderonWittBaseGammaBoundaryDefectCoefficient r =
      ((deningerCalderonWittBaseGammaMateCalibration *
        (deningerCenteredFlowRelativeReducedCurvature
              (1 - star (r.1 : ℂ)) 6 -
          deningerCenteredFlowRelativeReducedCurvature
              (r.1 : ℂ) 6) : ℝ) : ℂ) := by
  rw [
    deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_tensorSquareMateCurvature,
    deningerCenteredFlowRelativeReducedCurvature_reflection_sub_source
      (n := 6) (by norm_num) (r.1 : ℂ)]

/-- On an off-critical Xi fibre, absolute countertransport erases both
source and reflected framed curvatures although the actual Gamma boundary
coefficient remains nonzero. -/
theorem deningerCenteredFlow_absoluteErasure_not_coefficientFaithful
    (r : XiZeroCopy) (hoffline : (r.1 : ℂ).re ≠ 1 / 2) :
    deningerFramedCompositionCurvature
          (deningerCenteredFlowCountertransportedFramedTransport
            (r.1 : ℂ)) 2 6 = 0 ∧
      deningerFramedCompositionCurvature
          (deningerCenteredFlowCountertransportedFramedTransport
            (1 - star (r.1 : ℂ))) 2 6 = 0 ∧
      deningerCalderonWittBaseGammaBoundaryDefectCoefficient r ≠ 0 := by
  refine ⟨
    deningerCenteredFlowCountertransportedFramedCurvature_eq_zero
      (r.1 : ℂ) 2 6,
    deningerCenteredFlowCountertransportedFramedCurvature_eq_zero
      (1 - star (r.1 : ℂ)) 2 6,
    ?_⟩
  intro hzero
  exact hoffline
    ((deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_zero_iff r).1
      hzero)

/-- Any observation depending only on the two absolute countertransported
curvatures and vanishing at `(0,0)` misses the nonzero actual Gamma
coefficient on every off-critical divisor fibre. -/
theorem deningerCenteredFlow_absoluteCurvatureObservation_ne_gamma
    (r : XiZeroCopy) (hoffline : (r.1 : ℂ).re ≠ 1 / 2)
    (observe : Matrix (Fin 2) (Fin 2) ℝ →
      Matrix (Fin 2) (Fin 2) ℝ → ℂ)
    (hobserve : observe 0 0 = 0) :
    observe
        (deningerFramedCompositionCurvature
          (deningerCenteredFlowCountertransportedFramedTransport
            (r.1 : ℂ)) 2 6)
        (deningerFramedCompositionCurvature
          (deningerCenteredFlowCountertransportedFramedTransport
            (1 - star (r.1 : ℂ))) 2 6) ≠
      deningerCalderonWittBaseGammaBoundaryDefectCoefficient r := by
  rw [deningerCenteredFlowCountertransportedFramedCurvature_eq_zero,
    deningerCenteredFlowCountertransportedFramedCurvature_eq_zero,
    hobserve]
  intro hzero
  exact hoffline
    ((deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_zero_iff r).1
      hzero.symm)

end

end RHTower
