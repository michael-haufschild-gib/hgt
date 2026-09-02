import GaloisForLFunctions.RHTower.DyadicQuadraticGhostIndexRigidity
import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixRelativeReflectionFraming

/-!
# Dyadic relative-reflection integral-frame rigidity

The Gamma-six curved suspension is the framed difference between bare functional-equation
reflection and its horizontal half-density transport. Its determinant is the paired Gamma
curvature. This module proves that, throughout the open critical strip, the dyadic suspension can
act in a rank-two integral frame only at neutral horizontal grade.

This replaces an untyped demand that a varying real character equal an integer Euler index by a
legitimate integral-monodromy statement: a complex operator conjugate to an integer matrix has
integer determinant. The existing dyadic subunit law then forces that determinant to vanish.
-/

open Complex Matrix

namespace RHTower

noncomputable section

/-- A finite integral frame for the dyadic relative-reflection differential. The basis may be
complex, but the curved suspension has integer coordinates in that one frame. -/
structure DyadicRelativeReflectionIntegralFrame (a : ℝ) where
  basis : Matrix.GeneralLinearGroup (Fin 2) ℂ
  coordinates : Matrix (Fin 2) (Fin 2) ℤ
  intertwine :
    sourceHorizontalGammaSixCurvedSuspension (Real.log 2 * a) * basis.val =
      basis.val * coordinates.map (Int.castRingHom ℂ)

/-- An integral relative-reflection frame makes the exact framed determinant an integer. -/
theorem DyadicRelativeReflectionIntegralFrame.detDescent
    {a : ℝ} (F : DyadicRelativeReflectionIntegralFrame a) :
    ∃ k : ℤ,
      Matrix.det (sourceHorizontalGammaSixCurvedSuspension (Real.log 2 * a)) =
        (k : ℂ) := by
  let A : Matrix (Fin 2) (Fin 2) ℂ :=
    F.coordinates.map (Int.castRingHom ℂ)
  have hintertwine :
      sourceHorizontalGammaSixCurvedSuspension (Real.log 2 * a) * F.basis.val =
        F.basis.val * A := by
    simpa [A] using F.intertwine
  have hconj :
      sourceHorizontalGammaSixCurvedSuspension (Real.log 2 * a) =
        F.basis.val * A * F.basis.inv := by
    calc
      sourceHorizontalGammaSixCurvedSuspension (Real.log 2 * a) =
          sourceHorizontalGammaSixCurvedSuspension (Real.log 2 * a) * 1 := by simp
      _ = sourceHorizontalGammaSixCurvedSuspension (Real.log 2 * a) *
          (F.basis.val * F.basis.inv) := by rw [F.basis.val_inv]
      _ = (sourceHorizontalGammaSixCurvedSuspension (Real.log 2 * a) *
          F.basis.val) * F.basis.inv := by rw [Matrix.mul_assoc]
      _ = F.basis.val * A * F.basis.inv := by rw [hintertwine]
  refine ⟨Matrix.det F.coordinates, ?_⟩
  rw [hconj, Matrix.det_mul, Matrix.det_mul]
  have hdetBasis : Matrix.det F.basis.val * Matrix.det F.basis.inv = 1 := by
    rw [← Matrix.det_mul, F.basis.val_inv, Matrix.det_one]
  calc
    Matrix.det F.basis.val * Matrix.det A * Matrix.det F.basis.inv =
        Matrix.det A * (Matrix.det F.basis.val * Matrix.det F.basis.inv) := by ring
    _ = Matrix.det A := by rw [hdetBasis, mul_one]
    _ = ((Matrix.det F.coordinates : ℤ) : ℂ) := by
      simpa [A] using
        (RingHom.map_det (Int.castRingHom ℂ) F.coordinates).symm

/-- **One-prime integral-monodromy rigidity.** In the open strip, a dyadic integral frame for
the relative reflection differential forces neutral grade. -/
theorem eq_zero_of_dyadicRelativeReflectionIntegralFrame
    {a : ℝ} (ha : |a| < 1)
    (F : DyadicRelativeReflectionIntegralFrame a) :
    a = 0 := by
  obtain ⟨k, hk⟩ := F.detDescent
  have hkC :
      (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature
          (Real.log 2 * a) : ℂ) = (k : ℂ) := by
    rw [← det_sourceHorizontalGammaSixCurvedSuspension]
    exact hk
  have hkR :
      sourceHorizontalGammaSixUnitOppositeBoundaryCurvature (Real.log 2 * a) =
        (k : ℝ) := by
    exact_mod_cast hkC
  obtain ⟨hlower, _hupper⟩ := dyadicOneCopyQuadraticGhost_mem_subunit a ha
  rw [deningerIntegralGammaEvaluation_hermitianSquare_eq_neg_curvature] at hlower
  have hkLower : (0 : ℤ) ≤ k := by
    exact_mod_cast sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_nonneg
      (Real.log 2 * a) |>.trans_eq hkR
  have hkUpper : k < (1 : ℤ) := by
    exact_mod_cast (show (k : ℝ) < 1 by rw [← hkR]; linarith)
  have hk0 : k = 0 := by omega
  have hcurvature :
      sourceHorizontalGammaSixUnitOppositeBoundaryCurvature (Real.log 2 * a) = 0 := by
    rw [hkR, hk0]
    norm_num
  have hproduct : Real.log 2 * a = 0 :=
    (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_zero_iff _).1 hcurvature
  exact (mul_eq_zero.mp hproduct).resolve_left
    (ne_of_gt (Real.log_pos (by norm_num)))

/-- Canonical integral frame at neutral grade. -/
def dyadicRelativeReflectionIntegralFrameZero :
    DyadicRelativeReflectionIntegralFrame 0 where
  basis := 1
  coordinates := 0
  intertwine := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sourceHorizontalGammaSixCurvedSuspension,
        sourceHorizontalGammaSixForwardSuspensionLeg,
        sourceHorizontalGammaSixReflectedSuspensionLeg,
        sourceHorizontalGammaSixUnitForwardBoundaryDefect_eq,
        sourceHorizontalGammaSixUnitReflectedBoundaryDefect_eq]

/-- Complete classification: in the open strip, the dyadic relative reflection has an integral
frame exactly at neutral grade. -/
theorem dyadicRelativeReflectionIntegralFrame_nonempty_iff
    (a : ℝ) (ha : |a| < 1) :
    Nonempty (DyadicRelativeReflectionIntegralFrame a) ↔ a = 0 := by
  constructor
  · rintro ⟨F⟩
    exact eq_zero_of_dyadicRelativeReflectionIntegralFrame ha F
  · rintro rfl
    exact ⟨dyadicRelativeReflectionIntegralFrameZero⟩

/-- Pointwise source target on one Xi support point. -/
def XiDyadicRelativeReflectionIntegralFrameAt
    (rho : XiDivisorSupport) : Prop :=
  Nonempty (DyadicRelativeReflectionIntegralFrame
    (primeDepthBVWoldXiCenteredRate rho))

/-- At an actual Xi support point, dyadic relative-reflection integral descent is exactly
critical-line placement. -/
theorem xiDyadicRelativeReflectionIntegralFrameAt_iff_line
    (rho : XiDivisorSupport) :
    XiDyadicRelativeReflectionIntegralFrameAt rho ↔
      (rho : ℂ).re = 1 / 2 := by
  have ha : |primeDepthBVWoldXiCenteredRate rho| < 1 := by
    obtain ⟨hzero, hone⟩ := xi_divisor_support_re_mem_open_unit rho
    rw [primeDepthBVWoldXiCenteredRate, abs_lt]
    constructor <;> linarith
  rw [XiDyadicRelativeReflectionIntegralFrameAt,
    dyadicRelativeReflectionIntegralFrame_nonempty_iff _ ha,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- Global dyadic relative-reflection integral descent over the Xi divisor. -/
def EveryXiDyadicRelativeReflectionIntegralFrame : Prop :=
  ∀ rho : XiDivisorSupport,
    XiDyadicRelativeReflectionIntegralFrameAt rho

/-- Exact RH endpoint for the proposed global formation/properness theorem. -/
theorem everyXiDyadicRelativeReflectionIntegralFrame_iff_riemannHypothesis :
    EveryXiDyadicRelativeReflectionIntegralFrame ↔ RiemannHypothesis := by
  constructor
  · intro hframes
    apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
    intro rho
    exact (xiDyadicRelativeReflectionIntegralFrameAt_iff_line rho).1
      (hframes rho)
  · intro hRH rho
    exact (xiDyadicRelativeReflectionIntegralFrameAt_iff_line rho).2
      (xi_divisor_support_re_eq_half_of_rh hRH rho)

end


end RHTower
