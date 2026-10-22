import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixPairedDefectGaussHodgeCurvature
import GaloisForLFunctions.RHTower.SeamSuspensionTrace
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusHyperbolicRapidity
import GaloisForLFunctions.HTGeometry.SourceFormationHarmonicMechanics

open Complex Matrix

namespace RHTower

noncomputable section

/-- Forward cyclic defect as one odd corner of a two-state suspension. -/
def sourceHorizontalGammaSixForwardSuspensionLeg (a : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, (sourceHorizontalGammaSixUnitForwardBoundaryDefect a : ℂ);
     0, 0]

/-- Reflected cyclic defect as the opposite odd corner. -/
def sourceHorizontalGammaSixReflectedSuspensionLeg (a : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 0;
     (sourceHorizontalGammaSixUnitReflectedBoundaryDefect a : ℂ), 0]

/-- Odd two-orientation differential before imposing flatness. -/
def sourceHorizontalGammaSixCurvedSuspension (a : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  sourceHorizontalGammaSixForwardSuspensionLeg a +
    sourceHorizontalGammaSixReflectedSuspensionLeg a

/-- Canonical curved contracting homotopy away from the neutral character. -/
def sourceHorizontalGammaSixCurvedSuspensionHomotopy (a : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (-(1 : ℂ) /
      (2 * (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a : ℂ))) •
    sourceHorizontalGammaSixCurvedSuspension a

/-- Parity grading: forward and reflected states have opposite degree. -/
def sourceHorizontalGammaSixSuspensionGrading :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![-1, 0; 0, 1]

/-- Forward-corner compression. -/
def sourceHorizontalGammaSixForwardCorner :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, 0]

/-- Reflected-corner compression. -/
def sourceHorizontalGammaSixReflectedCorner :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 0; 0, 1]

/-- Canonical positive-half-density aperture whose Route-P/Route-R rapidity is the horizontal
Gamma-six character. -/
def sourceHorizontalGammaSixRapidityAperture (a : ℝ) : ℝ :=
  (Real.exp (2 * a) - 1) / 2

theorem sourceHorizontalGammaSixRapidityAperture_gt_neg_half (a : ℝ) :
    -(1 / 2 : ℝ) < sourceHorizontalGammaSixRapidityAperture a := by
  rw [sourceHorizontalGammaSixRapidityAperture]
  have hexp : 0 < Real.exp (2 * a) := Real.exp_pos _
  linarith

/-- The canonical aperture is coefficient-exact: its hyperbolic rapidity is the original
horizontal character, with no rescaling or loss of reflection orientation. -/
theorem mobiusCriticalTwoSidedRapidity_sourceHorizontalGammaSixRapidityAperture
    (a : ℝ) :
    HedenmalmThetaSource.mobiusCriticalTwoSidedRapidity
        (sourceHorizontalGammaSixRapidityAperture a) = a := by
  rw [HedenmalmThetaSource.mobiusCriticalTwoSidedRapidity,
    sourceHorizontalGammaSixRapidityAperture]
  have hexp : 0 < Real.exp a := Real.exp_pos _
  have hsquare :
      1 + 2 * ((Real.exp (2 * a) - 1) / 2) = (Real.exp a) ^ (2 : ℕ) := by
    rw [show 2 * a = a + a by ring, Real.exp_add]
    ring
  rw [hsquare, Real.sqrt_sq hexp.le, Real.log_exp]

theorem sourceHorizontalGammaSixForwardSuspensionLeg_odd (a : ℝ) :
    sourceHorizontalGammaSixSuspensionGrading *
        sourceHorizontalGammaSixForwardSuspensionLeg a =
      -(sourceHorizontalGammaSixForwardSuspensionLeg a *
        sourceHorizontalGammaSixSuspensionGrading) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceHorizontalGammaSixSuspensionGrading,
      sourceHorizontalGammaSixForwardSuspensionLeg, Matrix.mul_apply]

theorem sourceHorizontalGammaSixReflectedSuspensionLeg_odd (a : ℝ) :
    sourceHorizontalGammaSixSuspensionGrading *
        sourceHorizontalGammaSixReflectedSuspensionLeg a =
      -(sourceHorizontalGammaSixReflectedSuspensionLeg a *
        sourceHorizontalGammaSixSuspensionGrading) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceHorizontalGammaSixSuspensionGrading,
      sourceHorizontalGammaSixReflectedSuspensionLeg, Matrix.mul_apply]

theorem sourceHorizontalGammaSixCurvedSuspension_odd (a : ℝ) :
    sourceHorizontalGammaSixSuspensionGrading *
        sourceHorizontalGammaSixCurvedSuspension a =
      -(sourceHorizontalGammaSixCurvedSuspension a *
        sourceHorizontalGammaSixSuspensionGrading) := by
  rw [sourceHorizontalGammaSixCurvedSuspension, Matrix.mul_add,
    Matrix.add_mul, neg_add,
    sourceHorizontalGammaSixForwardSuspensionLeg_odd,
    sourceHorizontalGammaSixReflectedSuspensionLeg_odd]

/-- Exact curved-complex law: the square is minus paired cyclic curvature times identity. -/
theorem sourceHorizontalGammaSixCurvedSuspension_sq (a : ℝ) :
    sourceHorizontalGammaSixCurvedSuspension a *
        sourceHorizontalGammaSixCurvedSuspension a =
      -(sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a : ℂ) •
        (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceHorizontalGammaSixCurvedSuspension,
      sourceHorizontalGammaSixForwardSuspensionLeg,
      sourceHorizontalGammaSixReflectedSuspensionLeg,
      sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_neg_mul_defects,
      Matrix.mul_apply]
  all_goals ring

/-- The suspension becomes an honest differential exactly at neutral character. -/
theorem sourceHorizontalGammaSixCurvedSuspension_sq_eq_zero_iff (a : ℝ) :
    sourceHorizontalGammaSixCurvedSuspension a *
        sourceHorizontalGammaSixCurvedSuspension a = 0 ↔ a = 0 := by
  rw [sourceHorizontalGammaSixCurvedSuspension_sq]
  constructor
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
    have h00' : -(sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a : ℂ) = 0 := by
      simpa using h00
    have hreal : sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a = 0 := by
      exact_mod_cast neg_eq_zero.mp h00'
    exact (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_zero_iff a).1 hreal
  · rintro rfl
    simp [sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq]

/-- **Curved Hodge-contraction reversal.** Off center the non-flat suspension is invertible enough
to satisfy the bare Hodge relation with zero harmonic projection. Hence Hodge compression without
an independently proved `D²=0` accepts exactly the wrong, curved sector. -/
theorem sourceHorizontalGammaSixCurvedSuspension_contractible_of_ne_zero
    {a : ℝ} (ha : a ≠ 0) :
    sourceHorizontalGammaSixCurvedSuspension a *
          sourceHorizontalGammaSixCurvedSuspensionHomotopy a +
        sourceHorizontalGammaSixCurvedSuspensionHomotopy a *
          sourceHorizontalGammaSixCurvedSuspension a = 1 := by
  have hKreal : sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a ≠ 0 :=
    (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_pos_iff a).2 ha |>.ne'
  have hK : (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a : ℂ) ≠ 0 := by
    exact_mod_cast hKreal
  rw [sourceHorizontalGammaSixCurvedSuspensionHomotopy,
    Matrix.mul_smul, Matrix.smul_mul,
    sourceHorizontalGammaSixCurvedSuspension_sq,
    smul_smul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp [hK] <;> norm_num

/-- Bare graded Hodge compression is available for every observable in the off-center curved
sector. This instantiates the corpus transgression theorem with zero harmonic projection and shows
why compression, absent nilpotence, cannot be the RH producer. -/
theorem sourceHorizontalGammaSixCurvedSuspension_offCenter_hodgeTransgression
    {a : ℝ} (ha : a ≠ 0) (H : Matrix (Fin 2) (Fin 2) ℂ) :
    gradedMatrixTrace sourceHorizontalGammaSixSuspensionGrading H =
      gradedMatrixTrace sourceHorizontalGammaSixSuspensionGrading
        (sourceHorizontalGammaSixCurvedSuspensionHomotopy a *
          (sourceHorizontalGammaSixCurvedSuspension a * H -
            H * sourceHorizontalGammaSixCurvedSuspension a)) := by
  have hHodge :
      1 - (0 : Matrix (Fin 2) (Fin 2) ℂ) =
        sourceHorizontalGammaSixCurvedSuspension a *
            sourceHorizontalGammaSixCurvedSuspensionHomotopy a +
          sourceHorizontalGammaSixCurvedSuspensionHomotopy a *
            sourceHorizontalGammaSixCurvedSuspension a := by
    rw [sub_zero]
    exact (sourceHorizontalGammaSixCurvedSuspension_contractible_of_ne_zero ha).symm
  have h := gradedMatrixTrace_hodgeTransgression
    sourceHorizontalGammaSixSuspensionGrading
    (0 : Matrix (Fin 2) (Fin 2) ℂ) H
    (sourceHorizontalGammaSixCurvedSuspension a)
    (sourceHorizontalGammaSixCurvedSuspensionHomotopy a)
    (sourceHorizontalGammaSixCurvedSuspension_odd a) hHodge
  simpa [gradedMatrixTrace] using h

/-- Ordinary trace detects twice the curved-complex obstruction. -/
theorem trace_sourceHorizontalGammaSixCurvedSuspension_sq (a : ℝ) :
    Matrix.trace
        (sourceHorizontalGammaSixCurvedSuspension a *
          sourceHorizontalGammaSixCurvedSuspension a) =
      -2 * (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a : ℂ) := by
  rw [sourceHorizontalGammaSixCurvedSuspension_sq, Matrix.trace_smul,
    Matrix.trace_fin_two]
  norm_num
  ring

/-- Determinant of the odd two-orientation suspension is exactly the positive paired cyclic
curvature. This is the finite determinant/rank-birth form of the same Gauss-Hodge obstruction. -/
theorem det_sourceHorizontalGammaSixCurvedSuspension (a : ℝ) :
    Matrix.det (sourceHorizontalGammaSixCurvedSuspension a) =
      (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a : ℂ) := by
  rw [Matrix.det_fin_two]
  simp [sourceHorizontalGammaSixCurvedSuspension,
    sourceHorizontalGammaSixForwardSuspensionLeg,
    sourceHorizontalGammaSixReflectedSuspensionLeg,
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_neg_mul_defects]

/-- Route P's normalized source Cayley coordinate is exactly the hyperbolic tangent of the
Gamma-six horizontal character on the canonical aperture. -/
theorem mobiusCriticalTwoSidedCayleyDiscrepancy_gammaSixRapidityAperture
    (a : ℝ) :
    HedenmalmThetaSource.mobiusCriticalTwoSidedCayleyDiscrepancy
        (sourceHorizontalGammaSixRapidityAperture a) 0 = Real.tanh a := by
  have h :=
    HedenmalmThetaSource.mobiusCriticalTwoSidedCayleyDiscrepancy_eq_tanh_rapidity_sub
      (sourceHorizontalGammaSixRapidityAperture_gt_neg_half a)
      (by norm_num : -(1 / 2 : ℝ) < 0)
  rw [mobiusCriticalTwoSidedRapidity_sourceHorizontalGammaSixRapidityAperture] at h
  simpa [HedenmalmThetaSource.mobiusCriticalTwoSidedRapidity] using h

/-- Route P's normalized source Hardy overlap is exactly the hyperbolic secant of the same
Gamma-six character. -/
theorem mobiusCriticalTwoSidedUnitHardyGram_gammaSixRapidityAperture
    (a : ℝ) :
    HedenmalmThetaSource.mobiusCriticalTwoSidedUnitHardyGram
        (sourceHorizontalGammaSixRapidityAperture a) 0 =
      (Real.cosh a)⁻¹ := by
  have h :=
    HedenmalmThetaSource.mobiusCriticalTwoSidedUnitHardyGram_eq_inv_cosh_rapidity_sub
      (sourceHorizontalGammaSixRapidityAperture_gt_neg_half a)
      (by norm_num : -(1 / 2 : ℝ) < 0)
  rw [mobiusCriticalTwoSidedRapidity_sourceHorizontalGammaSixRapidityAperture] at h
  simpa [HedenmalmThetaSource.mobiusCriticalTwoSidedRapidity] using h

/-- Exact P/R/L determinant weld. The odd suspension determinant, after multiplication by the
positive Hardy overlap, is twice its unsquared normalized Hardy loss. -/
theorem sourceHorizontalGammaSixCurvature_mul_hardyGram_eq_loss (a : ℝ) :
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a *
        HedenmalmThetaSource.mobiusCriticalTwoSidedUnitHardyGram
          (sourceHorizontalGammaSixRapidityAperture a) 0 =
      2 * (1 -
        HedenmalmThetaSource.mobiusCriticalTwoSidedUnitHardyGram
          (sourceHorizontalGammaSixRapidityAperture a) 0) := by
  rw [sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq,
    mobiusCriticalTwoSidedUnitHardyGram_gammaSixRapidityAperture]
  have hcosh : Real.cosh a ≠ 0 := (Real.cosh_pos a).ne'
  field_simp [hcosh]

/-- Polynomial, division-free form of the Frankenstein seam: the suspension determinant is the
Route-P Cayley energy after the exact positive Hardy gauge. -/
theorem re_det_sourceHorizontalGammaSixCurvedSuspension_mul_hardyGauge_eq_cayleyEnergy
    (a : ℝ) :
    (Matrix.det (sourceHorizontalGammaSixCurvedSuspension a)).re *
          HedenmalmThetaSource.mobiusCriticalTwoSidedUnitHardyGram
            (sourceHorizontalGammaSixRapidityAperture a) 0 *
          (1 + HedenmalmThetaSource.mobiusCriticalTwoSidedUnitHardyGram
            (sourceHorizontalGammaSixRapidityAperture a) 0) =
      2 * HedenmalmThetaSource.mobiusCriticalTwoSidedCayleyDiscrepancy
        (sourceHorizontalGammaSixRapidityAperture a) 0 ^ (2 : ℕ) := by
  rw [det_sourceHorizontalGammaSixCurvedSuspension]
  simp only [ofReal_re]
  rw [sourceHorizontalGammaSixCurvature_mul_hardyGram_eq_loss]
  have hpyth :=
    HedenmalmThetaSource.sq_mobiusCriticalTwoSidedCayleyDiscrepancy_add_sq_unitHardyGram
      (sourceHorizontalGammaSixRapidityAperture_gt_neg_half a)
      (by norm_num : -(1 / 2 : ℝ) < 0)
  nlinarith

/-- Determinant flatness and Julia saturation are the same pointwise condition on the literal
source aperture. -/
theorem det_sourceHorizontalGammaSixCurvedSuspension_eq_zero_iff_cayleyDiscrepancy_eq_zero
    (a : ℝ) :
    Matrix.det (sourceHorizontalGammaSixCurvedSuspension a) = 0 ↔
      HedenmalmThetaSource.mobiusCriticalTwoSidedCayleyDiscrepancy
        (sourceHorizontalGammaSixRapidityAperture a) 0 = 0 := by
  rw [det_sourceHorizontalGammaSixCurvedSuspension, Complex.ofReal_eq_zero,
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_zero_iff,
    mobiusCriticalTwoSidedCayleyDiscrepancy_gammaSixRapidityAperture]
  constructor
  · rintro rfl
    simp
  · intro h
    apply Real.tanh_injective
    simpa using h

/-- Hostile conservation audit. The intrinsic theta/Route-R current is constant on every
canonical Gamma-six aperture even when the coefficient-faithful suspension determinant is
nonzero. Thus conserved hyperbolic current cannot force flatness. -/
theorem sourceHorizontalGammaSix_thetaCurrent_constant_but_determinant_nonzero_iff
    (a : ℝ) :
    (HedenmalmThetaSource.thetaGreenHyperbolicCurrent
          (HedenmalmThetaSource.mobiusCriticalTwoSidedHyperbolicPoint
            (sourceHorizontalGammaSixRapidityAperture a)) = -2 ∧
      Matrix.det (sourceHorizontalGammaSixCurvedSuspension a) ≠ 0) ↔
      a ≠ 0 := by
  have hcurrent :=
    HedenmalmThetaSource.thetaGreenHyperbolicCurrent_mobiusCriticalTwoSidedHyperbolicPoint
      (sourceHorizontalGammaSixRapidityAperture_gt_neg_half a)
  have hdet : Matrix.det (sourceHorizontalGammaSixCurvedSuspension a) = 0 ↔ a = 0 := by
    rw [det_sourceHorizontalGammaSixCurvedSuspension, Complex.ofReal_eq_zero,
      sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_zero_iff]
  constructor
  · exact fun h ha => h.2 (hdet.2 ha)
  · exact fun ha => ⟨hcurrent, fun hzero => ha (hdet.1 hzero)⟩

/-- The forward Gamma-six cyclic defect is literally the first source-formation edge energy at
radial character `exp a`. -/
theorem sourceHorizontalGammaSixForwardBoundaryDefect_sq_eq_geometricRefinementEnergy
    (a : ℝ) :
    sourceHorizontalGammaSixUnitForwardBoundaryDefect a ^ (2 : ℕ) =
      GaloisForLFunctions.HTGeometry.geometricRefinementEnergy (Real.exp a) 0 := by
  rw [sourceHorizontalGammaSixUnitForwardBoundaryDefect_eq,
    GaloisForLFunctions.HTGeometry.geometricRefinementEnergy]
  norm_num

/-- The reflected Gamma-six cyclic defect is the reciprocal first source-formation edge energy,
with the reflection orientation retained before squaring. -/
theorem sourceHorizontalGammaSixReflectedBoundaryDefect_sq_eq_geometricRefinementEnergy
    (a : ℝ) :
    sourceHorizontalGammaSixUnitReflectedBoundaryDefect a ^ (2 : ℕ) =
      GaloisForLFunctions.HTGeometry.geometricRefinementEnergy (Real.exp a)⁻¹ 0 := by
  rw [sourceHorizontalGammaSixUnitReflectedBoundaryDefect_eq,
    GaloisForLFunctions.HTGeometry.geometricRefinementEnergy, Real.exp_neg]
  norm_num

/-- Exact formation-completion weld. Bilateral admission of the full literal exponent-edge
history is equivalent to flatness of its two-state Gamma-six boundary suspension. -/
theorem sourceHorizontalGammaSix_bilateralFormationAdmission_iff_det_eq_zero (a : ℝ) :
    (Summable (GaloisForLFunctions.HTGeometry.geometricRefinementEnergy (Real.exp a)) ∧
        Summable (GaloisForLFunctions.HTGeometry.geometricRefinementEnergy (Real.exp a)⁻¹)) ↔
      Matrix.det (sourceHorizontalGammaSixCurvedSuspension a) = 0 := by
  rw [GaloisForLFunctions.HTGeometry.bilateral_geometricRefinementEnergy_summable_iff
      (Real.exp_pos a),
    det_sourceHorizontalGammaSixCurvedSuspension, Complex.ofReal_eq_zero,
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_zero_iff]
  constructor
  · intro h
    apply Real.exp_injective
    simpa using h
  · rintro rfl
    simp

/-- Graded trace is blind to the nonzero scalar curvature: it vanishes for every character. -/
theorem gradedMatrixTrace_sourceHorizontalGammaSixCurvedSuspension_sq (a : ℝ) :
    gradedMatrixTrace sourceHorizontalGammaSixSuspensionGrading
        (sourceHorizontalGammaSixCurvedSuspension a *
          sourceHorizontalGammaSixCurvedSuspension a) = 0 := by
  rw [sourceHorizontalGammaSixCurvedSuspension_sq, gradedMatrixTrace]
  simp [sourceHorizontalGammaSixSuspensionGrading, Matrix.trace_fin_two]

/-- Exact supertrace no-go: graded curvature trace vanishes identically, while the underlying
curved differential still fails to square to zero exactly away from neutral character. -/
theorem sourceHorizontalGammaSix_supertraceFlat_but_curved_iff (a : ℝ) :
    (gradedMatrixTrace sourceHorizontalGammaSixSuspensionGrading
          (sourceHorizontalGammaSixCurvedSuspension a *
            sourceHorizontalGammaSixCurvedSuspension a) = 0 ∧
      sourceHorizontalGammaSixCurvedSuspension a *
          sourceHorizontalGammaSixCurvedSuspension a ≠ 0) ↔ a ≠ 0 := by
  constructor
  · intro h ha
    apply h.2
    exact (sourceHorizontalGammaSixCurvedSuspension_sq_eq_zero_iff a).2 ha
  · intro ha
    exact ⟨gradedMatrixTrace_sourceHorizontalGammaSixCurvedSuspension_sq a,
      fun hzero => ha
        ((sourceHorizontalGammaSixCurvedSuspension_sq_eq_zero_iff a).1 hzero)⟩

/-- Split-leg commutator has zero ordinary trace, independently of the horizontal character. -/
theorem trace_sourceHorizontalGammaSixSuspensionLeg_commutator (a : ℝ) :
    Matrix.trace
      (sourceHorizontalGammaSixForwardSuspensionLeg a *
          sourceHorizontalGammaSixReflectedSuspensionLeg a -
        sourceHorizontalGammaSixReflectedSuspensionLeg a *
          sourceHorizontalGammaSixForwardSuspensionLeg a) = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

/-- Exact ordinary-trace no-go: cyclic commutator trace vanishes for every character even though
the resolved paired curvature is strictly positive precisely off center. -/
theorem sourceHorizontalGammaSix_commutatorTraceFlat_but_curvature_pos_iff (a : ℝ) :
    (Matrix.trace
          (sourceHorizontalGammaSixForwardSuspensionLeg a *
              sourceHorizontalGammaSixReflectedSuspensionLeg a -
            sourceHorizontalGammaSixReflectedSuspensionLeg a *
              sourceHorizontalGammaSixForwardSuspensionLeg a) = 0 ∧
      0 < sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a) ↔ a ≠ 0 := by
  constructor
  · intro h
    exact (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_pos_iff a).1 h.2
  · intro ha
    exact ⟨trace_sourceHorizontalGammaSixSuspensionLeg_commutator a,
      (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_pos_iff a).2 ha⟩

/-- Unlike ordinary trace, the grading resolves both corners and reads twice the positive paired
curvature from the split-leg commutator. -/
theorem gradedMatrixTrace_sourceHorizontalGammaSixSuspensionLeg_commutator (a : ℝ) :
    gradedMatrixTrace sourceHorizontalGammaSixSuspensionGrading
      (sourceHorizontalGammaSixForwardSuspensionLeg a *
          sourceHorizontalGammaSixReflectedSuspensionLeg a -
        sourceHorizontalGammaSixReflectedSuspensionLeg a *
          sourceHorizontalGammaSixForwardSuspensionLeg a) =
      2 * (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a : ℂ) := by
  rw [gradedMatrixTrace]
  simp [sourceHorizontalGammaSixSuspensionGrading,
    sourceHorizontalGammaSixForwardSuspensionLeg,
    sourceHorizontalGammaSixReflectedSuspensionLeg,
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_neg_mul_defects,
    Matrix.trace_fin_two]
  ring_nf

/-- Forward compressed trace is the negative paired curvature. -/
theorem trace_forwardCorner_mul_sourceHorizontalGammaSixSuspensionLeg_commutator (a : ℝ) :
    Matrix.trace
      (sourceHorizontalGammaSixForwardCorner *
        (sourceHorizontalGammaSixForwardSuspensionLeg a *
            sourceHorizontalGammaSixReflectedSuspensionLeg a -
          sourceHorizontalGammaSixReflectedSuspensionLeg a *
            sourceHorizontalGammaSixForwardSuspensionLeg a)) =
      -(sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a : ℂ) := by
  simp [sourceHorizontalGammaSixForwardCorner,
    sourceHorizontalGammaSixForwardSuspensionLeg,
    sourceHorizontalGammaSixReflectedSuspensionLeg,
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_neg_mul_defects,
    Matrix.trace_fin_two]

/-- Reflected compressed trace is the positive paired curvature. -/
theorem trace_reflectedCorner_mul_sourceHorizontalGammaSixSuspensionLeg_commutator (a : ℝ) :
    Matrix.trace
      (sourceHorizontalGammaSixReflectedCorner *
        (sourceHorizontalGammaSixForwardSuspensionLeg a *
            sourceHorizontalGammaSixReflectedSuspensionLeg a -
          sourceHorizontalGammaSixReflectedSuspensionLeg a *
            sourceHorizontalGammaSixForwardSuspensionLeg a)) =
      (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a : ℂ) := by
  simp [sourceHorizontalGammaSixReflectedCorner,
    sourceHorizontalGammaSixForwardSuspensionLeg,
    sourceHorizontalGammaSixReflectedSuspensionLeg,
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_neg_mul_defects,
    Matrix.trace_fin_two]
  ring

/-- Literal ordinary-trace energy of the curved two-orientation suspension. -/
def sourceHorizontalGammaSixSuspensionTraceEnergy (a : ℝ) : ℝ :=
  -(Matrix.trace
      (sourceHorizontalGammaSixCurvedSuspension a *
        sourceHorizontalGammaSixCurvedSuspension a)).re / 2

theorem sourceHorizontalGammaSixSuspensionTraceEnergy_eq_curvature (a : ℝ) :
    sourceHorizontalGammaSixSuspensionTraceEnergy a =
      sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a := by
  rw [sourceHorizontalGammaSixSuspensionTraceEnergy,
    trace_sourceHorizontalGammaSixCurvedSuspension_sq]
  simp

/-- Ordinary curvature-trace energy and determinant of the odd suspension are the same real
quantity; trace, determinant, and paired cyclic curvature now live on one carrier. -/
theorem sourceHorizontalGammaSixSuspensionTraceEnergy_eq_re_det (a : ℝ) :
    sourceHorizontalGammaSixSuspensionTraceEnergy a =
      (Matrix.det (sourceHorizontalGammaSixCurvedSuspension a)).re := by
  rw [sourceHorizontalGammaSixSuspensionTraceEnergy_eq_curvature,
    det_sourceHorizontalGammaSixCurvedSuspension]
  simp

/-- Gauss-weighted ordinary trace energy at one literal prime clock. -/
def gaussGammaSixSuspensionTraceEnergy
    (m : ℕ) (p : Nat.Primes) (t : ℝ) : ℝ :=
  gaussReciprocalCharacterWeight m p *
    sourceHorizontalGammaSixSuspensionTraceEnergy
      (Real.log (p : ℝ) * t)

theorem gaussGammaSixSuspensionTraceEnergy_eq_pairedBoundaryEnergy
    (m : ℕ) (p : Nat.Primes) (t : ℝ) :
    gaussGammaSixSuspensionTraceEnergy m p t =
      gaussGammaSixPairedBoundaryEnergy m p t := by
  rw [gaussGammaSixSuspensionTraceEnergy,
    sourceHorizontalGammaSixSuspensionTraceEnergy_eq_curvature,
    gaussGammaSixPairedBoundaryEnergy,
    sourceHorizontalGammaSixPrimeClockPairedBoundaryEnergy]

/-- Gauss Hodge mass is the Euler response of ordinary curvature trace of the literal curved
Gamma-six suspension. -/
theorem gaussHodgeMassCurrent_eq_euler_gaussGammaSixSuspensionTraceEnergy
    (m : ℕ) (q : XiZeroCopy) (p : Nat.Primes) :
    gaussHodgeMassCurrent m q p =
      primeDepthBVWoldXiCenteredRate q.1 *
        deriv (gaussGammaSixSuspensionTraceEnergy m p)
          (primeDepthBVWoldXiCenteredRate q.1) := by
  have hfun : gaussGammaSixSuspensionTraceEnergy m p =
      gaussGammaSixPairedBoundaryEnergy m p := by
    funext t
    exact gaussGammaSixSuspensionTraceEnergy_eq_pairedBoundaryEnergy m p t
  rw [hfun]
  exact gaussHodgeMassCurrent_eq_euler_gaussGammaSixPairedBoundaryEnergy m q p

/-- Determinant Frankenstein law: Gauss Hodge mass is the Euler derivative of the literal
prime-clock suspension determinant, with the exact Gauss residue/Fisher coefficient. -/
theorem gaussHodgeMassCurrent_eq_euler_gaussGammaSixSuspensionDeterminant
    (m : ℕ) (q : XiZeroCopy) (p : Nat.Primes) :
    gaussHodgeMassCurrent m q p =
      primeDepthBVWoldXiCenteredRate q.1 *
        deriv (fun t : ℝ =>
          gaussReciprocalCharacterWeight m p *
            (Matrix.det (sourceHorizontalGammaSixCurvedSuspension
              (Real.log (p : ℝ) * t))).re)
          (primeDepthBVWoldXiCenteredRate q.1) := by
  have hfun : (fun t : ℝ =>
      gaussReciprocalCharacterWeight m p *
        (Matrix.det (sourceHorizontalGammaSixCurvedSuspension
          (Real.log (p : ℝ) * t))).re) =
      gaussGammaSixSuspensionTraceEnergy m p := by
    funext t
    rw [gaussGammaSixSuspensionTraceEnergy,
      sourceHorizontalGammaSixSuspensionTraceEnergy_eq_re_det]
  rw [hfun]
  exact gaussHodgeMassCurrent_eq_euler_gaussGammaSixSuspensionTraceEnergy m q p

/-- At every prime clock, flatness of the literal two-orientation suspension is exactly placement
of the Xi divisor copy on the critical line. -/
theorem sourceHorizontalGammaSixPrimePhysicalCurvedSuspension_sq_eq_zero_iff
    (q : XiZeroCopy) (p : Nat.Primes) :
    sourceHorizontalGammaSixCurvedSuspension
          (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate q.1) *
        sourceHorizontalGammaSixCurvedSuspension
          (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate q.1) = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [sourceHorizontalGammaSixCurvedSuspension_sq_eq_zero_iff]
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.prop.one_lt)).ne'
  constructor
  · intro h
    exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).1
      ((mul_eq_zero.mp h).resolve_left hlog)
  · intro hline
    rw [(primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).2 hline, mul_zero]

/-- Fixed-prime global flatness of the coefficient-faithful two-orientation suspension. -/
def SourceHorizontalGammaSixPhysicalSuspensionsFlat (p : Nat.Primes) : Prop :=
  ∀ q : XiZeroCopy,
    sourceHorizontalGammaSixCurvedSuspension
          (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate q.1) *
        sourceHorizontalGammaSixCurvedSuspension
          (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate q.1) = 0

/-- Curved-to-flat suspension endpoint: at any retained prime label, the actual two-orientation
source is an honest complex for every Xi multiplicity copy exactly when RH holds. -/
theorem sourceHorizontalGammaSixPhysicalSuspensionsFlat_iff_riemannHypothesis
    (p : Nat.Primes) :
    SourceHorizontalGammaSixPhysicalSuspensionsFlat p ↔ RiemannHypothesis := by
  constructor
  · intro hflat
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have hline :=
      (sourceHorizontalGammaSixPrimePhysicalCurvedSuspension_sq_eq_zero_iff q p).1
        (hflat q)
    refine ⟨(q.1 : ℂ).im, ?_⟩
    apply Complex.ext
    · simp [xiSpectralPoint]
    · simp [xiSpectralPoint, hline]
  · intro hRH q
    apply (sourceHorizontalGammaSixPrimePhysicalCurvedSuspension_sq_eq_zero_iff q p).2
    exact xi_divisor_support_re_eq_half_of_rh hRH q.1

end

end RHTower
