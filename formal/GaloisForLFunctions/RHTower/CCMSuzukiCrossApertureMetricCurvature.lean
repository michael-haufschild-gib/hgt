import GaloisForLFunctions.RHTower.CCMSuzukiCrossApertureRieszTransport

/-!
# Curvature of source-faithful Suzuki aperture transport

The raw Suzuki forcing is identical on each retained form block, but the coercive Riesz metric
changes with the aperture.  Its exact correction is therefore an affine connection, not an error
to discard.  This module proves that aperture extension is additive after the canonical physical
identification and records the resulting three-aperture curvature law for the literal
metric-renormalized shell.  No sign, convergence, or RH premise enters.
-/

open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- Aperture extension is transitive after identifying the physical form value; the chosen
subtype representatives carry no additional transport data. -/
theorem ccmArchimedeanFormDomain_extension_trans
    {a b c : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (hbc : b.1 ≤ c.1)
    (u : CCMArchimedeanFormDomain a) :
    ccmArchimedeanFormDomain_extension hbc
        (ccmArchimedeanFormDomain_extension hab u) =
      ccmArchimedeanFormDomain_extension (hab.trans hbc) u := by
  apply Subtype.ext
  rw [ccmArchimedeanFormDomain_extension_val,
    ccmArchimedeanFormDomain_extension_val,
    ccmArchimedeanFormDomain_extension_val]

/-- Aperture extension preserves physical addition exactly. -/
theorem ccmArchimedeanFormDomain_extension_add
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    (u v : CCMArchimedeanFormDomain a) :
    ccmArchimedeanFormDomain_extension hab (u + v) =
      ccmArchimedeanFormDomain_extension hab u +
        ccmArchimedeanFormDomain_extension hab v := by
  apply Subtype.ext
  rw [ccmArchimedeanFormDomain_extension_val hab (u + v)]
  change u.1 + v.1 =
    (ccmArchimedeanFormDomain_extension hab u).1 +
      (ccmArchimedeanFormDomain_extension hab v).1
  rw [ccmArchimedeanFormDomain_extension_val hab u,
    ccmArchimedeanFormDomain_extension_val hab v]

/-- Aperture extension preserves physical subtraction exactly. -/
theorem ccmArchimedeanFormDomain_extension_sub
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    (u v : CCMArchimedeanFormDomain a) :
    ccmArchimedeanFormDomain_extension hab (u - v) =
      ccmArchimedeanFormDomain_extension hab u -
        ccmArchimedeanFormDomain_extension hab v := by
  apply Subtype.ext
  rw [ccmArchimedeanFormDomain_extension_val hab (u - v)]
  change u.1 - v.1 =
    (ccmArchimedeanFormDomain_extension hab u).1 -
      (ccmArchimedeanFormDomain_extension hab v).1
  rw [ccmArchimedeanFormDomain_extension_val hab u,
    ccmArchimedeanFormDomain_extension_val hab v]

/-- Curvature of the exact coercive-metric correction along a three-aperture chain.  It is a
pre-scalar source vector, so the completed prime--polar--Gamma cancellation remains intact. -/
def suzukiTaRiesz_metricCurvature
    {a b c : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (hbc : b.1 ≤ c.1)
    (eps : ℝ) : CCMArchimedeanFormDomain c :=
  ccmArchimedeanFormDomain_extension hbc
      (suzukiTaRiesz_metricShiftCorrection hab eps) +
    suzukiTaRiesz_metricShiftCorrection hbc eps -
      suzukiTaRiesz_metricShiftCorrection (hab.trans hbc) eps

/-- Exact affine cocycle law for literal metric-renormalized Suzuki shells.  A two-step boundary
transport differs from direct transport precisely by `suzukiTaRiesz_metricCurvature`; no shell,
prime, polar, or Gamma contribution has been bounded or omitted. -/
theorem suzukiTaRiesz_metricRenormalizedShell_cocycle
    {a b c : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (hbc : b.1 ≤ c.1)
    (eps : ℝ) :
    suzukiTaRiesz_metricRenormalizedShell (hab.trans hbc) eps =
      suzukiTaRiesz_metricRenormalizedShell hbc eps +
        ccmArchimedeanFormDomain_extension hbc
          (suzukiTaRiesz_metricRenormalizedShell hab eps) +
        suzukiTaRiesz_metricCurvature hab hbc eps := by
  have hext :
      ccmArchimedeanFormDomain_extension (hab.trans hbc)
          (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps)) =
        ccmArchimedeanFormDomain_extension hbc
          (ccmArchimedeanFormDomain_extension hab
            (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps))) :=
    (ccmArchimedeanFormDomain_extension_trans hab hbc _).symm
  rw [suzukiTaRiesz_metricRenormalizedShell,
    suzukiTaRiesz_metricRenormalizedShell,
    suzukiTaRiesz_metricRenormalizedShell, hext]
  unfold suzukiTaRiesz_metricCurvature
  rw [ccmArchimedeanFormDomain_extension_sub,
    ccmArchimedeanFormDomain_extension_sub]
  abel

/-- In common whole-line source coordinates, curvature is exactly the signed mismatch of the
three literal covariance metric responses.  This is the pre-scalar boundary charge that a
convergence argument must control; no sign or norm estimate is inserted. -/
theorem suzukiTaRiesz_metricCurvature_physical_eq
    {a b c : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (hbc : b.1 ≤ c.1)
    (eps : ℝ) :
    suzukiApertureZeroExtendL2
      (suzukiWeilIntervalFormEmbedding c
        (suzukiTaRiesz_metricCurvature hab hbc eps)) =
      suzukiApertureZeroExtendL2
        (suzukiWeilIntervalFormEmbedding b
          (suzukiTaRiesz_metricShiftCorrection hab eps)) +
        suzukiApertureZeroExtendL2
          (suzukiWeilIntervalFormEmbedding c
            (suzukiTaRiesz_metricShiftCorrection hbc eps)) -
          suzukiApertureZeroExtendL2
            (suzukiWeilIntervalFormEmbedding c
              (suzukiTaRiesz_metricShiftCorrection (hab.trans hbc) eps)) := by
  unfold suzukiTaRiesz_metricCurvature
  rw [map_sub, map_add]
  rw [show (suzukiWeilIntervalFormEmbedding c
      (ccmArchimedeanFormDomain_extension hbc
        (suzukiTaRiesz_metricShiftCorrection hab eps)) +
      suzukiWeilIntervalFormEmbedding c
        (suzukiTaRiesz_metricShiftCorrection hbc eps) -
      suzukiWeilIntervalFormEmbedding c
        (suzukiTaRiesz_metricShiftCorrection (hab.trans hbc) eps)) =
      suzukiWeilIntervalFormEmbedding c
        (ccmArchimedeanFormDomain_extension hbc
          (suzukiTaRiesz_metricShiftCorrection hab eps)) +
        suzukiWeilIntervalFormEmbedding c
          (suzukiTaRiesz_metricShiftCorrection hbc eps) +
        (-1 : ℂ) • suzukiWeilIntervalFormEmbedding c
          (suzukiTaRiesz_metricShiftCorrection (hab.trans hbc) eps) by module]
  rw [suzukiApertureZeroExtendL2_add, suzukiApertureZeroExtendL2_add,
    suzukiApertureZeroExtendL2_smul,
    suzukiApertureZeroExtendL2_formEmbedding_extension_eq hbc]
  module

/-- Opposite movable completed sources are related by literal whole-line reflection. -/
theorem l2Reflection_suzukiTaMovableCompletedCovarianceSource
    (a : SuzukiPositiveAperture) (eps : ℝ) :
    l2Reflection (suzukiTaMovableCompletedCovarianceSource a eps) =
      suzukiTaMovableCompletedCovarianceSource a (-eps) := by
  rw [suzukiTaMovableCompletedCovarianceSource_eq_rawDeficiency,
    suzukiTaMovableCompletedCovarianceSource_eq_rawDeficiency,
    suzukiTaPhysicalEmbedding_rawDeficiency_reflection,
    suzukiApertureZeroExtendL2_intervalReflection]

/-- The input to the coercive metric response has exact aperture-reflection covariance. -/
theorem suzukiTaRiesz_metricShiftInput_reflection
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (eps : ℝ) :
    suzukiWeilIntervalReflection b
      (suzukiWeilIntervalFormEmbedding b
        (ccmArchimedeanFormDomain_extension hab
          (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps)))) =
      suzukiWeilIntervalFormEmbedding b
        (ccmArchimedeanFormDomain_extension hab
          (suzukiTaToFormCLM a (suzukiTaRawDeficiency a (-eps))) ) := by
  apply suzukiApertureZeroExtendL2_injective
  rw [suzukiApertureZeroExtendL2_intervalReflection,
    suzukiApertureZeroExtendL2_formEmbedding_extension_eq hab,
    suzukiApertureZeroExtendL2_formEmbedding_extension_eq hab]
  change l2Reflection
      (suzukiApertureZeroExtendL2
        (suzukiTaPhysicalEmbedding a (suzukiTaRawDeficiency a eps))) =
    suzukiApertureZeroExtendL2
      (suzukiTaPhysicalEmbedding a (suzukiTaRawDeficiency a (-eps)))
  rw [← suzukiTaMovableCompletedCovarianceSource_eq_rawDeficiency,
    ← suzukiTaMovableCompletedCovarianceSource_eq_rawDeficiency]
  exact l2Reflection_suzukiTaMovableCompletedCovarianceSource a eps

/-- Reflection transports literal coercive-metric correction to its opposite movable source. -/
theorem l2Reflection_suzukiTaRiesz_metricShiftCorrection
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (eps : ℝ) :
    l2Reflection
      (suzukiApertureZeroExtendL2
        (suzukiWeilIntervalFormEmbedding b
          (suzukiTaRiesz_metricShiftCorrection hab eps))) =
      suzukiApertureZeroExtendL2
        (suzukiWeilIntervalFormEmbedding b
          (suzukiTaRiesz_metricShiftCorrection hab (-eps))) := by
  rw [suzukiWeilIntervalFormEmbedding_metricShiftCorrection_eq_covariance,
    suzukiApertureZeroExtendL2_smul, map_smul,
    suzukiWeilIntervalFormEmbedding_metricShiftCorrection_eq_covariance,
    suzukiApertureZeroExtendL2_smul]
  congr 1
  rw [← suzukiApertureZeroExtendL2_intervalReflection,
    ← suzukiWeilIntervalCovariance_reflection,
    suzukiTaRiesz_metricShiftInput_reflection]

/-- Curvature at opposite movable sources is related by common whole-line reflection exactly.
This pairs the two signed channels but does not assert that either is zero or small. -/
theorem l2Reflection_suzukiTaRiesz_metricCurvature
    {a b c : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (hbc : b.1 ≤ c.1)
    (eps : ℝ) :
    l2Reflection
      (suzukiApertureZeroExtendL2
        (suzukiWeilIntervalFormEmbedding c
          (suzukiTaRiesz_metricCurvature hab hbc eps))) =
      suzukiApertureZeroExtendL2
        (suzukiWeilIntervalFormEmbedding c
          (suzukiTaRiesz_metricCurvature hab hbc (-eps))) := by
  rw [suzukiTaRiesz_metricCurvature_physical_eq,
    map_sub, map_add,
    suzukiTaRiesz_metricCurvature_physical_eq,
    l2Reflection_suzukiTaRiesz_metricShiftCorrection hab eps,
    l2Reflection_suzukiTaRiesz_metricShiftCorrection hbc eps,
    l2Reflection_suzukiTaRiesz_metricShiftCorrection (hab.trans hbc) eps]

end RHTower
