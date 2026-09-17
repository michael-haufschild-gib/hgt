import GaloisForLFunctions.RHTower.CCMSuzukiCrossApertureForcingTransport

/-!
# Retained-block transport of the literal Suzuki Riesz equation

The completed form and the literal exponential forcing are both invariant on a retained form
block.  This module transports the actual finite Suzuki Riesz equation itself.  It exposes the
inverse metric as the only retained-block discrepancy; no positive estimate or replacement source
is introduced.
-/

open scoped InnerProductSpace

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- The canonical larger-aperture representative of a retained form vector.  This is a literal
subtype change only; it is deliberately not packaged as an auxiliary covariance. -/
def ccmArchimedeanFormDomain_extension
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    (u : CCMArchimedeanFormDomain a) : CCMArchimedeanFormDomain b :=
  (exists_ccmArchimedeanFormDomain_extension hab u).choose

@[simp] theorem ccmArchimedeanFormDomain_extension_val
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    (u : CCMArchimedeanFormDomain a) :
    (ccmArchimedeanFormDomain_extension hab u).1 = u.1 :=
  (exists_ccmArchimedeanFormDomain_extension hab u).choose_spec

/-- Weak literal Riesz equation for Suzuki's actual raw deficiency. -/
theorem inner_suzukiTaRiesz_rawDeficiency_eq_exponential
    (a : SuzukiPositiveAperture) (eps : ℝ) (v : CCMArchimedeanFormDomain a) :
    inner ℂ
      (boundedPerturbedFormRiesz
        (suzukiWeilIntervalFormEmbedding a)
        (suzukiWeilIntervalBoundedRemainder a)
        (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps))) v =
      inner ℂ (suzukiTaExponentialL2 a eps)
        (suzukiWeilIntervalFormEmbedding a v) := by
  let J := suzukiWeilIntervalFormEmbedding a
  let B := suzukiWeilIntervalBoundedRemainder a
  let hB := suzukiWeilIntervalBoundedRemainder_isSelfAdjoint a
  let R := boundedPerturbedFormRiesz J B
  let Rinv := boundedPerturbedFormRieszInv J B hB
  have hdef := suzukiTaToFormCLM_rawDeficiency_eq_rieszInv a eps
  change inner ℂ (R (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps))) v =
    inner ℂ (suzukiTaExponentialL2 a eps) (J v)
  rw [hdef]
  change inner ℂ (R (Rinv (J.adjoint (suzukiTaExponentialL2 a eps)))) v = _
  have hRinv : R (Rinv (J.adjoint (suzukiTaExponentialL2 a eps))) =
      J.adjoint (suzukiTaExponentialL2 a eps) := by
    change (boundedPerturbedFormRieszEquiv J B hB)
      ((boundedPerturbedFormRieszEquiv J B hB).symm
        (J.adjoint (suzukiTaExponentialL2 a eps))) = _
    exact (boundedPerturbedFormRieszEquiv J B hB).apply_symm_apply _
  rw [hRinv]
  rw [J.adjoint_inner_left]

/-- On every retained test vector, the two actual Suzuki Riesz equations have identical right
side.  New forcing can therefore enter only through shell test vectors. -/
theorem inner_suzukiTaRiesz_rawDeficiency_oldBlock_eq
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (eps : ℝ)
    (v : CCMArchimedeanFormDomain a) :
    inner ℂ
      (boundedPerturbedFormRiesz
        (suzukiWeilIntervalFormEmbedding b)
        (suzukiWeilIntervalBoundedRemainder b)
        (suzukiTaToFormCLM b (suzukiTaRawDeficiency b eps)))
      (ccmArchimedeanFormDomain_extension hab v) =
      inner ℂ
        (boundedPerturbedFormRiesz
          (suzukiWeilIntervalFormEmbedding a)
          (suzukiWeilIntervalBoundedRemainder a)
          (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps))) v := by
  rw [inner_suzukiTaRiesz_rawDeficiency_eq_exponential,
    inner_suzukiTaRiesz_rawDeficiency_eq_exponential]
  exact inner_suzukiTaExponential_formEmbedding_eq_of_val_eq hab eps
    (ccmArchimedeanFormDomain_extension_val hab v)

/-- Interval form embeddings preserve their mixed physical pairing on every retained pair. -/
theorem inner_suzukiWeilIntervalFormEmbedding_eq_of_val_eq
    {a b : SuzukiPositiveAperture}
    {u w : CCMArchimedeanFormDomain a} {v x : CCMArchimedeanFormDomain b}
    (hvu : v.1 = u.1) (hxw : x.1 = w.1) :
    inner ℂ (suzukiWeilIntervalFormEmbedding b v)
      (suzukiWeilIntervalFormEmbedding b x) =
      inner ℂ (suzukiWeilIntervalFormEmbedding a u)
        (suzukiWeilIntervalFormEmbedding a w) := by
  have hphysical : ∀ (d : SuzukiPositiveAperture) (z : CCMArchimedeanFormDomain d),
      suzukiApertureZeroExtendL2 (suzukiWeilIntervalFormEmbedding d z) =
        (ccmArchimedeanFormToAperture d z : SoninL2) := by
    intro d z
    change ((suzukiApertureL2Equiv d)
      ((suzukiApertureL2Equiv d).symm (ccmArchimedeanFormToAperture d z)) : SoninL2) =
        (ccmArchimedeanFormToAperture d z : SoninL2)
    rw [(suzukiApertureL2Equiv d).apply_symm_apply]
  rw [← inner_suzukiApertureZeroExtendL2,
    ← inner_suzukiApertureZeroExtendL2, hphysical b v, hphysical b x,
    hphysical a u, hphysical a w,
    ccmArchimedeanFormToAperture_coe_eq_of_val_eq hvu,
    ccmArchimedeanFormToAperture_coe_eq_of_val_eq hxw]

/-- The canonical finite Riesz operator is the literal completed form plus its exact coercive
shift on every mixed matrix coefficient. -/
theorem inner_suzukiWeilIntervalRiesz_eq_ccmRestrictedWeilForm_add_shift
    (a : SuzukiPositiveAperture) (u v : CCMArchimedeanFormDomain a) :
    inner ℂ
      (boundedPerturbedFormRiesz
        (suzukiWeilIntervalFormEmbedding a)
        (suzukiWeilIntervalBoundedRemainder a) u) v =
      ccmRestrictedWeilForm a u v +
        (boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) : ℂ) *
          inner ℂ (suzukiWeilIntervalFormEmbedding a u)
            (suzukiWeilIntervalFormEmbedding a v) := by
  let J := suzukiWeilIntervalFormEmbedding a
  let B := suzukiWeilIntervalBoundedRemainder a
  let s := boundedPerturbedFormShift B
  change inner ℂ (boundedPerturbedFormRiesz J B u) v =
    ccmRestrictedWeilForm a u v + (s : ℂ) * inner ℂ (J u) (J v)
  rw [← suzukiWeilIntervalForm_eq_ccmRestrictedWeilForm]
  change inner ℂ (boundedPerturbedFormRiesz J B u) v =
    (inner ℂ u v + inner ℂ (B (J u)) (J v)) + (s : ℂ) * inner ℂ (J u) (J v)
  rw [boundedPerturbedFormRiesz_apply, inner_add_left, inner_add_left,
    inner_smul_left, J.adjoint_inner_left, J.adjoint_inner_left]
  simp only [Complex.conj_ofReal]
  ring

/-- Exact old-block equation for actual Suzuki deficiencies in completed source coordinates. -/
theorem suzukiTaRiesz_rawDeficiency_oldBlock_formEquation
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (eps : ℝ)
    (v : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilForm b
        (suzukiTaToFormCLM b (suzukiTaRawDeficiency b eps))
        (ccmArchimedeanFormDomain_extension hab v) +
      (boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder b) : ℂ) *
        inner ℂ
          (suzukiWeilIntervalFormEmbedding b
            (suzukiTaToFormCLM b (suzukiTaRawDeficiency b eps)))
          (suzukiWeilIntervalFormEmbedding b
            (ccmArchimedeanFormDomain_extension hab v)) =
      ccmRestrictedWeilForm a
          (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps)) v +
        (boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) : ℂ) *
          inner ℂ
            (suzukiWeilIntervalFormEmbedding a
              (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps)))
            (suzukiWeilIntervalFormEmbedding a v) := by
  rw [← inner_suzukiWeilIntervalRiesz_eq_ccmRestrictedWeilForm_add_shift,
    ← inner_suzukiWeilIntervalRiesz_eq_ccmRestrictedWeilForm_add_shift]
  exact inner_suzukiTaRiesz_rawDeficiency_oldBlock_eq hab eps v

/-- After the literal old response is transported, its entire retained-block residual is the
difference of the two canonical coercive shifts.  Prime, polar, and Gamma terms stay inside the
single completed form throughout; no shell term has been bounded or discarded. -/
theorem suzukiTaRiesz_rawDeficiency_oldBlock_residual
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (eps : ℝ)
    (v : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilForm b
        (suzukiTaToFormCLM b (suzukiTaRawDeficiency b eps) -
          ccmArchimedeanFormDomain_extension hab
            (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps)))
        (ccmArchimedeanFormDomain_extension hab v) +
      (boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder b) : ℂ) *
        inner ℂ
          (suzukiWeilIntervalFormEmbedding b
            (suzukiTaToFormCLM b (suzukiTaRawDeficiency b eps) -
              ccmArchimedeanFormDomain_extension hab
                (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps))))
          (suzukiWeilIntervalFormEmbedding b
            (ccmArchimedeanFormDomain_extension hab v)) =
      ((boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) -
        boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder b) : ℝ) : ℂ) *
        inner ℂ
          (suzukiWeilIntervalFormEmbedding a
            (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps)))
          (suzukiWeilIntervalFormEmbedding a v) := by
  have hform := ccmRestrictedWeilForm_eq_of_val_eq hab
    (ccmArchimedeanFormDomain_extension_val hab
      (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps)))
    (ccmArchimedeanFormDomain_extension_val hab v)
  have hinner := inner_suzukiWeilIntervalFormEmbedding_eq_of_val_eq
    (ccmArchimedeanFormDomain_extension_val hab
      (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps)))
    (ccmArchimedeanFormDomain_extension_val hab v)
  rw [show ccmRestrictedWeilForm b
      (suzukiTaToFormCLM b (suzukiTaRawDeficiency b eps) -
        ccmArchimedeanFormDomain_extension hab
          (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps)))
      (ccmArchimedeanFormDomain_extension hab v) =
      ccmRestrictedWeilForm b
        (suzukiTaToFormCLM b (suzukiTaRawDeficiency b eps))
        (ccmArchimedeanFormDomain_extension hab v) -
      ccmRestrictedWeilForm b
        (ccmArchimedeanFormDomain_extension hab
          (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps)))
        (ccmArchimedeanFormDomain_extension hab v) by
      simp [ccmRestrictedWeilForm, map_sub]
      ring,
    map_sub, inner_sub_left]
  have hweak := suzukiTaRiesz_rawDeficiency_oldBlock_formEquation hab eps v
  have hshift :
      ((boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) -
        boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder b) : ℝ) : ℂ) =
        (boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) : ℂ) -
          (boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder b) : ℂ) := by
    norm_cast
  rw [hshift]
  linear_combination hweak - hform -
    (boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder b) : ℂ) * hinner

/-- Explicit correction carrying the entire change of canonical coercive metric into the larger
literal Riesz problem.  It is built from the actual transported covariance response, before any
scalar reporter is formed. -/
def suzukiTaRiesz_metricShiftCorrection
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (eps : ℝ) :
    CCMArchimedeanFormDomain b :=
  ((boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) -
    boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder b) : ℝ) : ℂ) •
    boundedPerturbedFormRieszInv
      (suzukiWeilIntervalFormEmbedding b)
      (suzukiWeilIntervalBoundedRemainder b)
      (suzukiWeilIntervalBoundedRemainder_isSelfAdjoint b)
      ((suzukiWeilIntervalFormEmbedding b).adjoint
        (suzukiWeilIntervalFormEmbedding b
          (ccmArchimedeanFormDomain_extension hab
            (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps)))))

/-- The metric correction represents exactly the signed shift charge on a retained test vector. -/
theorem inner_suzukiTaRiesz_metricShiftCorrection
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (eps : ℝ)
    (v : CCMArchimedeanFormDomain a) :
    inner ℂ
      (boundedPerturbedFormRiesz
        (suzukiWeilIntervalFormEmbedding b)
        (suzukiWeilIntervalBoundedRemainder b)
        (suzukiTaRiesz_metricShiftCorrection hab eps))
      (ccmArchimedeanFormDomain_extension hab v) =
      ((boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) -
        boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder b) : ℝ) : ℂ) *
        inner ℂ
          (suzukiWeilIntervalFormEmbedding b
            (ccmArchimedeanFormDomain_extension hab
              (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps))))
          (suzukiWeilIntervalFormEmbedding b
            (ccmArchimedeanFormDomain_extension hab v)) := by
  let J := suzukiWeilIntervalFormEmbedding b
  let B := suzukiWeilIntervalBoundedRemainder b
  let hB := suzukiWeilIntervalBoundedRemainder_isSelfAdjoint b
  let R := boundedPerturbedFormRiesz J B
  let Rinv := boundedPerturbedFormRieszInv J B hB
  let delta : ℝ := boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) -
    boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder b)
  let u0 := ccmArchimedeanFormDomain_extension hab
    (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps))
  let p := J.adjoint (J u0)
  let v0 := ccmArchimedeanFormDomain_extension hab v
  change inner ℂ (R ((delta : ℂ) • Rinv p)) v0 =
    (delta : ℂ) * inner ℂ (J u0) (J v0)
  have hRinv : R (Rinv p) = p := by
    change (boundedPerturbedFormRieszEquiv J B hB)
      ((boundedPerturbedFormRieszEquiv J B hB).symm p) = _
    exact (boundedPerturbedFormRieszEquiv J B hB).apply_symm_apply _
  calc
    _ = inner ℂ ((delta : ℂ) • R (Rinv p)) v0 := by rw [map_smul]
    _ = (delta : ℂ) * inner ℂ (R (Rinv p)) v0 := by
      simpa only [Complex.conj_ofReal] using
        (inner_smul_left (R (Rinv p)) v0 (delta : ℂ))
    _ = _ := by
      rw [hRinv]
      simp only [p]
      rw [J.adjoint_inner_left]

/-- After the explicit metric correction, the actual aperture difference is Riesz-orthogonal to
every retained test vector.  This is an exact shell isolation, not a convergence estimate. -/
theorem inner_suzukiTaRiesz_metricRenormalized_oldBlock_eq_zero
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (eps : ℝ)
    (v : CCMArchimedeanFormDomain a) :
    inner ℂ
      (boundedPerturbedFormRiesz
        (suzukiWeilIntervalFormEmbedding b)
        (suzukiWeilIntervalBoundedRemainder b)
        (suzukiTaToFormCLM b (suzukiTaRawDeficiency b eps) -
          ccmArchimedeanFormDomain_extension hab
            (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps)) -
          suzukiTaRiesz_metricShiftCorrection hab eps))
      (ccmArchimedeanFormDomain_extension hab v) = 0 := by
  have hres :
      inner ℂ
        (boundedPerturbedFormRiesz
          (suzukiWeilIntervalFormEmbedding b)
          (suzukiWeilIntervalBoundedRemainder b)
          (suzukiTaToFormCLM b (suzukiTaRawDeficiency b eps) -
            ccmArchimedeanFormDomain_extension hab
              (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps))))
        (ccmArchimedeanFormDomain_extension hab v) =
      ((boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) -
        boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder b) : ℝ) : ℂ) *
        inner ℂ
          (suzukiWeilIntervalFormEmbedding a
            (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps)))
          (suzukiWeilIntervalFormEmbedding a v) := by
    rw [inner_suzukiWeilIntervalRiesz_eq_ccmRestrictedWeilForm_add_shift]
    exact suzukiTaRiesz_rawDeficiency_oldBlock_residual hab eps v
  have hmetric := inner_suzukiTaRiesz_metricShiftCorrection hab eps v
  have hinner := inner_suzukiWeilIntervalFormEmbedding_eq_of_val_eq
    (ccmArchimedeanFormDomain_extension_val hab
      (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps)))
    (ccmArchimedeanFormDomain_extension_val hab v)
  rw [hinner] at hmetric
  rw [map_sub, inner_sub_left, hres, hmetric, sub_self]

/-- The exact pre-scalar aperture residual after removal of the unique retained-block metric
charge.  Its two leading terms are the literal completed covariance responses at the two
apertures; no positive or scalarized replacement is used. -/
def suzukiTaRiesz_metricRenormalizedShell
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (eps : ℝ) :
    CCMArchimedeanFormDomain b :=
  suzukiTaToFormCLM b (suzukiTaRawDeficiency b eps) -
    ccmArchimedeanFormDomain_extension hab
      (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps)) -
    suzukiTaRiesz_metricShiftCorrection hab eps

/-- The metric-renormalized shell is exactly Riesz-orthogonal to every retained form test. -/
theorem inner_suzukiTaRiesz_metricRenormalizedShell_oldBlock_eq_zero
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (eps : ℝ)
    (v : CCMArchimedeanFormDomain a) :
    inner ℂ
      (boundedPerturbedFormRiesz
        (suzukiWeilIntervalFormEmbedding b)
        (suzukiWeilIntervalBoundedRemainder b)
        (suzukiTaRiesz_metricRenormalizedShell hab eps))
      (ccmArchimedeanFormDomain_extension hab v) = 0 := by
  simpa only [suzukiTaRiesz_metricRenormalizedShell] using
    inner_suzukiTaRiesz_metricRenormalized_oldBlock_eq_zero hab eps v

/-- Zero-extending a retained form vector commutes exactly with aperture extension. -/
theorem suzukiApertureZeroExtendL2_formEmbedding_extension_eq
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    (u : CCMArchimedeanFormDomain a) :
    suzukiApertureZeroExtendL2
      (suzukiWeilIntervalFormEmbedding b
        (ccmArchimedeanFormDomain_extension hab u)) =
      suzukiApertureZeroExtendL2 (suzukiWeilIntervalFormEmbedding a u) := by
  have hphysical : ∀ (d : SuzukiPositiveAperture) (z : CCMArchimedeanFormDomain d),
      suzukiApertureZeroExtendL2 (suzukiWeilIntervalFormEmbedding d z) =
        (ccmArchimedeanFormToAperture d z : SoninL2) := by
    intro d z
    change ((suzukiApertureL2Equiv d)
      ((suzukiApertureL2Equiv d).symm (ccmArchimedeanFormToAperture d z)) : SoninL2) =
        (ccmArchimedeanFormToAperture d z : SoninL2)
    rw [(suzukiApertureL2Equiv d).apply_symm_apply]
  rw [hphysical b, hphysical a,
    ccmArchimedeanFormToAperture_coe_eq_of_val_eq
      (ccmArchimedeanFormDomain_extension_val hab u)]

/-- The explicit metric correction has an exact physical realization: covariance at the larger
aperture applied to the transported old completed response. -/
theorem suzukiWeilIntervalFormEmbedding_metricShiftCorrection_eq_covariance
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (eps : ℝ) :
    suzukiWeilIntervalFormEmbedding b
      (suzukiTaRiesz_metricShiftCorrection hab eps) =
      ((boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) -
        boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder b) : ℝ) : ℂ) •
        suzukiWeilIntervalCovariance b
          (suzukiWeilIntervalFormEmbedding b
            (ccmArchimedeanFormDomain_extension hab
              (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps)))) := by
  rw [suzukiTaRiesz_metricShiftCorrection, suzukiWeilIntervalCovariance,
    boundedPerturbedFormCovariance]
  simp only [ContinuousLinearMap.comp_apply, map_smul]

/-- **Literal source-coordinate shell identity.**  After exact retained-block cancellation,
the physical residual is the larger completed covariance response minus the transported smaller
one, less precisely the metric-response required by the changed coercive Riesz geometry.  This
is the sole object whose paired `eps = ±1` cofinal control can advance Suzuki convergence. -/
theorem suzukiTaRiesz_metricRenormalizedShell_physical_eq
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (eps : ℝ) :
    suzukiApertureZeroExtendL2
      (suzukiWeilIntervalFormEmbedding b
        (suzukiTaRiesz_metricRenormalizedShell hab eps)) =
      suzukiTaMovableCompletedCovarianceSource b eps -
        suzukiTaMovableCompletedCovarianceSource a eps -
        ((boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) -
          boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder b) : ℝ) : ℂ) •
          suzukiApertureZeroExtendL2
            (suzukiWeilIntervalCovariance b
              (suzukiWeilIntervalFormEmbedding b
                (ccmArchimedeanFormDomain_extension hab
                  (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps))))) := by
  have hnew (d : SuzukiPositiveAperture) :
      suzukiApertureZeroExtendL2
        (suzukiWeilIntervalFormEmbedding d
          (suzukiTaToFormCLM d (suzukiTaRawDeficiency d eps))) =
        suzukiTaMovableCompletedCovarianceSource d eps := by
    have hphysical :
        suzukiApertureZeroExtendL2
          (suzukiWeilIntervalFormEmbedding d
            (suzukiTaToFormCLM d (suzukiTaRawDeficiency d eps))) =
          (ccmArchimedeanFormToAperture d
            (suzukiTaToFormCLM d (suzukiTaRawDeficiency d eps)) : SoninL2) := by
      change ((suzukiApertureL2Equiv d)
        ((suzukiApertureL2Equiv d).symm
          (ccmArchimedeanFormToAperture d
            (suzukiTaToFormCLM d (suzukiTaRawDeficiency d eps)))) : SoninL2) = _
      rw [(suzukiApertureL2Equiv d).apply_symm_apply]
    rw [hphysical]
    exact ccmArchimedeanFormToAperture_movableCompletedCovarianceCCMResponse_eq_source d eps
  have hold :
      suzukiApertureZeroExtendL2
        (suzukiWeilIntervalFormEmbedding b
          (ccmArchimedeanFormDomain_extension hab
            (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps)))) =
        suzukiTaMovableCompletedCovarianceSource a eps := by
    rw [suzukiApertureZeroExtendL2_formEmbedding_extension_eq hab]
    exact hnew a
  have hcorrection :
      suzukiApertureZeroExtendL2
        (suzukiWeilIntervalFormEmbedding b
          (suzukiTaRiesz_metricShiftCorrection hab eps)) =
        ((boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) -
          boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder b) : ℝ) : ℂ) •
          suzukiApertureZeroExtendL2
            (suzukiWeilIntervalCovariance b
              (suzukiWeilIntervalFormEmbedding b
                (ccmArchimedeanFormDomain_extension hab
                  (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps))))) := by
    rw [suzukiWeilIntervalFormEmbedding_metricShiftCorrection_eq_covariance,
      suzukiApertureZeroExtendL2_smul]
  unfold suzukiTaRiesz_metricRenormalizedShell
  rw [map_sub, map_sub]
  rw [show (suzukiWeilIntervalFormEmbedding b
      (suzukiTaToFormCLM b (suzukiTaRawDeficiency b eps)) -
      suzukiWeilIntervalFormEmbedding b
        (ccmArchimedeanFormDomain_extension hab
          (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps))) -
      suzukiWeilIntervalFormEmbedding b
        (suzukiTaRiesz_metricShiftCorrection hab eps)) =
      suzukiWeilIntervalFormEmbedding b
        (suzukiTaToFormCLM b (suzukiTaRawDeficiency b eps)) +
      (-1 : ℂ) • suzukiWeilIntervalFormEmbedding b
        (ccmArchimedeanFormDomain_extension hab
          (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps))) +
      (-1 : ℂ) • suzukiWeilIntervalFormEmbedding b
        (suzukiTaRiesz_metricShiftCorrection hab eps) by module]
  rw [suzukiApertureZeroExtendL2_add, suzukiApertureZeroExtendL2_add,
    suzukiApertureZeroExtendL2_smul, suzukiApertureZeroExtendL2_smul,
    hnew b, hold, hcorrection]
  module

/-- Coefficient-faithful physical source obtained by retaining the literal Riesz-deficiency
normalization.  At `eps = 1` this is the normalization carried by Suzuki's plus channel. -/
def suzukiTaNormalizedCompletedCovarianceSource
    (a : SuzukiPositiveAperture) (eps : ℝ) : SoninL2 :=
  (‖suzukiTaRawDeficiency a eps‖ : ℂ) •
    suzukiTaMovableCompletedCovarianceSource a eps

/-- **Coefficient-faithful cross-aperture law.**  A normalized Suzuki source difference splits
exactly into three literal terms: normalized pure shell, normalization drift on the old completed
source, and the explicit covariance metric response.  In particular, a convergence argument may
not discard or absorb the raw-deficiency normalization factor. -/
theorem suzukiTaNormalizedCompletedCovarianceSource_crossAperture_eq
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (eps : ℝ) :
    suzukiTaNormalizedCompletedCovarianceSource b eps -
      suzukiTaNormalizedCompletedCovarianceSource a eps =
      (‖suzukiTaRawDeficiency b eps‖ : ℂ) •
        suzukiApertureZeroExtendL2
          (suzukiWeilIntervalFormEmbedding b
            (suzukiTaRiesz_metricRenormalizedShell hab eps)) +
      ((‖suzukiTaRawDeficiency b eps‖ - ‖suzukiTaRawDeficiency a eps‖ : ℝ) : ℂ) •
        suzukiTaMovableCompletedCovarianceSource a eps +
      ((‖suzukiTaRawDeficiency b eps‖ : ℂ) *
        ((boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) -
          boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder b) : ℝ) : ℂ)) •
        suzukiApertureZeroExtendL2
          (suzukiWeilIntervalCovariance b
            (suzukiWeilIntervalFormEmbedding b
              (ccmArchimedeanFormDomain_extension hab
                (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps))))) := by
  let nb : ℝ := ‖suzukiTaRawDeficiency b eps‖
  let na : ℝ := ‖suzukiTaRawDeficiency a eps‖
  let S : SoninL2 := suzukiApertureZeroExtendL2
    (suzukiWeilIntervalFormEmbedding b
      (suzukiTaRiesz_metricRenormalizedShell hab eps))
  let P : SoninL2 := suzukiTaMovableCompletedCovarianceSource b eps
  let Q : SoninL2 := suzukiTaMovableCompletedCovarianceSource a eps
  let d : ℂ := ((boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) -
    boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder b) : ℝ) : ℂ)
  let K : SoninL2 := suzukiApertureZeroExtendL2
    (suzukiWeilIntervalCovariance b
      (suzukiWeilIntervalFormEmbedding b
        (ccmArchimedeanFormDomain_extension hab
          (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps)))))
  change (nb : ℂ) • P - (na : ℂ) • Q =
    (nb : ℂ) • S + ((nb - na : ℝ) : ℂ) • Q + ((nb : ℂ) * d) • K
  have hs : S = P - Q - d • K := by
    exact suzukiTaRiesz_metricRenormalizedShell_physical_eq hab eps
  have hp : P = S + Q + d • K := by
    rw [hs]
    module
  rw [hp]
  module

end RHTower
