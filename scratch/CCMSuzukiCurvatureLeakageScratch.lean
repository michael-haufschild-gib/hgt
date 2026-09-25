import GaloisForLFunctions.RHTower.CCMSuzukiCrossApertureMetricCurvature

open scoped InnerProductSpace

noncomputable section
namespace RHTower

private theorem suzukiRiesz_retained_metric_gap
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    (u v : CCMArchimedeanFormDomain a) :
    inner ℂ
        (boundedPerturbedFormRiesz
          (suzukiWeilIntervalFormEmbedding b)
          (suzukiWeilIntervalBoundedRemainder b)
          (ccmArchimedeanFormDomain_extension hab u))
        (ccmArchimedeanFormDomain_extension hab v) =
      inner ℂ
        (boundedPerturbedFormRiesz
          (suzukiWeilIntervalFormEmbedding a)
          (suzukiWeilIntervalBoundedRemainder a) u) v +
        ((boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder b) -
          boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) : ℝ) : ℂ) *
          inner ℂ (suzukiWeilIntervalFormEmbedding a u)
            (suzukiWeilIntervalFormEmbedding a v) := by
  rw [inner_suzukiWeilIntervalRiesz_eq_ccmRestrictedWeilForm_add_shift,
    inner_suzukiWeilIntervalRiesz_eq_ccmRestrictedWeilForm_add_shift]
  rw [ccmRestrictedWeilForm_eq_of_val_eq hab
    (ccmArchimedeanFormDomain_extension_val hab u)
    (ccmArchimedeanFormDomain_extension_val hab v)]
  rw [inner_suzukiWeilIntervalFormEmbedding_eq_of_val_eq
    (ccmArchimedeanFormDomain_extension_val hab u)
    (ccmArchimedeanFormDomain_extension_val hab v)]
  ring

theorem suzuki_metricCurvature_retained_eq_shift_shellLeakage
    {a b c : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (hbc : b.1 ≤ c.1)
    (eps : ℝ) (v : CCMArchimedeanFormDomain a) :
    inner ℂ
        (boundedPerturbedFormRiesz
          (suzukiWeilIntervalFormEmbedding c)
          (suzukiWeilIntervalBoundedRemainder c)
          (suzukiTaRiesz_metricCurvature hab hbc eps))
        (ccmArchimedeanFormDomain_extension (hab.trans hbc) v) =
      ((boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder b) -
        boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder c) : ℝ) : ℂ) *
        inner ℂ
          (suzukiWeilIntervalFormEmbedding b
            (suzukiTaRiesz_metricRenormalizedShell hab eps))
          (suzukiWeilIntervalFormEmbedding b
            (ccmArchimedeanFormDomain_extension hab v)) := by
  let S := suzukiTaRiesz_metricRenormalizedShell hab eps
  let T := suzukiTaRiesz_metricRenormalizedShell hbc eps
  let K := suzukiTaRiesz_metricCurvature hab hbc eps
  let R := boundedPerturbedFormRiesz
    (suzukiWeilIntervalFormEmbedding c) (suzukiWeilIntervalBoundedRemainder c)
  let w := ccmArchimedeanFormDomain_extension (hab.trans hbc) v
  have hw : w = ccmArchimedeanFormDomain_extension hbc
      (ccmArchimedeanFormDomain_extension hab v) := by
    exact (ccmArchimedeanFormDomain_extension_trans hab hbc v).symm
  have hAC : inner ℂ (R (suzukiTaRiesz_metricRenormalizedShell
      (hab.trans hbc) eps)) w = 0 := by
    exact inner_suzukiTaRiesz_metricRenormalizedShell_oldBlock_eq_zero
      (hab.trans hbc) eps v
  have hBC : inner ℂ (R T) w = 0 := by
    rw [hw]
    exact inner_suzukiTaRiesz_metricRenormalizedShell_oldBlock_eq_zero
      hbc eps (ccmArchimedeanFormDomain_extension hab v)
  have hAB : inner ℂ
      (boundedPerturbedFormRiesz
        (suzukiWeilIntervalFormEmbedding b)
        (suzukiWeilIntervalBoundedRemainder b) S)
      (ccmArchimedeanFormDomain_extension hab v) = 0 :=
    inner_suzukiTaRiesz_metricRenormalizedShell_oldBlock_eq_zero hab eps v
  have hgap := suzukiRiesz_retained_metric_gap hbc S
    (ccmArchimedeanFormDomain_extension hab v)
  rw [← hw, hAB, zero_add] at hgap
  have hcoc := suzukiTaRiesz_metricRenormalizedShell_cocycle hab hbc eps
  change suzukiTaRiesz_metricRenormalizedShell (hab.trans hbc) eps =
    T + ccmArchimedeanFormDomain_extension hbc S + K at hcoc
  rw [hcoc, map_add, map_add, inner_add_left, inner_add_left,
    hBC, zero_add, hgap] at hAC
  change inner ℂ (R K) w = _
  linear_combination -hAC

end RHTower
