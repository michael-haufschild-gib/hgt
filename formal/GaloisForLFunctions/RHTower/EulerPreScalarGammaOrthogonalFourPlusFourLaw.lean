import GaloisForLFunctions.RHTower.EulerPreScalarGammaReporterRigidity

/-!
# Orthogonal four-plus-four law for the pre-scalar Gamma reporter

The unique full-Euler pre-scalar Gamma reporter has critical energy eight.
This file identifies that eight canonically.  The reporter is the orthogonal
sum of a radial normalized-state channel and a transverse centered-Fisher
channel.  Each channel has critical energy four.

Thus the factor-two excess is not removable slack: it is two independent
four-unit records required by the division-free coefficient family.  Together
with same-carrier reporter rigidity, this forces every four-unit completion to
change the carrier or the incidence pairing rather than project away one of
the two source records.
-/

open Complex Filter Set
open scoped Topology

namespace RHTower

noncomputable section

/-- Radial base-state component of the pre-scalar Gamma reporter. -/
def eulerPositivePreScalarGammaRadialSource
    (sigma : ℝ) (hsigma : 1 < sigma) : EulerPositiveL2 :=
  (((2 * (sigma - 1) * eulerPositiveLogMoment 1 sigma : ℝ) : ℂ) •
    eulerPositiveStateLp sigma hsigma)

/-- Transverse centered-Fisher component of the pre-scalar Gamma reporter. -/
def eulerPositivePreScalarGammaTransverseSource
    (sigma : ℝ) (hsigma : 1 < sigma) : EulerPositiveL2 :=
  -eulerPositiveCriticalFisherTangentLp sigma hsigma

/-- Exact radial/transverse decomposition of the literal reporter. -/
theorem eulerPositivePreScalarGammaSource_eq_radial_add_transverse
    {sigma : ℝ} (hsigma : 1 < sigma) :
    eulerPositivePreScalarGammaSource sigma hsigma =
      eulerPositivePreScalarGammaRadialSource sigma hsigma +
        eulerPositivePreScalarGammaTransverseSource sigma hsigma := by
  simpa [eulerPositivePreScalarGammaRadialSource,
    eulerPositivePreScalarGammaTransverseSource, sub_eq_add_neg] using
    eulerPositivePreScalarGammaSource_eq_base_sub_tangent hsigma

/-- The radial and transverse source records are exactly orthogonal. -/
theorem inner_eulerPositivePreScalarGammaRadial_transverse_eq_zero
    {sigma : ℝ} (hsigma : 1 < sigma) :
    inner ℂ
        (eulerPositivePreScalarGammaRadialSource sigma hsigma)
        (eulerPositivePreScalarGammaTransverseSource sigma hsigma) = 0 := by
  rw [eulerPositivePreScalarGammaRadialSource,
    eulerPositivePreScalarGammaTransverseSource,
    inner_neg_right, inner_smul_left,
    inner_eulerPositiveState_fisherTangent_eq_zero hsigma,
    mul_zero, neg_zero]

/-- Exact radial-channel energy. -/
theorem norm_eulerPositivePreScalarGammaRadialSource_sq
    {sigma : ℝ} (hsigma : 1 < sigma) :
    ‖eulerPositivePreScalarGammaRadialSource sigma hsigma‖ ^ (2 : ℕ) =
      (2 * (sigma - 1) * eulerPositiveLogMoment 1 sigma) ^ (2 : ℕ) := by
  rw [eulerPositivePreScalarGammaRadialSource, norm_smul,
    norm_eulerPositiveStateLp hsigma, mul_one, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

/-- Exact transverse-channel energy. -/
theorem norm_eulerPositivePreScalarGammaTransverseSource_sq
    {sigma : ℝ} (hsigma : 1 < sigma) :
    ‖eulerPositivePreScalarGammaTransverseSource sigma hsigma‖ ^ (2 : ℕ) =
      eulerPositiveCriticalProjectiveFisherEnergy sigma := by
  rw [eulerPositivePreScalarGammaTransverseSource, norm_neg,
    norm_eulerPositiveCriticalFisherTangentLp_sq hsigma]

/-- Exact Pythagorean energy decomposition of the pre-scalar reporter. -/
theorem norm_eulerPositivePreScalarGammaSource_sq_eq_radial_add_transverse
    {sigma : ℝ} (hsigma : 1 < sigma) :
    ‖eulerPositivePreScalarGammaSource sigma hsigma‖ ^ (2 : ℕ) =
      ‖eulerPositivePreScalarGammaRadialSource sigma hsigma‖ ^ (2 : ℕ) +
        ‖eulerPositivePreScalarGammaTransverseSource sigma hsigma‖ ^ (2 : ℕ) := by
  rw [norm_eulerPositivePreScalarGammaSource_sq hsigma,
    norm_eulerPositivePreScalarGammaRadialSource_sq hsigma,
    norm_eulerPositivePreScalarGammaTransverseSource_sq hsigma,
    eulerPositiveCriticalProjectiveFisherEnergy]
  ring

/-- The radial source record carries four critical energy units. -/
theorem tendsto_norm_eulerPositivePreScalarGammaRadialSource_sq :
    Tendsto
      (fun sigma : ℝ =>
        if hsigma : 1 < sigma then
          ‖eulerPositivePreScalarGammaRadialSource sigma hsigma‖ ^ (2 : ℕ)
        else 0)
      (nhdsWithin 1 (Ioi 1)) (nhds 4) := by
  have hmean := tendsto_eulerSquarefreeAffineCriticalClockMean
  have hfour :
      Tendsto
        (fun sigma : ℝ =>
          4 * eulerSquarefreeAffineCriticalClockMean sigma ^ (2 : ℕ))
        (nhdsWithin 1 (Ioi 1)) (nhds 4) := by
    convert
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (4 : ℝ))
          (nhdsWithin 1 (Ioi 1)) (nhds 4)).mul (hmean.pow 2)) using 1 <;>
      norm_num
  apply hfour.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  simp only [dif_pos hsigma]
  rw [norm_eulerPositivePreScalarGammaRadialSource_sq hsigma,
    ← sub_one_mul_eulerPositiveLogMoment_one_eq_affineMean hsigma]
  ring

/-- The transverse Fisher record independently carries four critical energy
units. -/
theorem tendsto_norm_eulerPositivePreScalarGammaTransverseSource_sq :
    Tendsto
      (fun sigma : ℝ =>
        if hsigma : 1 < sigma then
          ‖eulerPositivePreScalarGammaTransverseSource sigma hsigma‖ ^ (2 : ℕ)
        else 0)
      (nhdsWithin 1 (Ioi 1)) (nhds 4) := by
  apply tendsto_eulerPositiveCriticalProjectiveFisherEnergy.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  simp only [dif_pos hsigma]
  exact (norm_eulerPositivePreScalarGammaTransverseSource_sq hsigma).symm

/-- **Orthogonal four-plus-four law.**  The unique pre-scalar reporter is an
orthogonal sum of two source records, each carrying four critical energy
units, while their total carries eight. -/
theorem eulerPositivePreScalarGamma_orthogonal_four_plus_four_law :
    Tendsto
        (fun sigma : ℝ =>
          if hsigma : 1 < sigma then
            ‖eulerPositivePreScalarGammaRadialSource sigma hsigma‖ ^ (2 : ℕ)
          else 0)
        (nhdsWithin 1 (Ioi 1)) (nhds 4) ∧
      Tendsto
        (fun sigma : ℝ =>
          if hsigma : 1 < sigma then
            ‖eulerPositivePreScalarGammaTransverseSource sigma hsigma‖ ^ (2 : ℕ)
          else 0)
        (nhdsWithin 1 (Ioi 1)) (nhds 4) ∧
      Tendsto
        (fun sigma : ℝ =>
          if hsigma : 1 < sigma then
            ‖eulerPositivePreScalarGammaSource sigma hsigma‖ ^ (2 : ℕ)
          else 0)
        (nhdsWithin 1 (Ioi 1)) (nhds 8) :=
  ⟨tendsto_norm_eulerPositivePreScalarGammaRadialSource_sq,
    tendsto_norm_eulerPositivePreScalarGammaTransverseSource_sq,
    tendsto_norm_eulerPositivePreScalarGammaSource_sq⟩

end

end RHTower
