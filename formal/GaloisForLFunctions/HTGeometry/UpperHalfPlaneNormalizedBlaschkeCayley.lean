import GaloisForLFunctions.HTGeometry.IndexedBlaschkeMultiplier
import GaloisForLFunctions.HTGeometry.UpperHalfPlaneFiniteBlaschkeCayley

/-!
# Cayley transport for phase-normalized Blaschke factors

The infinite-product normalization uses a radial unit in addition to the ordinary Cayley unit.
This file packages their product and proves exact upper-half-plane transport with unit modulus.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Radial phase used by the standard normalized disk Blaschke factor. -/
def normalizedBlaschkePhase_upperHalfPlaneNormalizedBlaschkeCayley (a : ℂ) : ℂ :=
  if a = 0 then 1 else -((‖a‖ : ℂ) / a)

theorem norm_normalizedBlaschkePhase_eq_one (a : ℂ) :
    ‖normalizedBlaschkePhase_upperHalfPlaneNormalizedBlaschkeCayley a‖ = 1 := by
  by_cases ha : a = 0
  · simp [normalizedBlaschkePhase_upperHalfPlaneNormalizedBlaschkeCayley, ha]
  rw [normalizedBlaschkePhase_upperHalfPlaneNormalizedBlaschkeCayley, if_neg ha, norm_neg, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a),
    div_self (norm_ne_zero_iff.mpr ha)]

theorem normalizedBlaschkeFactor_eq_phase_mul_upperHalfPlaneNormalizedBlaschkeCayley (a z : ℂ) :
    normalizedBlaschkeFactor a z =
      normalizedBlaschkePhase_upperHalfPlaneNormalizedBlaschkeCayley a * blaschkeFactor a z := by
  by_cases ha : a = 0
  · subst a
    simp [normalizedBlaschkeFactor, normalizedBlaschkePhase_upperHalfPlaneNormalizedBlaschkeCayley,
      blaschkeFactor]
  simp [normalizedBlaschkeFactor, normalizedBlaschkePhase_upperHalfPlaneNormalizedBlaschkeCayley, ha]

/-- Combined radial and Cayley phase for a normalized upper-half-plane Blaschke factor. -/
def normalizedCayleyBlaschkeUnit (p : ℂ) : ℂ :=
  normalizedBlaschkePhase_upperHalfPlaneNormalizedBlaschkeCayley (upperToDiskCayley p) *
    cayleyBlaschkeUnit p

theorem norm_normalizedCayleyBlaschkeUnit_eq_one
    {p : ℂ} (hp : 0 < p.im) :
    ‖normalizedCayleyBlaschkeUnit p‖ = 1 := by
  rw [normalizedCayleyBlaschkeUnit, norm_mul,
    norm_normalizedBlaschkePhase_eq_one,
    norm_cayleyBlaschkeUnit_eq_one hp, one_mul]

/-- Exact Cayley transport of one phase-normalized disk Blaschke factor. -/
theorem normalizedBlaschkeFactor_upperToDiskCayley
    {p z : ℂ} (hp : 0 < p.im) (hz : 0 < z.im) :
    normalizedBlaschkeFactor (upperToDiskCayley p) (upperToDiskCayley z) =
      normalizedCayleyBlaschkeUnit p *
        upperHalfPlaneBlaschkeFactor p z := by
  rw [normalizedBlaschkeFactor_eq_phase_mul_upperHalfPlaneNormalizedBlaschkeCayley,
    blaschkeFactor_upperToDiskCayley hp hz,
    normalizedCayleyBlaschkeUnit]
  ring

end

end GaloisForLFunctions.HTGeometry
