import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureBoundaryCapacity

/-!
# One-limit positive-shift renderer for phase-averaged HCF covariance

The HCF boundary phase average was previously defined as an integral of phasewise boundary
limits.  Here phase is integrated into one compact test weight before any boundary limit is
taken.  A single Plemelj theorem then identifies one positive-real-shift
pole--Gamma--von-Mangoldt integral with the complete phase-averaged boundary channel.

Subtracting this integral from the exact safe-line height-cell source gives a zero-independent
finite-shift renderer converging to the full phase-averaged HCF covariance.  Thus any uniform
finite-shift estimate can now attack the sharp `π N + o(N)` gate without selecting a Xi divisor
and without interchanging a phase integral with a family of boundary limits.
-/

open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry
open RHTower.RealBoundaryDivisor
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Compact HCF test weight after height phase has been integrated out. -/
def criticalFeaturePhaseAveragedBoundaryCutoffWeight
    (n : ℕ) (x : ℝ) : ℝ :=
  ∫ theta : ℝ in (0 : ℝ)..1,
    criticalFeatureTranslatedLatticeBoundaryCutoffWeight theta
      (criticalFeatureCanonicalLatticeWindow n) n x

theorem continuous_criticalFeaturePhaseAveragedBoundaryCutoffWeight
    (n : ℕ) :
    Continuous (criticalFeaturePhaseAveragedBoundaryCutoffWeight n) := by
  unfold criticalFeaturePhaseAveragedBoundaryCutoffWeight
  unfold criticalFeatureTranslatedLatticeBoundaryCutoffWeight
    criticalFeatureBoundaryCutoffWeight criticalFeatureRealBoundaryWeight
  fun_prop (disch := intros; positivity)

theorem criticalFeaturePhaseAveragedBoundaryCutoffWeight_eq_zero_of_not_mem
    (n : ℕ) {x : ℝ}
    (hx : x ∉ Ioo (-((n : ℝ) + 3)) ((n : ℝ) + 3)) :
    criticalFeaturePhaseAveragedBoundaryCutoffWeight n x = 0 := by
  rw [criticalFeaturePhaseAveragedBoundaryCutoffWeight]
  rw [show (fun theta : ℝ =>
      criticalFeatureTranslatedLatticeBoundaryCutoffWeight theta
        (criticalFeatureCanonicalLatticeWindow n) n x) = fun _ => 0 by
    funext theta
    exact criticalFeatureTranslatedLatticeBoundaryCutoffWeight_eq_zero_of_not_mem
      theta (criticalFeatureCanonicalLatticeWindow n) n hx]
  simp

/-- One compact boundary observable after integrating phase into its test weight. -/
def criticalFeaturePhaseAveragedCompactBoundaryObservable
    (n : ℕ) (eta : ℝ) : ℝ :=
  ∫ x in Icc (-((n : ℝ) + 3)) ((n : ℝ) + 3),
    criticalFeaturePhaseAveragedBoundaryCutoffWeight n x *
      boundaryDensity XiC eta x

/-- Positive-real-shift pole--Gamma--von-Mangoldt evaluation of the same test weight. -/
def criticalFeaturePhaseAveragedCompactPoleGammaObservable
    (n : ℕ) (eta : ℝ) : ℝ :=
  ∫ x in Icc (-((n : ℝ) + 3)) ((n : ℝ) + 3),
    criticalFeaturePhaseAveragedBoundaryCutoffWeight n x *
      criticalFeaturePositiveShiftPoleGammaDensity eta x

theorem criticalFeaturePhaseAveragedCompactBoundaryObservable_eq_poleGamma
    (n : ℕ) {eta : ℝ} (heta0 : 0 < eta) (hetaHalf : eta < 1 / 2) :
    criticalFeaturePhaseAveragedCompactBoundaryObservable n eta =
      criticalFeaturePhaseAveragedCompactPoleGammaObservable n eta := by
  rw [criticalFeaturePhaseAveragedCompactBoundaryObservable,
    criticalFeaturePhaseAveragedCompactPoleGammaObservable]
  apply setIntegral_congr_ae measurableSet_Icc
  filter_upwards
    [ae_boundaryDensity_XiC_eq_positiveShiftPoleGammaDensity heta0 hetaHalf]
    with x hx
  rw [hx]
  intro _hx
  rfl

theorem criticalFeaturePhaseAveragedBoundaryCutoffWeight_eq_capacity
    (n : ℕ) (x : ℝ) :
    criticalFeaturePhaseAveragedBoundaryCutoffWeight n x =
      SchwartzMap.realCompactIntervalCutoff (n : ℝ) x *
        (∫ theta : ℝ in (0 : ℝ)..1,
          criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight theta
            (criticalFeatureCanonicalLatticeWindow n) x) := by
  rw [criticalFeaturePhaseAveragedBoundaryCutoffWeight]
  simp_rw [criticalFeatureTranslatedLatticeBoundaryCutoffWeight_eq_finite_mul_cutoff]
  rw [intervalIntegral.integral_mul_const]
  ring

/-- Single Plemelj limit for the whole phase-averaged HCF boundary channel. -/
theorem tendsto_criticalFeaturePhaseAveragedCompactBoundaryObservable
    (n : ℕ) :
    Tendsto (criticalFeaturePhaseAveragedCompactBoundaryObservable n)
      (𝓝[>] (0 : ℝ))
      (𝓝 (criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n)) := by
  have hr : 0 ≤ (n : ℝ) + 3 := by positivity
  have hrR : (n : ℝ) + 3 < (n : ℝ) + 4 := by linarith
  obtain ⟨Gamma, hGamma, hlim⟩ :=
    XiRealBoundary.tendsto_xiBoundaryDensity_setIntegral
      (c := 0) (r := (n : ℝ) + 3) (R := (n : ℝ) + 4)
      hr hrR
      (continuous_criticalFeaturePhaseAveragedBoundaryCutoffWeight n)
      (fun x hx => by
        apply criticalFeaturePhaseAveragedBoundaryCutoffWeight_eq_zero_of_not_mem n
        simpa only [zero_sub, zero_add] using hx)
  obtain ⟨Gamma', hGamma', havg⟩ :=
    exists_criticalFeatureSourceBoundaryPhaseAverage_eq_capacitySum n
  have hsame : Gamma = Gamma' := by
    ext gamma
    rw [hGamma, hGamma']
    simp
  have htarget :
      (∑ gamma ∈ Gamma,
        ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
          criticalFeaturePhaseAveragedBoundaryCutoffWeight n gamma) =
        criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n := by
    rw [hsame, havg]
    apply Finset.sum_congr rfl
    intro gamma hgamma
    rw [criticalFeaturePhaseAveragedBoundaryCutoffWeight_eq_capacity]
    ring
  rw [← htarget]
  have hlower : (0 : ℝ) - ((n : ℝ) + 3) = -((n : ℝ) + 3) := by ring
  have hupper : (0 : ℝ) + ((n : ℝ) + 3) = (n : ℝ) + 3 := by ring
  rw [hlower, hupper] at hlim
  exact hlim

/-- One zero-independent positive-real-shift source evaluation has the same boundary limit. -/
theorem tendsto_criticalFeaturePhaseAveragedCompactPoleGammaObservable
    (n : ℕ) :
    Tendsto (criticalFeaturePhaseAveragedCompactPoleGammaObservable n)
      (𝓝[>] (0 : ℝ))
      (𝓝 (criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n)) := by
  have hsource := tendsto_criticalFeaturePhaseAveragedCompactBoundaryObservable n
  apply hsource.congr'
  have hhalf : ∀ᶠ eta : ℝ in 𝓝[>] (0 : ℝ), eta < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin, hhalf] with eta heta0 hetaHalf
  exact criticalFeaturePhaseAveragedCompactBoundaryObservable_eq_poleGamma
    n heta0 hetaHalf

/-- Zero-independent positive-shift renderer for complete phase-averaged HCF covariance. -/
def criticalFeaturePhaseAveragedPoleGammaCovarianceAtShift
    (n : ℕ) (eta : ℝ) : ℝ :=
  (∑ k ∈ criticalFeatureCanonicalLatticeWindow n,
    ∫ t : ℝ in ((k : ℝ) - 1)..(k : ℝ),
      2 * (logDeriv archFactor (criticalFeatureEulerVMArchPoint t) -
        deriv (logDeriv archFactor) (criticalFeatureEulerVMArchPoint t)).re) -
    criticalFeaturePhaseAveragedCompactPoleGammaObservable n eta

/-- Source renderer lands on exact HCF covariance in one boundary limit. -/
theorem tendsto_criticalFeaturePhaseAveragedPoleGammaCovarianceAtShift
    (n : ℕ) :
    Tendsto (criticalFeaturePhaseAveragedPoleGammaCovarianceAtShift n)
      (𝓝[>] (0 : ℝ))
      (𝓝 (criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage n)) := by
  have hconst : Tendsto
      (fun _ : ℝ =>
        ∑ k ∈ criticalFeatureCanonicalLatticeWindow n,
          ∫ t : ℝ in ((k : ℝ) - 1)..(k : ℝ),
            2 * (logDeriv archFactor (criticalFeatureEulerVMArchPoint t) -
              deriv (logDeriv archFactor) (criticalFeatureEulerVMArchPoint t)).re)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑ k ∈ criticalFeatureCanonicalLatticeWindow n,
        ∫ t : ℝ in ((k : ℝ) - 1)..(k : ℝ),
          2 * (logDeriv archFactor (criticalFeatureEulerVMArchPoint t) -
            deriv (logDeriv archFactor) (criticalFeatureEulerVMArchPoint t)).re)) :=
    tendsto_const_nhds
  have h := hconst.sub
    (tendsto_criticalFeaturePhaseAveragedCompactPoleGammaObservable n)
  change Tendsto
    (fun eta : ℝ =>
      (∑ k ∈ criticalFeatureCanonicalLatticeWindow n,
        ∫ t : ℝ in ((k : ℝ) - 1)..(k : ℝ),
          2 * (logDeriv archFactor (criticalFeatureEulerVMArchPoint t) -
            deriv (logDeriv archFactor) (criticalFeatureEulerVMArchPoint t)).re) -
        criticalFeaturePhaseAveragedCompactPoleGammaObservable n eta)
    (𝓝[>] (0 : ℝ))
    (𝓝 (criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage n))
  rw [criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage_eq_heightCells]
  exact h

end

end RHTower
