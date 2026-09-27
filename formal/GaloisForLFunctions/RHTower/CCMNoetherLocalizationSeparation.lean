import GaloisForLFunctions.RHTower.CCMLocalizationPrimeBudget

/-!
# A conserved actual Noether energy coexists with unbounded localization errors

The action uses the literal arithmetic phase potential. Its time-translation
charge is mechanical energy. An already constructed global Newton flow keeps
that charge fixed on a positive source, while finite mass-preserving
localizations of the same source have continuous error unbounded below.
-/

noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard

/-- The compensated local energy remains in one fixed source-dependent interval
for every finite chain, including chains whose individual terms diverge. -/
theorem ccmLocalization_compensated_energy_bound {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (angles : List 𝓢(ℝ, ℝ)) :
    |ccmRestrictedWeilSourceQuadratic a (ccmLocalizationRemainder u angles).toCCMFormVector +
      ((ccmLocalizationPieces u angles).map
        (fun v => ccmRestrictedWeilSourceQuadratic a v.toCCMFormVector)).sum +
      ccmLocalizationContinuousTotal u angles -
      ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector| ≤ ccmLocalizationPrimeBudget u := by
  have h := ccmLocalization_energy_conservation u angles
  have he : ccmRestrictedWeilSourceQuadratic a (ccmLocalizationRemainder u angles).toCCMFormVector +
      ((ccmLocalizationPieces u angles).map
        (fun v => ccmRestrictedWeilSourceQuadratic a v.toCCMFormVector)).sum +
      ccmLocalizationContinuousTotal u angles -
      ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector = ccmLocalizationPrimeTotal u angles := by
    linarith only [h]
  rw [he]
  exact abs_ccmLocalizationPrimeTotal_le_budget u angles

def ccmSourcePhaseLagrangian {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) (q v : ℝ) : ℝ :=
  v ^ 2 / 2 - ccmPhaseLocalizationEnergy u theta q

def ccmSourcePhaseAction {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ))
    (q : ℝ → ℝ) (t₀ t₁ : ℝ) : ℝ :=
  ∫ t in t₀..t₁, ccmSourcePhaseLagrangian u theta (q t) (deriv q t)

theorem ccmSourcePhaseAction_time_translation {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ))
    (q : ℝ → ℝ) (t₀ t₁ c : ℝ) :
    ccmSourcePhaseAction u theta (fun t => q (t + c)) t₀ t₁ =
      ccmSourcePhaseAction u theta q (t₀ + c) (t₁ + c) := by
  simp only [ccmSourcePhaseAction, deriv_comp_add_const]
  exact intervalIntegral.integral_comp_add_right
    (fun t => ccmSourcePhaseLagrangian u theta (q t) (deriv q t)) c

theorem ccmSourcePhase_noether_charge {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) (q v : ℝ) :
    v * deriv (ccmSourcePhaseLagrangian u theta q) v - ccmSourcePhaseLagrangian u theta q v =
      v ^ 2 / 2 + ccmPhaseLocalizationEnergy u theta q := by
  have hd : HasDerivAt (ccmSourcePhaseLagrangian u theta q) v v := by
    convert! (((hasDerivAt_id v).pow 2).div_const 2).sub_const
      (ccmPhaseLocalizationEnergy u theta q) using 1
    simp
  rw [hd.deriv, ccmSourcePhaseLagrangian]
  ring

theorem exists_ccmNoether_positive_flow_unbounded_localization :
    ∃ (a : SuzukiPositiveAperture) (u : CCMComplexSmoothInteriorSource a)
      (theta : 𝓢(ℝ, ℝ)) (B K : ℝ),
      0 < ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector ∧ 0 < B ∧ 0 ≤ K ∧
      (∀ q v : ℝ, ccmSourcePhaseLagrangian u theta q v = arithmeticPhaseLagrangian B q v -
        ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector) ∧
      (∀ (q : ℝ → ℝ) (t₀ t₁ c : ℝ),
        ccmSourcePhaseAction u theta (fun t => q (t + c)) t₀ t₁ =
          ccmSourcePhaseAction u theta q (t₀ + c) (t₁ + c)) ∧
      (∀ q t : ℝ, (deriv (arithmeticPhaseFlow B q) t) ^ 2 / 2 +
        ccmPhaseLocalizationEnergy u theta (arithmeticPhaseFlow B q t) =
          ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector + 2 * B + 1) ∧
      (∀ t : ℝ, deriv (deriv (arithmeticPhaseTrajectory B)) t =
        -deriv (ccmPhaseLocalizationEnergy u theta) (arithmeticPhaseTrajectory B t)) ∧
      (∀ angles : List 𝓢(ℝ, ℝ), |ccmLocalizationPrimeTotal u angles| ≤ K) ∧
      ∀ R : ℝ, ∃ angles : List 𝓢(ℝ, ℝ),
        (∀ eta ∈ angles, HasCompactSupport eta) ∧
        (((ccmLocalizationPieces u angles).map
          (fun v => ‖ccmArchimedeanFormEmbedding a v.toCCMFormVector‖ ^ 2)).sum =
          ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2) ∧
        (∀ x y, 0 ≤ thetaLocalizationChainWeight angles x y ∧
          thetaLocalizationChainWeight angles x y ≤ 4) ∧
        (∫ p, ccmThetaChainContinuousDensity u angles p ∂thetaContinuousLinkMeasure) < R := by
  obtain ⟨a, u, theta, B, hq, hB, _, he, _, hflow, hnewton⟩ :=
    exists_ccmArithmetic_positive_noether_flow
  have hne : ccmArchimedeanFormEmbedding a u.toCCMFormVector ≠ 0 := by
    intro hz
    have hv : u.toCCMFormVector = 0 := ccmArchimedeanFormEmbedding_injective a
      (by rw [hz, map_zero])
    rw [hv, ccmRestrictedWeilSourceQuadratic_zero] at hq
    exact (lt_irrefl 0) hq
  have hm := sq_pos_of_pos (norm_pos_iff.mpr hne)
  refine ⟨a, u, theta, B, ccmLocalizationPrimeBudget u, hq, hB,
    ccmLocalizationPrimeBudget_nonneg u, ?_, ccmSourcePhaseAction_time_translation u theta,
    hflow, hnewton, abs_ccmLocalizationPrimeTotal_le_budget u,
    ccmLocalization_continuous_total_unbounded_below u hm⟩
  intro q v
  rw [ccmSourcePhaseLagrangian, he, arithmeticPhaseLagrangian]
  ring

end RHTower
