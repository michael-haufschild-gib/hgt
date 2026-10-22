import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalHorizonFinitePartCurrent
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFundamentalHorizonDomain

/-! The original finite-part horizon pairing and physical boundary current at every Xi fundamental QNM. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Filter Topology Set MeasureTheory
noncomputable section
set_option autoImplicit false

/-- At both fundamental QNMs of every Xi divisor, the actual cutoff pairing converges,
its value is meromorphic, and its frequency germ equals the original response's boundary current.
No endpoint admission, nonresonance, assigned left covector, or RH premise is supplied. -/
theorem allXi_fundamental_original_horizon_finite_part (q : XiZeroCopy) (s a J K : ℂ) :
    ∀ w ∈ ({-Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q),
      -Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)} : Set ℂ),
    ∀ b ∈ Ioo (0:ℝ) 1,
      let chi := thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q)
      Tendsto (fun e : ℝ => (∫ t in e..b, continuedHorizonSourcePairing s chi a J K w t)+
        continuedHorizonSourceCounterterm s chi a J K w e)
        (𝓝[>] (0:ℝ)) (𝓝 (continuedHorizonSourcePhase s chi a J K b w)) ∧
      MeromorphicAt (continuedHorizonSourcePhase s chi a J K b) w ∧
      ∀ᶠ u in 𝓝[≠] w, radialBracket (horizon u chi) (horizonFirst u chi)
        (fun t => continuedResponse s chi a J K t u)
        (deriv (fun t => continuedResponse s chi a J K t u)) b =
          continuedHorizonSourcePhase s chi a J K b u := by
  intro w hw b hb
  have hstrip := allXi_fundamental_frequency_strip q w hw
  have hr := (abs_lt.mp hstrip.2).1
  exact ⟨continuedHorizonSource_cutoff_tendsto s _ a J K w hstrip.1 hr hb,
    continuedHorizonSourcePhase_meromorphicAt s _ a J K w hstrip.1 hr hb,
    continuedResponse_horizon_current_germ s _ a J K w hstrip.1 hr hb⟩

end
end RHTower.D4BMLaplaceRadial
