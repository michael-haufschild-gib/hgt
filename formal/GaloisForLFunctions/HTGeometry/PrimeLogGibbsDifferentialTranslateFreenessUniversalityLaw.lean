import GaloisForLFunctions.HTGeometry.PrimeLogDifferentialLinearIndependence
import GaloisForLFunctions.HTGeometry.PrimeLogGibbsQuantitativeJets

/-!
# Prime-log Gibbs differential-translate freeness universality

The universal facet gauge produces a prime-log Herglotz source that is both an all-order locally
uniform limit of finite Hermitian Gibbs susceptibilities and free of every nontrivial finite
constant-coefficient differential relation among distinct complex translates.
-/

open Complex Set Filter Finset Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The `m`-th susceptibility jet of the finite universal-gauge Hermitian Gibbs response. -/
def universalPrimeLogFiniteHermitianGibbsJet
    (m : ℕ) (x : Finset Nat.Primes × ℝ) (z : ℂ) : ℂ :=
  iteratedDeriv m
    (fun w => -_root_.HTGeometry.finiteTransitionPassiveResponse
      (_root_.HTGeometry.finiteGibbsTransitionIntensity x.2
        (primeLogKMSFiniteEnergy x.1)
        (primeLogGibbsFiniteHermitianAmplitude x.1
          (fun q => universalFacetOrbitGauge q) x.2))
      (primeLogKMSFiniteEnergy x.1) w) z

/-- Every derivative order of the finite physical response converges locally uniformly to the
corresponding universal prime-log jet. -/
theorem universalPrimeLogFiniteHermitianGibbsJet_tendstoLocallyUniformlyOn
    (m : ℕ) :
    TendstoLocallyUniformlyOn
      (universalPrimeLogFiniteHermitianGibbsJet m)
      (iteratedDeriv m (primeLogHerglotz (fun q => universalFacetOrbitGauge q)))
      Filter.atTop upperHalfPlane := by
  simpa only [universalPrimeLogFiniteHermitianGibbsJet] using
    universalFacetOrbitGauge_iteratedDeriv_finiteHermitianGibbsResponse_tendstoLocallyUniformlyOn_joint
      m

/-- **Gibbs-realizable differential-translate freeness law.**  One universal source is reached in
all susceptibility orders by finite Hermitian Gibbs systems, yet no nontrivial finite polynomial
packet of constant-coefficient differential operators can cancel its distinct translates. -/
theorem universalFacetOrbitGauge_gibbsRealizable_differentialTranslateFree :
    (∀ (H : Finset ℂ) (L : ℂ → Polynomial ℂ) {h₀ : ℂ}, h₀ ∈ H → L h₀ ≠ 0 →
      (∑ h ∈ H, constantCoeffDifferentialOperator (L h)
        (primeLogTranslate (fun q => universalFacetOrbitGauge q) h)) ≠ 0) ∧
    ∀ m : ℕ,
      TendstoLocallyUniformlyOn
        (universalPrimeLogFiniteHermitianGibbsJet m)
        (iteratedDeriv m (primeLogHerglotz (fun q => universalFacetOrbitGauge q)))
        Filter.atTop upperHalfPlane := by
  refine ⟨?_, universalPrimeLogFiniteHermitianGibbsJet_tendstoLocallyUniformlyOn⟩
  intro H L h₀ hh₀ hL
  exact finite_primeLogTranslate_differentialCombination_ne_zero
    (fun q => universalFacetOrbitGauge q) ‖universalFacetOrbitGauge‖
    (fun q => (le_abs_self (universalFacetOrbitGauge q)).trans
      (universalFacetOrbitGauge.norm_coe_le_norm q)) H L hh₀ hL

end

end GaloisForLFunctions.HTGeometry
