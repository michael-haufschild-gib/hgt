import GaloisForLFunctions.RHTower.CCMCumulativeNegativeMassSpectrum

/-!
# Prime--Gamma cumulative cofinal universality

The cumulative negative-mass RH criterion is stated at an admissible fixed cutoff.  Rectangular
admissibility is cofinal, so the auxiliary cutoff witness can be removed uniformly.
-/

open Filter

namespace RHTower

noncomputable section

/-- **Prime--Gamma cumulative cofinal law.**  At every sufficiently late cutoff, critical
summatory growth of the explicit prime--Gamma negative mass is equivalent to RH. -/
theorem eventually_riemannHypothesis_iff_primeGammaCumulativeNegativeMassCriticalGrowth
    {L : ℝ} (hL : 0 < L) :
    ∀ᶠ N : ℕ in atTop,
      RiemannHypothesis ↔
        NonnegativeDirichletSummatoryGrowthAt
          (xiRectangularPrimeGammaTailNegativePart L N) 1 := by
  obtain ⟨N₀, hN₀⟩ := exists_xiRectangularAdmissibleCutoff L
  filter_upwards [eventually_ge_atTop N₀] with N hN
  exact riemannHypothesis_iff_primeGammaCumulativeNegativeMassCriticalGrowth hL
    (fun n hNn => hN₀ n (hN.trans hNn))

end

end RHTower
