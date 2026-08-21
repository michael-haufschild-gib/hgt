import GaloisForLFunctions.RHTower.Sieve.MaynardTrivialBoundaryShellCap

noncomputable section
namespace RHTower.Sieve

open Filter Topology

/-- Reparameterized central shell, positive-amplitude branch, with polylog cap discharged
internally.  The surviving band already satisfies Maynard's second count. -/
theorem eventually_exists_routeT_adjacentDefect_centralInterval_forcedSecond_capped
    {D : ℝ} (hD : 0 < D) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X : ℕ} {mu N0 H R b : ℝ},
      1 < X → 1 ≤ L → L ≤ X → X < (L + 1) ^ 60 →
      T ^ mu = (X : ℝ) →
      (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 19 / 9 →
      1 < N0 / (2 ^ 120 : ℝ) →
      (X : ℝ) ≤ 4 * N0 → N0 ≤ (X : ℝ) →
      0 < H → 0 < R → H ≤ R →
      T + 2 ≤ b → b ≤ 2 * T →
      (∀ y ∈ Set.Icc T b, |y| ≤ N0 / (2 * R)) →
      D ≤ ‖∫ y in T..b,
        heathBrownWindowRelevantEligibleDyadicAggregate L X 60 T (mu / 120) N0
            ((1 : ℂ) + (y : ℝ) * Complex.I) *
          (routeTNormalizedSmoothWindowMellin N0 R
              ((1 : ℂ) + (y : ℝ) * Complex.I) -
            routeTNormalizedSmoothWindowMellin N0 H
              ((1 : ℂ) + (y : ℝ) * Complex.I))‖ →
      (b - T) * routeTTrivialBoundaryAmplitudeThreshold L X 60 N0 ≤ D / 8 →
      ∃ n : ℕ, ∃ delta : ℝ, ∃ lam : ℕ → ℝ, ∃ S : Finset ℕ, ∃ q : ℕ,
        0 < n ∧ 1 ≤ delta ∧ delta ≤ 2 ∧
        b = T + ((2 * n : ℕ) : ℝ) * delta ∧
        (∀ i, lam i + delta ≤ lam (i + 1)) ∧
        S ⊆ Finset.range n ∧ q < routeTTrivialBoundaryBandCount T ∧
        (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) ∧
        (∀ r ∈ S, (((2 ^ q : ℕ) : ℝ) *
          routeTTrivialBoundaryAmplitudeThreshold L X 60 N0) ≤
            ‖heathBrownWindowRelevantEligibleDyadicAggregate
              L X 60 T (mu / 120) N0
                ((1 : ℂ) + (lam r : ℝ) * Complex.I)‖) ∧
        D / (32 * (routeTTrivialBoundaryBandCount T : ℝ)) ≤
          (((2 ^ q : ℕ) : ℝ) *
            routeTTrivialBoundaryAmplitudeThreshold L X 60 N0) *
              (S.card : ℝ) ∧
        (S.card : ℝ) ≤ T * (T ^ mu) ^
          (1 + routeTGapMomentNu -
            2 * routeTAdaptiveCellAmplitude L X 60 N0
              (((2 ^ q : ℕ) : ℝ) *
                routeTTrivialBoundaryAmplitudeThreshold L X 60 N0)) := by
  filter_upwards [
    eventually_exists_routeT_adjacentDefect_centralInterval_forcedSecond hD,
    eventually_heathBrownWindowRelevantFixedPolylogBound_le_shellBandCap,
    Filter.eventually_ge_atTop (1 : ℝ)] with T hforced hcap hT
  intro L X mu N0 H R b hX hL hLX hXL hXexact hLscale hmuLo hmuHi hN hXN
    hNX hH hR hHR hlength htop hcentral hdefect hbase
  have hXscale : (X : ℝ) ≤ T ^ (19 / 9 : ℝ) := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hT hmuHi
    simpa only [hXexact] using hpow
  have hcap' := hcap hL hX hLX hXN hNX hXscale hN
  have hcomparable :
      (X : ℝ) ≤ (4 * (2 ^ 120 : ℝ)) * (N0 / (2 ^ 120 : ℝ)) := by
    have heq : (4 * (2 ^ 120 : ℝ)) * (N0 / (2 ^ 120 : ℝ)) = 4 * N0 := by
      field_simp
    rw [heq]
    exact hXN
  exact hforced hX hL hLX hXL hXexact hLscale hmuLo hmuHi hN hcomparable hH hR
    hHR hlength htop hcentral hdefect hcap' hbase

end RHTower.Sieve
