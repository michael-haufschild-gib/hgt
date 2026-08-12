import GaloisForLFunctions.RHTower.Sieve.MaynardFixedPolylogGlobalCount
import GaloisForLFunctions.RHTower.Sieve.MaynardPerronAmplitudeSelection

/-!
# Complete Route-T high-amplitude alternative

Above the fixed long-factor boundary, literal Perron coloring exists.  Below the moving Route-T
boundary its fixed-polylog fibres satisfy Maynard's first alternative; above that boundary the
aggregate is empty.  This closes the entire high-amplitude range without a moving energy constant.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex Filter Topology

/-- The fixed long-factor boundary lies strictly above `99 / 100`.  Keeping this arithmetic
outside the global theorem prevents its large dependent context from entering normalization. -/
theorem maynardLongGlobalAmplitudeDeficit_lt_one_hundredth :
    maynardLongGlobalAmplitudeDeficit < (1 / 100 : ℝ) := by
  dsimp only [maynardLongGlobalAmplitudeDeficit, maynardDerivativeDeficit]
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (47 : ℕ) := one_le_pow₀ (by norm_num)
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **Complete high-amplitude Maynard alternative.**  One unconditional Route-T deficit producer
simultaneously supplies endpoint emptiness and moving-boundary polylog absorption. -/
theorem exists_eventually_routeT_high_amplitude_first_alternative :
    ∃ A : ℝ, ∀ᶠ T : ℝ in atTop,
      ∀ {X K : ℕ} {mu c alpha V delta : ℝ},
      1 ≤ X → (X : ℝ) ≤ T ^ mu →
      4 / 3 ≤ mu → mu ≤ 19 / 9 →
      1 / 2 ≤ c → 1 - maynardLongGlobalAmplitudeDeficit < alpha →
      0 < V → 0 < delta →
      ∀ (S : Finset ℕ), S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) →
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T) →
      (∀ L : ℕ, 1 ≤ L → X < (L + 1) ^ 60 →
        ∀ r ∈ S,
          V ≤ ‖heathBrownPerronRelevantEligibleDyadicAggregate
            L X 60 T (mu / 120)
              ((c : ℂ) + (lam r : ℝ) * Complex.I)‖) →
      (∀ L : ℕ, 1 ≤ L → X < (L + 1) ^ 60 →
        ∀ box : HeathBrownBoxChoice L X 60,
          IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
          IsHeathBrownBoxPerronRelevant X 60 box →
          heathBrownEligibleBoxCost L X 60 *
            (groupedDyadicLower
              (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
                (alpha - c) ≤ V) →
      ∃ L : ℕ, 1 ≤ L ∧ X < (L + 1) ^ 60 ∧
        (L : ℝ) ≤ T ^ (mu / 60) ∧
        (S.card : ℝ) ≤
          maynardHarmonicFactor K delta * T ^ (mu * (1 - alpha)) := by
  obtain ⟨A, _C, _C', _delta0, _hC, _hC', _hdelta0, hendpoint⟩ :=
    exists_eventually_no_perronRelevant_aggregate_near_one
  refine ⟨A, ?_⟩
  filter_upwards [hendpoint,
    eventually_exists_canonical_sixty_perronRelevant_coloring_at_high_amplitude,
    eventually_card_le_maynard_first_alternative_of_high_amplitude_coloring A,
    eventually_gt_atTop (1 : ℝ)] with T hendpointT hcolorT hglobalT hT
  intro X K mu c alpha V delta hX hXscale hmu_lo hmu_hi hc halpha hV hdelta
    S hS lam hband hgap hdiam haggregate hreserve
  obtain ⟨L, hL, hXL, hcut, color, hcolor⟩ :=
    hcolorT X hX mu hmu_lo hmu_hi hXscale c alpha V
      (by linarith) halpha hV S lam hband haggregate hreserve
  have hcut' : (L : ℝ) ≤ T ^ (mu / 60) := by
    have hexponent : (2 : ℝ) * (mu / 120) = mu / 60 := by ring
    simpa only [hexponent] using hcut
  refine ⟨L, hL, hXL, hcut', ?_⟩
  by_cases halphaEndpoint : alpha ≤ 1 - routeTEndpointGlobalDeficit A T
  · have halpha99 : (99 / 100 : ℝ) ≤ alpha := by
      linarith [maynardLongGlobalAmplitudeDeficit_lt_one_hundredth]
    exact hglobalT hX hL hXscale hcut hc halpha99 halphaEndpoint
      hmu_lo hmu_hi rfl rfl hdelta S hS lam hgap hdiam color
        (fun r hr => (hcolor r hr).2)
  · have hnear : 1 - routeTEndpointGlobalDeficit A T < alpha :=
      lt_of_not_ge halphaEndpoint
    have hSempty : S = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hSne
      obtain ⟨r, hr⟩ := hSne
      exact hendpointT X hX mu hmu_lo hmu_hi hXscale L hL hXL hcut'
        c (lam r) alpha V (by linarith) (hband r hr).1 (hband r hr).2
        hnear hV (haggregate L hL hXL r hr) (hreserve L hL hXL)
    rw [hSempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (maynardHarmonicFactor_pos K hdelta).le
      (Real.rpow_nonneg (by linarith) _)

end RHTower.Sieve
