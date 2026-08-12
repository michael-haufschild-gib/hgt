import GaloisForLFunctions.RHTower.Sieve.MaynardReadyAllShort

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

theorem exists_canonical_sixty_robust_group_of_ready_scale
    {X : ℕ} {T0 t mu sigma y V : ℝ}
    (hready : IsMaynardLongScaleReady T0)
    (hmu_lo : 4 / 3 ≤ mu) (hmu_hi : mu ≤ 19 / 9)
    (ht : t = mu / 120) (hX : 1 ≤ X) (hXscale : (X : ℝ) ≤ T0 ^ mu)
    (hsigma : 0 ≤ sigma) (hylo : T0 ≤ y) (hyupper : y ≤ 2 * T0)
    (hV : 0 < V)
    (haggregate : ∀ L : ℕ, 1 ≤ L → X < (L + 1) ^ 60 →
      V ≤ ‖heathBrownEligibleDyadicAggregate L X 60 T0 t
        ((sigma : ℂ) + (y : ℝ) * Complex.I)‖)
    (hreserve : ∀ L : ℕ, 1 ≤ L → X < (L + 1) ^ 60 →
      ∀ c : HeathBrownBoxChoice L X 60,
        IsHeathBrownBoxEligible L X 60 T0 t c →
          heathBrownEligibleBoxCost L X 60 *
            (groupedDyadicLower
              (heathBrownBoxFactorExponent c.a c.b c.q) : ℝ) ^ (1 - sigma) ≤ V) :
    ∃ L : ℕ, 1 ≤ L ∧ X < (L + 1) ^ 60 ∧
      ∃ c : HeathBrownBoxChoice L X 60,
        IsHeathBrownBoxEligible L X 60 T0 t c ∧
        ∃ u : Finset (HeathBrownBoxFactorIndex 60 c.m), u.Nonempty ∧
          let alpha := ∑ i ∈ u,
            dyadicLogExponent T0 (heathBrownBoxFactorExponent c.a c.b c.q i)
          t ≤ alpha ∧ alpha < 4 * t ∧
            u.card ≤ Fintype.card (HeathBrownBoxFactorIndex 60 c.m) ∧
            ((groupedDyadicLower
              (fun i : {i // i ∈ u} =>
                heathBrownBoxFactorExponent c.a c.b c.q i) : ℕ) : ℝ) =
                  T0 ^ alpha ∧
            ((groupedDyadicLower
              (fun i : {i // i ∈ u} =>
                heathBrownBoxFactorExponent c.a c.b c.q i) : ℕ) : ℝ) ^
                (1 - sigma) ≤
              ‖∏ i : {i // i ∈ u}, LSeries
                (complexCoeff (arithmeticDyadicBlock
                  (heathBrownFactorBase L X
                    (heathBrownBoxFactorKind 60 c.m i))
                  (heathBrownBoxFactorExponent c.a c.b c.q i)))
                    ((sigma : ℂ) + (y : ℝ) * Complex.I)‖ := by
  have ht0 : 0 < t := by rw [ht]; linarith
  have hX120 : (X : ℝ) ≤ T0 ^ (120 * t) := by
    have hexponent : 120 * t = mu := by
      rw [ht]
      ring
    rw [hexponent]
    exact hXscale
  obtain ⟨L, hL, hXL, hmobius⟩ :=
    exists_sixty_cutoff_all_moebius_factors_short hready.1 ht0.le hX120
  refine ⟨L, hL, hXL, ?_⟩
  exact exists_heathBrown_eligible_robust_group_of_ready_scale
    L X 60 (by norm_num) hready hmu_lo hmu_hi ht hX hXscale hsigma
      hylo hyupper hV (haggregate L hL hXL) hmobius (hreserve L hL hXL)

end RHTower.Sieve
