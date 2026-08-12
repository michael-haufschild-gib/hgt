import GaloisForLFunctions.RHTower.Sieve.MaynardLongFactorAbsorption
import GaloisForLFunctions.RHTower.Sieve.MaynardCanonicalFactorDichotomy

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

theorem exists_heathBrown_box_dyadic_robust_group_of_ready_scale
    (L X k : ℕ) (c : HeathBrownBoxChoice L X k)
    {T0 t mu sigma y : ℝ} (hready : IsMaynardLongScaleReady T0)
    (hmu_lo : 4 / 3 ≤ mu) (hmu_hi : mu ≤ 19 / 9)
    (ht : t = mu / 120) (hX : 1 ≤ X) (hXscale : (X : ℝ) ≤ T0 ^ mu)
    (hsigma : 0 ≤ sigma) (hylo : T0 ≤ y) (hyupper : y ≤ 2 * T0)
    (hmobius : ∀ i : HeathBrownBoxFactorIndex k c.m,
      heathBrownBoxFactorKind k c.m i = .moebius →
        dyadicLogExponent T0
          (heathBrownBoxFactorExponent c.a c.b c.q i) ≤ 2 * t)
    (htotal : t ≤ ∑ i : HeathBrownBoxFactorIndex k c.m,
      dyadicLogExponent T0 (heathBrownBoxFactorExponent c.a c.b c.q i))
    (hcore :
      (groupedDyadicLower (heathBrownBoxFactorExponent c.a c.b c.q) : ℝ) ^
          (1 - sigma) ≤
        ‖heathBrownDyadicCoreProduct L X k c.m c.a c.b c.q
          ((sigma : ℂ) + (y : ℝ) * Complex.I)‖) :
    ∃ u : Finset (HeathBrownBoxFactorIndex k c.m), u.Nonempty ∧
      let alpha := ∑ i ∈ u,
        dyadicLogExponent T0 (heathBrownBoxFactorExponent c.a c.b c.q i)
      t ≤ alpha ∧ alpha < 4 * t ∧
        u.card ≤ Fintype.card (HeathBrownBoxFactorIndex k c.m) ∧
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
              (heathBrownFactorBase L X (heathBrownBoxFactorKind k c.m i))
              (heathBrownBoxFactorExponent c.a c.b c.q i)))
                ((sigma : ℂ) + (y : ℝ) * Complex.I)‖ := by
  have hT0 : 1 < T0 := hready.1
  have ht0 : 0 < t := by rw [ht]; linarith
  have hshort : ∀ i : HeathBrownBoxFactorIndex k c.m,
      dyadicLogExponent T0
        (heathBrownBoxFactorExponent c.a c.b c.q i) ≤ 2 * t := by
    intro i
    by_contra hnot
    have hlong : 2 * t < dyadicLogExponent T0
        (heathBrownBoxFactorExponent c.a c.b c.q i) := lt_of_not_ge hnot
    have hkind := heathBrown_factorKind_eq_zeta_or_log_of_long c hmobius i hlong
    exact (not_heathBrown_box_core_large_of_ready_maynard_long_scale
      L X k c i hkind hX hready hmu_lo hmu_hi ht hlong hXscale
        hsigma hylo hyupper) hcore
  exact exists_heathBrown_box_dyadic_robust_group
    L X k c.m c.a c.b c.q hT0 ht0 hshort htotal
      ((sigma : ℂ) + (y : ℝ) * Complex.I) hcore

theorem exists_heathBrown_eligible_robust_group_of_ready_scale
    (L X k : ℕ) (hk : 0 < k) {T0 t mu sigma y V : ℝ}
    (hready : IsMaynardLongScaleReady T0)
    (hmu_lo : 4 / 3 ≤ mu) (hmu_hi : mu ≤ 19 / 9)
    (ht : t = mu / 120) (hX : 1 ≤ X) (hXscale : (X : ℝ) ≤ T0 ^ mu)
    (hsigma : 0 ≤ sigma) (hylo : T0 ≤ y) (hyupper : y ≤ 2 * T0)
    (hV : 0 < V)
    (haggregate : V ≤ ‖heathBrownEligibleDyadicAggregate L X k T0 t
      ((sigma : ℂ) + (y : ℝ) * Complex.I)‖)
    (hmobius : ∀ c : HeathBrownBoxChoice L X k,
      ∀ i : HeathBrownBoxFactorIndex k c.m,
        heathBrownBoxFactorKind k c.m i = .moebius →
          dyadicLogExponent T0
            (heathBrownBoxFactorExponent c.a c.b c.q i) ≤ 2 * t)
    (hreserve : ∀ c : HeathBrownBoxChoice L X k,
      IsHeathBrownBoxEligible L X k T0 t c →
        heathBrownEligibleBoxCost L X k *
          (groupedDyadicLower
            (heathBrownBoxFactorExponent c.a c.b c.q) : ℝ) ^ (1 - sigma) ≤ V) :
    ∃ c : HeathBrownBoxChoice L X k,
      IsHeathBrownBoxEligible L X k T0 t c ∧
      ∃ u : Finset (HeathBrownBoxFactorIndex k c.m), u.Nonempty ∧
        let alpha := ∑ i ∈ u,
          dyadicLogExponent T0 (heathBrownBoxFactorExponent c.a c.b c.q i)
        t ≤ alpha ∧ alpha < 4 * t ∧
          u.card ≤ Fintype.card (HeathBrownBoxFactorIndex k c.m) ∧
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
                (heathBrownFactorBase L X (heathBrownBoxFactorKind k c.m i))
                (heathBrownBoxFactorExponent c.a c.b c.q i)))
                  ((sigma : ℂ) + (y : ℝ) * Complex.I)‖ := by
  obtain ⟨c, helig, hcore, _⟩ :=
    exists_heathBrown_eligible_long_zeta_log_or_robust_group_of_large
      L X k hk hready.1 (by rw [ht]; linarith) hV
        ((sigma : ℂ) + (y : ℝ) * Complex.I) haggregate hmobius hreserve
  refine ⟨c, helig, ?_⟩
  have htotal : t ≤ ∑ i : HeathBrownBoxFactorIndex k c.m,
      dyadicLogExponent T0 (heathBrownBoxFactorExponent c.a c.b c.q i) := by
    simpa [IsHeathBrownBoxEligible, heathBrownBoxTotalExponent] using helig
  exact exists_heathBrown_box_dyadic_robust_group_of_ready_scale
    L X k c hready hmu_lo hmu_hi ht hX hXscale hsigma hylo hyupper
      (hmobius c) htotal hcore

end RHTower.Sieve
