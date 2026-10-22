import GaloisForLFunctions.RHTower.Sieve.MaynardLongFactorAbsorption
import GaloisForLFunctions.RHTower.Sieve.MaynardCanonicalFactorDichotomy

/-!
# Robust factor groups in Heath-Brown boxes at a ready height

In the degree-`k` Heath-Brown decomposition with Möbius cutoff `L`, each dyadic box `c` is a
product of Dirichlet polynomials of truncated Möbius, constant-one and logarithm coefficients on
dyadic blocks `[2^q, 2^{q+1})`, and a factor has logarithmic length `log_{T0} 2^q`. At a height `T0`
satisfying `IsMaynardLongScaleReady` and a point `s = σ + iy` with `T0 ≤ y ≤ 2T0`, this module shows
that a large box core forces a robust factor group: a nonempty set `u` of factors with total
logarithmic length `α ∈ [t, 4t)`, grouped lower edge exactly `T0^α`, and
`|∏_{i ∈ u} L(block_i, s)| ≥ (T0^α)^{1-σ}`. Long zeta or logarithm factors are first excluded by
the readiness condition, so every factor is short and greedy grouping applies.

## Main results

- `exists_heathBrown_box_dyadic_robust_group_of_ready_scale`: one box with short Möbius factors,
  total length at least `t` and a large core product contains a robust factor group.
- `exists_heathBrown_eligible_robust_group_of_ready_scale`: if the eligible aggregate is at least
  `V` at `s` and every eligible box satisfies the reserve inequality, some eligible box contains a
  robust factor group.

## Hypotheses

The results are conditional. They take the scale predicate `IsMaynardLongScaleReady T0` (explicit
scalar inequalities on `T0`, which hold for all large `T0`), the ranges `4/3 ≤ μ ≤ 19/9`,
`t = μ/120`, `1 ≤ X ≤ T0^μ`, `σ ≥ 0`, `T0 ≤ y ≤ 2T0`, and: shortness of every Möbius factor
(length `≤ 2t`); for the box lemma, total length `≥ t` and the core lower bound
`|core(s)| ≥ (lower edge)^{1-σ}`; for the aggregate lemma, `V > 0`, the large-value premise
`V ≤ |eligible aggregate(s)|` and the reserve inequality `cost · (lower edge)^{1-σ} ≤ V`.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- Robust group in one box. Assuming `IsMaynardLongScaleReady T0`, `4/3 ≤ μ ≤ 19/9`,
`t = μ/120`, `X ≤ T0^μ`, `T0 ≤ y ≤ 2T0`, short Möbius factors, total length `≥ t` and a large core
`|core(σ+iy)| ≥ (lower edge)^{1-σ}`, some factor group of length `α ∈ [t, 4t)` is large. -/
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

/-- Robust group from a large eligible aggregate. Under the same scale hypotheses, assuming
`V ≤ |eligible aggregate(σ+iy)|`, short Möbius factors in every box and the reserve inequality,
some eligible box has a factor group `u` of length `α ∈ [t, 4t)` with
`|∏_{u} L(block_i, σ+iy)| ≥ (T0^α)^{1-σ}`. -/
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
