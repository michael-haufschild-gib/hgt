import GaloisForLFunctions.RHTower.Sieve.MaynardCanonicalReadyAllShort

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

theorem exists_heathBrownEligibleSelection_label_of_ready_scale
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
    ∃ label : HeathBrownSelectionLabel L X k,
      IsHeathBrownEligibleSelection L X k
        (T0 := T0) (t := t) (e := 1 - sigma)
        ((sigma : ℂ) + (y : ℝ) * Complex.I) label := by
  obtain ⟨c, helig, u, hune, hulower, huupper, hucard, hulength, hularge⟩ :=
    exists_heathBrown_eligible_robust_group_of_ready_scale
      L X k hk hready hmu_lo hmu_hi ht hX hXscale hsigma hylo hyupper
        hV haggregate hmobius hreserve
  let label : HeathBrownSelectionLabel L X k := ⟨c, u⟩
  refine ⟨label, helig, ?_⟩
  exact ⟨hune, hulower, huupper, hucard, hulength, hularge⟩

theorem exists_heathBrownEligibleSelection_coloring_of_ready_scale
    (L X k : ℕ) (hk : 0 < k) {T0 t mu sigma V : ℝ}
    (hready : IsMaynardLongScaleReady T0)
    (hmu_lo : 4 / 3 ≤ mu) (hmu_hi : mu ≤ 19 / 9)
    (ht : t = mu / 120) (hX : 1 ≤ X) (hXscale : (X : ℝ) ≤ T0 ^ mu)
    (hsigma : 0 ≤ sigma) (hV : 0 < V)
    (S : Finset ℕ) (lam : ℕ → ℝ)
    (hband : ∀ r ∈ S, T0 ≤ lam r ∧ lam r ≤ 2 * T0)
    (haggregate : ∀ r ∈ S,
      V ≤ ‖heathBrownEligibleDyadicAggregate L X k T0 t
        ((sigma : ℂ) + (lam r : ℝ) * Complex.I)‖)
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
    ∃ color : ℕ → HeathBrownSelectionLabel L X k,
      ∀ r ∈ S, IsHeathBrownEligibleSelection L X k
        (T0 := T0) (t := t) (e := 1 - sigma)
        ((sigma : ℂ) + (lam r : ℝ) * Complex.I) (color r) := by
  classical
  have hpoint : ∀ r : ℕ, r ∈ S →
      ∃ label : HeathBrownSelectionLabel L X k,
        IsHeathBrownEligibleSelection L X k
          (T0 := T0) (t := t) (e := 1 - sigma)
          ((sigma : ℂ) + (lam r : ℝ) * Complex.I) label := by
    intro r hr
    exact exists_heathBrownEligibleSelection_label_of_ready_scale
      L X k hk hready hmu_lo hmu_hi ht hX hXscale hsigma
        (hband r hr).1 (hband r hr).2 hV (haggregate r hr) hmobius hreserve
  choose selected hselected using hpoint
  let fallback : HeathBrownSelectionLabel L X k :=
    Classical.choice (nonempty_heathBrownSelectionLabel L X k hk)
  let color : ℕ → HeathBrownSelectionLabel L X k := fun r =>
    if hr : r ∈ S then selected r hr else fallback
  refine ⟨color, ?_⟩
  intro r hr
  simpa [color, hr] using hselected r hr

theorem exists_canonical_sixty_eligibleSelection_coloring_of_ready_scale
    {X : ℕ} {T0 t mu sigma V : ℝ}
    (hready : IsMaynardLongScaleReady T0)
    (hmu_lo : 4 / 3 ≤ mu) (hmu_hi : mu ≤ 19 / 9)
    (ht : t = mu / 120) (hX : 1 ≤ X) (hXscale : (X : ℝ) ≤ T0 ^ mu)
    (hsigma : 0 ≤ sigma) (hV : 0 < V)
    (S : Finset ℕ) (lam : ℕ → ℝ)
    (hband : ∀ r ∈ S, T0 ≤ lam r ∧ lam r ≤ 2 * T0)
    (haggregate : ∀ L : ℕ, 1 ≤ L → X < (L + 1) ^ (60 : ℕ) →
      ∀ r ∈ S, V ≤ ‖heathBrownEligibleDyadicAggregate L X 60 T0 t
        ((sigma : ℂ) + (lam r : ℝ) * Complex.I)‖)
    (hreserve : ∀ L : ℕ, 1 ≤ L → X < (L + 1) ^ (60 : ℕ) →
      ∀ c : HeathBrownBoxChoice L X 60,
        IsHeathBrownBoxEligible L X 60 T0 t c →
          heathBrownEligibleBoxCost L X 60 *
            (groupedDyadicLower
              (heathBrownBoxFactorExponent c.a c.b c.q) : ℝ) ^ (1 - sigma) ≤ V) :
    ∃ L : ℕ, 1 ≤ L ∧ X < (L + 1) ^ (60 : ℕ) ∧ (L : ℝ) ≤ T0 ^ (2 * t) ∧
      ∃ color : ℕ → HeathBrownSelectionLabel L X 60,
        ∀ r ∈ S, IsHeathBrownEligibleSelection L X 60
          (T0 := T0) (t := t) (e := 1 - sigma)
          ((sigma : ℂ) + (lam r : ℝ) * Complex.I) (color r) := by
  have ht0 : 0 < t := by rw [ht]; linarith
  have hX120 : (X : ℝ) ≤ T0 ^ (120 * t) := by
    have hexponent : 120 * t = mu := by
      rw [ht]
      ring
    rw [hexponent]
    exact hXscale
  obtain ⟨L, hL, hXL, hcut⟩ :=
    exists_maynardMoebiusCutoff_sixty hready.1 ht0.le hX120
  have hmobius : ∀ c : HeathBrownBoxChoice L X 60,
      ∀ i : HeathBrownBoxFactorIndex 60 c.m,
        heathBrownBoxFactorKind 60 c.m i = .moebius →
          dyadicLogExponent T0
            (heathBrownBoxFactorExponent c.a c.b c.q i) ≤ 2 * t := by
    intro c i hi
    exact c.moebius_factor_dyadicLogExponent_le hready.1 hL hcut i hi
  refine ⟨L, hL, hXL, hcut, ?_⟩
  exact exists_heathBrownEligibleSelection_coloring_of_ready_scale
    L X 60 (by norm_num) hready hmu_lo hmu_hi ht hX hXscale hsigma hV
      S lam hband (haggregate L hL hXL) hmobius (hreserve L hL hXL)

end RHTower.Sieve
