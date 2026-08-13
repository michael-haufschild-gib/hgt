import GaloisForLFunctions.RHTower.Sieve.MaynardOverweightZetaLogExclusion

/-!
# Complete selected-cell trichotomy for Route T

Every large window-relevant aggregate now selects exactly one of three analytically closed cell
types: a small cell with fixed adjacent-power reserve, a moderate cell excluded from the last
`3/1000` of amplitude by order four, or an overweight cell excluded above `983/1000` by order three.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

set_option maxHeartbeats 1000000 in
/-- **Complete pointwise Route-T cell classification.**  No selected exponent or equality seam
remains outside one of the three proved count regimes. -/
theorem eventually_exists_windowRelevant_subHeight_cell_trichotomy :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, 4 / 3 ≤ mu → mu ≤ 19 / 9 →
        (X : ℝ) ≤ T ^ mu →
        ∀ L : ℕ, 1 ≤ L →
        ∀ c y alpha V N0 : ℝ, 0 ≤ c → T ≤ y → y ≤ 2 * T →
          3 / 4 ≤ alpha → 0 < V →
          (∀ box : HeathBrownBoxChoice L X 60,
            ∀ i : HeathBrownBoxFactorIndex 60 box.m,
              heathBrownBoxFactorKind 60 box.m i = .moebius →
                dyadicLogExponent T
                  (heathBrownBoxFactorExponent box.a box.b box.q i) ≤
                    2 * (mu / 120)) →
          V ≤ ‖heathBrownWindowRelevantEligibleDyadicAggregate
            L X 60 T (mu / 120) N0
              ((c : ℂ) + (y : ℝ) * Complex.I)‖ →
          (∀ box : HeathBrownBoxChoice L X 60,
            IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
            IsHeathBrownBoxWindowRelevant N0 X 60 box →
              heathBrownEligibleBoxCost L X 60 *
                (groupedDyadicLower
                  (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
                    (alpha - c) ≤ V) →
          ∃ box : HeathBrownBoxChoice L X 60,
            IsHeathBrownBoxEligible L X 60 T (mu / 120) box ∧
            IsHeathBrownBoxWindowRelevant N0 X 60 box ∧
            (groupedDyadicLower
              (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
                (alpha - c) ≤
              ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
                ((c : ℂ) + (y : ℝ) * Complex.I)‖ ∧
            ∃ u : Finset (HeathBrownBoxFactorIndex 60 box.m), u.Nonempty ∧
              (∀ i ∈ u, dyadicLogExponent T
                (heathBrownBoxFactorExponent box.a box.b box.q i) < 1) ∧
              let beta := ∑ i ∈ u, dyadicLogExponent T
                (heathBrownBoxFactorExponent box.a box.b box.q i)
              mu / 120 ≤ beta ∧ beta < 1 + 2 * (mu / 120) ∧
                ((groupedDyadicLower (fun i : {i // i ∈ u} =>
                  heathBrownBoxFactorExponent box.a box.b box.q i) : ℕ) : ℝ) =
                    T ^ beta ∧
                ((groupedDyadicLower (fun i : {i // i ∈ u} =>
                  heathBrownBoxFactorExponent box.a box.b box.q i) : ℕ) : ℝ) ^
                    (alpha - c) ≤
                  ‖∏ i : {i // i ∈ u}, LSeries
                    (complexCoeff (arithmeticDyadicBlock
                      (heathBrownFactorBase L X
                        (heathBrownBoxFactorKind 60 box.m i))
                      (heathBrownBoxFactorExponent box.a box.b box.q i)))
                        ((c : ℂ) + (y : ℝ) * Complex.I)‖ ∧
                (beta ≤ 5 / 12 ∨
                  (5 / 12 < beta ∧ beta < 1 ∧ alpha ≤ 997 / 1000 ∧
                    ∃ j ∈ u,
                      (heathBrownBoxFactorKind 60 box.m j = .zeta ∨
                        heathBrownBoxFactorKind 60 box.m j = .log) ∧
                      beta - 2 * (mu / 120) < dyadicLogExponent T
                        (heathBrownBoxFactorExponent box.a box.b box.q j)) ∨
                  (1 ≤ beta ∧ alpha ≤ 983 / 1000 ∧
                    ∃ j ∈ u,
                      (heathBrownBoxFactorKind 60 box.m j = .zeta ∨
                        heathBrownBoxFactorKind 60 box.m j = .log) ∧
                      1 - 2 * (mu / 120) < dyadicLogExponent T
                        (heathBrownBoxFactorExponent box.a box.b box.q j))) := by
  filter_upwards [eventually_exists_windowRelevant_subHeight_group,
    eventually_maynard_perronRelevant_moderate_global_amplitude_le_997,
    eventually_maynard_perronRelevant_overweight_global_amplitude_le_nineEightyThree_div_thousand]
      with T hselect hmoderate hoverweight
  intro X hX mu hmuLo hmuHi hXscale L hL c y alpha V N0 hc hylo hyupper
    halpha hV hmobius haggregate hreserve
  obtain ⟨box, helig, hrel, hcore, u, hune, husub, hbetaLo, hbetaHi,
      hlength, hlarge, hlocal, hheight⟩ :=
    hselect X hX mu hmuLo hmuHi hXscale L hL c y alpha V N0 hc hylo hyupper
      halpha hV hmobius haggregate hreserve
  let beta := ∑ i ∈ u, dyadicLogExponent T
    (heathBrownBoxFactorExponent box.a box.b box.q i)
  have hlocalKind (hbeta : 5 / 12 < beta) : ∃ j ∈ u,
      (heathBrownBoxFactorKind 60 box.m j = .zeta ∨
        heathBrownBoxFactorKind 60 box.m j = .log) ∧
      beta - 2 * (mu / 120) < dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q j) := by
    obtain ⟨j, hju, hjweight⟩ := hlocal
    refine ⟨j, hju, ?_, by simpa [beta] using hjweight⟩
    cases hkind : heathBrownBoxFactorKind 60 box.m j with
    | moebius =>
        have hjupper := hmobius box j hkind
        exfalso
        dsimp only [beta] at hbeta
        linarith
    | zeta => exact Or.inl rfl
    | log => exact Or.inr rfl
  by_cases hsmall : beta ≤ 5 / 12
  · exact ⟨box, helig, hrel, hcore, u, hune, husub, hbetaLo, hbetaHi,
      hlength, hlarge, Or.inl hsmall⟩
  · have hbeta : 5 / 12 < beta := lt_of_not_ge hsmall
    by_cases hregular : beta < 1
    · obtain ⟨j, hju, hkind, hjweight⟩ := hlocalKind hbeta
      have halpha997 := hmoderate X hX mu hmuLo hmuHi hXscale L hL 60 box
        helig hrel.1 c y alpha beta hc hylo hyupper hbeta j hkind hjweight hcore
      exact ⟨box, helig, hrel, hcore, u, hune, husub, hbetaLo, hbetaHi,
        hlength, hlarge, Or.inr (Or.inl
          ⟨hbeta, hregular, halpha997, j, hju, hkind, hjweight⟩)⟩
    · have hbetaOne : 1 ≤ beta := le_of_not_gt hregular
      rcases hheight with hfalse | ⟨j, hju, hkind, hjweight⟩
      · exact (hregular hfalse).elim
      · have halpha983 := hoverweight X hX mu hmuLo hmuHi hXscale L hL 60 box
          helig hrel.1 c y alpha hc hylo hyupper j hkind hjweight hcore
        exact ⟨box, helig, hrel, hcore, u, hune, husub, hbetaLo, hbetaHi,
          hlength, hlarge, Or.inr (Or.inr
            ⟨hbetaOne, halpha983, j, hju, hkind, hjweight⟩)⟩

end RHTower.Sieve
