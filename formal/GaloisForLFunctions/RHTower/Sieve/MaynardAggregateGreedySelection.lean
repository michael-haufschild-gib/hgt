import GaloisForLFunctions.RHTower.Sieve.MaynardSelectionLabels

/-!
# Pointwise smooth-aggregate to robust Huxley group

This capstone composes every pointwise selection step.  A large smooth signed aggregate selects one
literal box after its exact polylog/binomial cost.  If that cost times the box-scale threshold is
below the aggregate threshold, cancellation leaves the unsigned box large enough.  Robust greedy
grouping then selects one literal Möbius/zeta/log subproduct in the widened exponent window.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- Exact pointwise loss paid in passing from the signed aggregate to one unsigned box core. -/
def heathBrownAggregateBoxCost (L X k m : ℕ) : ℝ :=
  (k : ℝ) * (((Nat.log 2 X + 1 : ℕ) : ℝ) ^ (k - m)) *
    (((Nat.log 2 L + 1 : ℕ) : ℝ) ^ (k - m)) * (2 ^ k : ℝ)

theorem heathBrownAggregateBoxCost_pos
    {L X k m : ℕ} (hk : 0 < k) : 0 < heathBrownAggregateBoxCost L X k m := by
  dsimp [heathBrownAggregateBoxCost]
  positivity

/-- **Complete pointwise aggregate-to-group selection.**  All choices are literal and all losses
are explicit. -/
theorem exists_heathBrown_aggregate_dyadic_robust_group
    (L X k : ℕ) (hk : 0 < k) {T0 t e V : ℝ}
    (hT0 : 1 < T0) (ht : 0 < t) (s : ℂ)
    (haggregate : V ≤ ‖heathBrownDyadicAggregate L X k s‖)
    (hshort : ∀ m ∈ Finset.range k,
      ∀ q ∈ Finset.range (Nat.log 2 X + 1),
      ∀ b ∈ dyadicChoiceSet (k - m - 1) X,
      ∀ a ∈ dyadicChoiceSet (k - m) L,
      ∀ i : HeathBrownBoxFactorIndex k m,
        dyadicLogExponent T0 (heathBrownBoxFactorExponent a b q i) ≤ 2 * t)
    (htotal : ∀ m ∈ Finset.range k,
      ∀ q ∈ Finset.range (Nat.log 2 X + 1),
      ∀ b ∈ dyadicChoiceSet (k - m - 1) X,
      ∀ a ∈ dyadicChoiceSet (k - m) L,
        t ≤ ∑ i : HeathBrownBoxFactorIndex k m,
          dyadicLogExponent T0 (heathBrownBoxFactorExponent a b q i))
    (hreserve : ∀ m ∈ Finset.range k,
      ∀ q ∈ Finset.range (Nat.log 2 X + 1),
      ∀ b ∈ dyadicChoiceSet (k - m - 1) X,
      ∀ a ∈ dyadicChoiceSet (k - m) L,
        heathBrownAggregateBoxCost L X k m *
          (groupedDyadicLower (heathBrownBoxFactorExponent a b q) : ℝ) ^ e ≤ V) :
    ∃ m ∈ Finset.range k,
      ∃ q ∈ Finset.range (Nat.log 2 X + 1),
        ∃ b ∈ dyadicChoiceSet (k - m - 1) X,
          ∃ a ∈ dyadicChoiceSet (k - m) L,
            ∃ u : Finset (HeathBrownBoxFactorIndex k m), u.Nonempty ∧
              let alpha := ∑ i ∈ u,
                dyadicLogExponent T0 (heathBrownBoxFactorExponent a b q i)
              t ≤ alpha ∧ alpha < 4 * t ∧
                u.card ≤ Fintype.card (HeathBrownBoxFactorIndex k m) ∧
                ((groupedDyadicLower
                  (fun i : {i // i ∈ u} => heathBrownBoxFactorExponent a b q i) : ℕ) : ℝ) =
                    T0 ^ alpha ∧
                ((groupedDyadicLower
                  (fun i : {i // i ∈ u} => heathBrownBoxFactorExponent a b q i) : ℕ) : ℝ) ^ e ≤
                  ‖∏ i : {i // i ∈ u}, LSeries
                    (complexCoeff (arithmeticDyadicBlock
                      (heathBrownFactorBase L X (heathBrownBoxFactorKind k m i))
                      (heathBrownBoxFactorExponent a b q i))) s‖ := by
  obtain ⟨m, hm, q, hq, b, hb, a, ha, hcoreBound⟩ :=
    exists_large_heathBrownDyadicCoreProduct L X k hk s haggregate
  let P := heathBrownAggregateBoxCost L X k m
  have hcoreBound' : V ≤ P * ‖heathBrownDyadicCoreProduct L X k m a b q s‖ := by
    simpa [P, heathBrownAggregateBoxCost, mul_assoc] using hcoreBound
  have hscaled := (hreserve m hm q hq b hb a ha).trans hcoreBound'
  have hPpos : 0 < P := heathBrownAggregateBoxCost_pos hk
  have hcoreLarge :
      (groupedDyadicLower (heathBrownBoxFactorExponent a b q) : ℝ) ^ e ≤
        ‖heathBrownDyadicCoreProduct L X k m a b q s‖ := by
    exact (mul_le_mul_left hPpos).mp hscaled
  obtain ⟨u, hune, hulower, huupper, hucard, hulength, hularge⟩ :=
    exists_heathBrown_box_dyadic_robust_group L X k m a b q hT0 ht
      (hshort m hm q hq b hb a ha) (htotal m hm q hq b hb a ha) s hcoreLarge
  exact ⟨m, hm, q, hq, b, hb, a, ha, u, hune, hulower, huupper,
    hucard, hulength, hularge⟩

end RHTower.Sieve
