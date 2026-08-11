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
    exact (mul_le_mul_iff_right₀ hPpos).mp hscaled
  obtain ⟨u, hune, hulower, huupper, hucard, hulength, hularge⟩ :=
    exists_heathBrown_box_dyadic_robust_group L X k m a b q hT0 ht
      (hshort m hm q hq b hb a ha) (htotal m hm q hq b hb a ha) s hcoreLarge
  exact ⟨m, hm, q, hq, b, hb, a, ha, u, hune, hulower, huupper,
    hucard, hulength, hularge⟩

/-- Predicate asserting that one finite selection label realizes the complete pointwise conclusion
at `s`. -/
def IsHeathBrownAggregateSelection
    (L X k : ℕ) {T0 t e : ℝ} (s : ℂ)
    (label : HeathBrownSelectionLabel L X k) : Prop :=
  let c := label.1
  let u := label.2
  u.Nonempty ∧
    let alpha := ∑ i ∈ u,
      dyadicLogExponent T0
        (heathBrownBoxFactorExponent c.a c.b c.q i)
    t ≤ alpha ∧ alpha < 4 * t ∧
      u.card ≤ Fintype.card (HeathBrownBoxFactorIndex k c.m) ∧
      ((groupedDyadicLower
        (fun i : {i // i ∈ u} =>
          heathBrownBoxFactorExponent c.a c.b c.q i) : ℕ) : ℝ) = T0 ^ alpha ∧
      ((groupedDyadicLower
        (fun i : {i // i ∈ u} =>
          heathBrownBoxFactorExponent c.a c.b c.q i) : ℕ) : ℝ) ^ e ≤
        ‖∏ i : {i // i ∈ u}, LSeries
          (complexCoeff (arithmeticDyadicBlock
            (heathBrownFactorBase L X (heathBrownBoxFactorKind k c.m i))
            (heathBrownBoxFactorExponent c.a c.b c.q i))) s‖

/-- Pointwise capstone in finite-label form. -/
theorem exists_heathBrownAggregateSelection_label
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
    ∃ label : HeathBrownSelectionLabel L X k,
      IsHeathBrownAggregateSelection L X k (T0 := T0) (t := t) (e := e) s label := by
  obtain ⟨m, hm, q, hq, b, hb, a, ha, u, hune, hulower, huupper,
    hucard, hulength, hularge⟩ :=
      exists_heathBrown_aggregate_dyadic_robust_group L X k hk hT0 ht s
        haggregate hshort htotal hreserve
  let c : HeathBrownBoxChoice L X k :=
    ⟨⟨m, Finset.mem_range.mp hm⟩,
      ⟨q, Finset.mem_range.mp hq⟩, ⟨b, hb⟩, ⟨a, ha⟩⟩
  let label : HeathBrownSelectionLabel L X k := ⟨c, u⟩
  refine ⟨label, ?_⟩
  dsimp [IsHeathBrownAggregateSelection, label, c,
    HeathBrownBoxChoice.m, HeathBrownBoxChoice.q,
    HeathBrownBoxChoice.a, HeathBrownBoxChoice.b]
  exact ⟨hune, hulower, huupper, hucard, hulength, hularge⟩

/-- The selection-label type is inhabited whenever the packet has positive order. -/
theorem nonempty_heathBrownSelectionLabel
    (L X k : ℕ) (hk : 0 < k) : Nonempty (HeathBrownSelectionLabel L X k) := by
  let m : Fin k := ⟨0, hk⟩
  let q : Fin (Nat.log 2 X + 1) := ⟨0, by omega⟩
  let b : Fin (k - (m : ℕ) - 1) → ℕ := fun _ => 0
  let a : Fin (k - (m : ℕ)) → ℕ := fun _ => 0
  have hb : b ∈ dyadicChoiceSet (k - (m : ℕ) - 1) X := by
    simp [b, dyadicChoiceSet]
  have ha : a ∈ dyadicChoiceSet (k - (m : ℕ)) L := by
    simp [a, dyadicChoiceSet]
  exact ⟨⟨⟨m, q, ⟨b, hb⟩, ⟨a, ha⟩⟩, ∅⟩⟩

/-- **Uniform finite coloring of a large ordinate set.**  One selection label may be chosen at
every ordinate simultaneously; outside `S` an arbitrary fixed label is used. -/
theorem exists_heathBrownAggregateSelection_coloring
    (L X k : ℕ) (hk : 0 < k) {T0 t e V : ℝ}
    (hT0 : 1 < T0) (ht : 0 < t) (S : Finset ℕ) (s : ℕ → ℂ)
    (haggregate : ∀ r ∈ S, V ≤ ‖heathBrownDyadicAggregate L X k (s r)‖)
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
    ∃ color : ℕ → HeathBrownSelectionLabel L X k,
      ∀ r ∈ S, IsHeathBrownAggregateSelection L X k
        (T0 := T0) (t := t) (e := e) (s r) (color r) := by
  classical
  have hpoint : ∀ r : ℕ, r ∈ S →
      ∃ label : HeathBrownSelectionLabel L X k,
        IsHeathBrownAggregateSelection L X k
          (T0 := T0) (t := t) (e := e) (s r) label := by
    intro r hr
    exact exists_heathBrownAggregateSelection_label L X k hk hT0 ht (s r)
      (haggregate r hr) hshort htotal hreserve
  choose selected hselected using hpoint
  let fallback : HeathBrownSelectionLabel L X k :=
    Classical.choice (nonempty_heathBrownSelectionLabel L X k hk)
  let color : ℕ → HeathBrownSelectionLabel L X k := fun r =>
    if hr : r ∈ S then selected r hr else fallback
  refine ⟨color, ?_⟩
  intro r hr
  simpa [color, hr] using hselected r hr

end RHTower.Sieve
