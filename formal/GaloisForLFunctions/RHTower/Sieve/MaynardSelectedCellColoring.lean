import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellTrichotomy
import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedRaise

/-!
# Finite coloring by complete Route-T selected cells

One finite label fixes box, selected subset, exponent, and trichotomy branch.  This is the exact
uniformity needed to apply one adjacent raising power on every color fibre.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

def maynardSubHeightSelectedExponent {L X k : ℕ} (T : ℝ)
    (label : HeathBrownSelectionLabel L X k) : ℝ :=
  ∑ i ∈ label.2, dyadicLogExponent T
    (heathBrownBoxFactorExponent label.1.a label.1.b label.1.q i)

def IsMaynardSelectedCellBranch {L X : ℕ} (T mu alpha : ℝ)
    (label : HeathBrownSelectionLabel L X 60) : Prop :=
  let beta := maynardSubHeightSelectedExponent T label
  beta ≤ 5 / 12 ∨
    (5 / 12 < beta ∧ beta < 1 ∧ alpha ≤ 997 / 1000 ∧
      ∃ j ∈ label.2,
        (heathBrownBoxFactorKind 60 label.1.m j = .zeta ∨
          heathBrownBoxFactorKind 60 label.1.m j = .log) ∧
        beta - 2 * (mu / 120) < dyadicLogExponent T
          (heathBrownBoxFactorExponent label.1.a label.1.b label.1.q j)) ∨
    (1 ≤ beta ∧ alpha ≤ 99 / 100 ∧
      ∃ j ∈ label.2,
        (heathBrownBoxFactorKind 60 label.1.m j = .zeta ∨
          heathBrownBoxFactorKind 60 label.1.m j = .log) ∧
        1 - 2 * (mu / 120) < dyadicLogExponent T
          (heathBrownBoxFactorExponent label.1.a label.1.b label.1.q j))

def IsMaynardWindowRelevantSelectedCell
    (L X : ℕ) (T mu N0 c y alpha : ℝ)
    (label : HeathBrownSelectionLabel L X 60) : Prop :=
  let beta := maynardSubHeightSelectedExponent T label
  IsHeathBrownBoxEligible L X 60 T (mu / 120) label.1 ∧
    IsHeathBrownBoxWindowRelevant N0 X 60 label.1 ∧
    (groupedDyadicLower
      (heathBrownBoxFactorExponent label.1.a label.1.b label.1.q) : ℝ) ^
        (alpha - c) ≤
      ‖heathBrownDyadicCoreProduct L X 60 label.1.m
        label.1.a label.1.b label.1.q
        ((c : ℂ) + (y : ℝ) * Complex.I)‖ ∧
    label.2.Nonempty ∧
    (∀ i ∈ label.2, dyadicLogExponent T
      (heathBrownBoxFactorExponent label.1.a label.1.b label.1.q i) < 1) ∧
    mu / 120 ≤ beta ∧ beta < 1 + 2 * (mu / 120) ∧
    ((groupedDyadicLower (heathBrownSelectedExponent label) : ℕ) : ℝ) = T ^ beta ∧
    ((groupedDyadicLower (heathBrownSelectedExponent label) : ℕ) : ℝ) ^
        (alpha - c) ≤
      ‖∏ i : HeathBrownSelectedFactor label, LSeries
        (complexCoeff (arithmeticDyadicBlock
          (heathBrownFactorBase L X (heathBrownSelectedKind label i))
          (heathBrownSelectedExponent label i)))
            ((c : ℂ) + (y : ℝ) * Complex.I)‖ ∧
    IsMaynardSelectedCellBranch T mu alpha label

set_option maxHeartbeats 1000000 in
theorem eventually_exists_maynardWindowRelevantSelectedCell_label :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, 4 / 3 ≤ mu → mu ≤ 19 / 9 →
        (X : ℝ) ≤ T ^ mu → ∀ L : ℕ, 1 ≤ L →
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
          ∃ label : HeathBrownSelectionLabel L X 60,
            IsMaynardWindowRelevantSelectedCell L X T mu N0 c y alpha label := by
  filter_upwards [eventually_exists_windowRelevant_subHeight_cell_trichotomy]
    with T hT
  intro X hX mu hmuLo hmuHi hXscale L hL c y alpha V N0 hc hylo hyupper
    halpha hV hmobius haggregate hreserve
  obtain ⟨box, helig, hrel, hcore, u, hune, husub, hbetaLo, hbetaHi,
      hlength, hlarge, hbranch⟩ :=
    hT X hX mu hmuLo hmuHi hXscale L hL c y alpha V N0 hc hylo hyupper
      halpha hV hmobius haggregate hreserve
  let label : HeathBrownSelectionLabel L X 60 := ⟨box, u⟩
  refine ⟨label, ?_⟩
  dsimp only [IsMaynardWindowRelevantSelectedCell]
  refine ⟨helig, hrel, hcore, hune, husub, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [maynardSubHeightSelectedExponent, label] using hbetaLo
  · simpa [maynardSubHeightSelectedExponent, label] using hbetaHi
  · simpa [maynardSubHeightSelectedExponent, label,
      heathBrownSelectedExponent] using hlength
  · simpa [label, heathBrownSelectedExponent, heathBrownSelectedKind,
      HeathBrownSelectedFactor] using hlarge
  · simpa [IsMaynardSelectedCellBranch, maynardSubHeightSelectedExponent, label] using hbranch

set_option maxHeartbeats 1000000 in
/-- Uniform finite coloring of any ordinate set by complete selected-cell labels. -/
theorem eventually_exists_maynardWindowRelevantSelectedCell_coloring :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, 4 / 3 ≤ mu → mu ≤ 19 / 9 →
        (X : ℝ) ≤ T ^ mu → ∀ L : ℕ, 1 ≤ L →
        ∀ c alpha V N0 : ℝ, 0 ≤ c → 3 / 4 ≤ alpha → 0 < V →
        ∀ S : Finset ℕ, ∀ y : ℕ → ℝ,
          (∀ r ∈ S, T ≤ y r ∧ y r ≤ 2 * T) →
          (∀ box : HeathBrownBoxChoice L X 60,
            ∀ i : HeathBrownBoxFactorIndex 60 box.m,
              heathBrownBoxFactorKind 60 box.m i = .moebius →
                dyadicLogExponent T
                  (heathBrownBoxFactorExponent box.a box.b box.q i) ≤
                    2 * (mu / 120)) →
          (∀ r ∈ S, V ≤ ‖heathBrownWindowRelevantEligibleDyadicAggregate
            L X 60 T (mu / 120) N0
              ((c : ℂ) + (y r : ℝ) * Complex.I)‖) →
          (∀ box : HeathBrownBoxChoice L X 60,
            IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
            IsHeathBrownBoxWindowRelevant N0 X 60 box →
              heathBrownEligibleBoxCost L X 60 *
                (groupedDyadicLower
                  (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
                    (alpha - c) ≤ V) →
          ∃ color : ℕ → HeathBrownSelectionLabel L X 60,
            ∀ r ∈ S, IsMaynardWindowRelevantSelectedCell
              L X T mu N0 c (y r) alpha (color r) := by
  filter_upwards [eventually_exists_maynardWindowRelevantSelectedCell_label]
    with T hpoint
  intro X hX mu hmuLo hmuHi hXscale L hL c alpha V N0 hc halpha hV
    S y hy hmobius haggregate hreserve
  classical
  have hchoose : ∀ r : ℕ, r ∈ S →
      ∃ label : HeathBrownSelectionLabel L X 60,
        IsMaynardWindowRelevantSelectedCell
          L X T mu N0 c (y r) alpha label := by
    intro r hr
    exact hpoint X hX mu hmuLo hmuHi hXscale L hL c (y r) alpha V N0 hc
      (hy r hr).1 (hy r hr).2 halpha hV hmobius (haggregate r hr) hreserve
  choose selected hselected using hchoose
  let fallback : HeathBrownSelectionLabel L X 60 :=
    Classical.choice (nonempty_heathBrownSelectionLabel L X 60 (by norm_num))
  let color : ℕ → HeathBrownSelectionLabel L X 60 := fun r =>
    if hr : r ∈ S then selected r hr else fallback
  refine ⟨color, ?_⟩
  intro r hr
  simpa [color, hr] using hselected r hr

end RHTower.Sieve
