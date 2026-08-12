import GaloisForLFunctions.RHTower.Sieve.MaynardEligibleAggregate

/-!
# Perron-relevant eligible Heath--Brown aggregate

Smooth Perron weights supported through `X` cannot see a literal dyadic box whose multiplicative
lower edge exceeds `X`.  Large-value selection must therefore occur after removing those boxes;
otherwise a pointwise-large but integrally invisible box can be selected.  This module defines the
correct restricted aggregate and proves its exact selector.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- Grouped-factor lower edge is literally the coefficient-support lower edge of the same box. -/
theorem groupedDyadicLower_heathBrownBoxFactorExponent_eq_coreLower
    {k m : ℕ} (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ) (q : ℕ) :
    groupedDyadicLower (heathBrownBoxFactorExponent a b q) =
      heathBrownDyadicCoreLower (k - m) a b q := by
  simp [groupedDyadicLower, heathBrownBoxFactorExponent, heathBrownDyadicCoreLower,
    mul_assoc]

/-- A literal box can contribute to a coefficient prefix through `X`. -/
def IsHeathBrownBoxPerronRelevant
    (X k : ℕ) {L : ℕ} (box : HeathBrownBoxChoice L X k) : Prop :=
  groupedDyadicLower
    (heathBrownBoxFactorExponent box.a box.b box.q) ≤ X

/-- Eligible aggregate with every pointwise term also Perron-relevant. -/
def heathBrownPerronRelevantEligibleDyadicAggregate
    (L X k : ℕ) (T0 t : ℝ) (s : ℂ) : ℂ := by
  classical
  exact ∑ box : HeathBrownBoxChoice L X k,
    if IsHeathBrownBoxEligible L X k T0 t box ∧
        IsHeathBrownBoxPerronRelevant X k box then
      heathBrownBoxTerm L X k box s
    else 0

/-- **Perron-relevant aggregate selection.**  A positive large value selects a box that is both
eligible for robust grouping and capable of contributing below the Perron cutoff. -/
theorem exists_large_perronRelevant_eligible_heathBrownBox
    (L X k : ℕ) (hk : 0 < k) (T0 t : ℝ) (s : ℂ) {V : ℝ}
    (hV : 0 < V)
    (hlarge : V ≤
      ‖heathBrownPerronRelevantEligibleDyadicAggregate L X k T0 t s‖) :
    ∃ box : HeathBrownBoxChoice L X k,
      IsHeathBrownBoxEligible L X k T0 t box ∧
      IsHeathBrownBoxPerronRelevant X k box ∧
      V ≤ (Fintype.card (HeathBrownBoxChoice L X k) : ℝ) *
        ‖heathBrownBoxTerm L X k box s‖ := by
  classical
  letI : Nonempty (HeathBrownBoxChoice L X k) :=
    nonempty_heathBrownBoxChoice L X k hk
  let f : HeathBrownBoxChoice L X k → ℂ := fun box =>
    if IsHeathBrownBoxEligible L X k T0 t box ∧
        IsHeathBrownBoxPerronRelevant X k box then
      heathBrownBoxTerm L X k box s
    else 0
  have hsum : heathBrownPerronRelevantEligibleDyadicAggregate L X k T0 t s =
      ∑ box ∈ (Finset.univ : Finset (HeathBrownBoxChoice L X k)), f box := by
    simp [heathBrownPerronRelevantEligibleDyadicAggregate, f]
  obtain ⟨box, _hbox, hbox⟩ := exists_mem_card_mul_norm_ge
    (Finset.univ : Finset (HeathBrownBoxChoice L X k)) Finset.univ_nonempty f
      (hlarge.trans_eq (congrArg norm hsum))
  have hboth : IsHeathBrownBoxEligible L X k T0 t box ∧
      IsHeathBrownBoxPerronRelevant X k box := by
    by_contra hnot
    simp [f, hnot] at hbox
    linarith
  refine ⟨box, hboth.1, hboth.2, ?_⟩
  simpa [f, hboth] using hbox

theorem perronRelevant_heathBrownBox_coreLower_le
    {L X k : ℕ} {box : HeathBrownBoxChoice L X k}
    (hbox : IsHeathBrownBoxPerronRelevant X k box) :
    (groupedDyadicLower
      (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ≤ X := by
  exact_mod_cast hbox

end RHTower.Sieve
