import GaloisForLFunctions.WorldsOfTheZeroConfiguration.ACountBelowTheDeletionExponentIsARealZero

/-!
# A fake below its top is balanced or has a real top

Let an edit of the rational primes have count `A x + O(x^β)` and a fake zero `ρ₀` with
`β < Re ρ₀`; this holds for every fake zero if `β ≤ 1/2`.

**Theorem** (`balance_or_real_top`).  Either the doubled and the deleted primes have the same
exponent, or the continuation of `(s − 1) ζ_B(s)` vanishes at the real point `κ₋ > 1/2` and every
fake zero has real part at most `κ₋`: a real zero on top.

Proof.  Thickness puts `ρ₀` at or left of `max(κ₊, κ₋)`, so the count exponent is below the
thickness of the edit.  Additions are paid in full: `κ₊ ≤ max(β, κ₋)`, so `κ₊ ≤ κ₋`.  If
`κ₊ < κ₋`, Landau's zero from the count sits at `κ₋`, and thickness bounds every fake zero by
`κ₋`.

So a fake with a count below `√x` and a non-real top (`balance_or_real_top_of_fake`) exists only
at exact balance `κ₊ = κ₋`: every unbalanced edit below `√x` has a real zero on top.
-/

open Complex Metric Filter Topology Finset
open RHTower RHTower.BeurlingDeletion RHTower.BeurlingDeletion.DeletionData
open GaloisForLFunctions.RigidArithmeticOfCuts GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm GaloisForLFunctions.HeckeLFunctions

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration.BalanceLaw

open PrimeEdits TwoSidedEdits NormCount CountFloor

/-- **A count below a fake zero forces balance or a real zero on top.** -/
theorem balance_or_real_top {e : ℕ → ℤ} (he : IsEdit e) {A C β : ℝ} (hA : 0 ≤ A) (hβ : 0 ≤ β)
    (hN : ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β)
    {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hGeq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s) {ρ₀ : ℂ}
    (hρ₀ : 1 / 2 < ρ₀.re) (hρ₀1 : ρ₀ ≠ 1) (hzero : G ρ₀ = 0) (hζ : riemannZeta ρ₀ ≠ 0)
    (hβρ : β < ρ₀.re) :
    expo (plusSet e) = expo (minusSet e) ∨
      (G ((expo (minusSet e) : ℝ) : ℂ) = 0 ∧ 1 / 2 < expo (minusSet e) ∧
        ∀ z : ℂ, z ≠ 1 → G z = 0 → riemannZeta z ≠ 0 → z.re ≤ expo (minusSet e)) := by
  -- thickness: the fake zero lies at or left of the larger exponent
  have hthick := re_le_of_fake_zero he hG hGeq hρ₀1 hzero hζ
  have hmax : ρ₀.re ≤ max (expo (plusSet e)) (expo (minusSet e)) := by
    rcases le_max_iff.mp hthick with h | h
    · exact h
    · linarith
  rcases lt_trichotomy (expo (plusSet e)) (expo (minusSet e)) with hlt | heq | hgt
  · right
    rw [max_eq_right hlt.le] at hmax
    have hκhalf : 1 / 2 < expo (minusSet e) := lt_of_lt_of_le hρ₀ hmax
    have hβκ : β < expo (minusSet e) := lt_of_lt_of_le hβρ hmax
    obtain ⟨G', hG', hG'eq, hG'zero⟩ := zero_at_expo_minus_of_count he hβ hN (max_lt hlt hβκ)
    -- the two continuations agree right of `max(β, 1/2)`
    have hsub₁ : {s : ℂ | max β (1 / 2) < s.re} ⊆ {s : ℂ | 1 / 2 < s.re} :=
      fun z (hz : max β (1 / 2) < z.re) =>
        show 1 / 2 < z.re from lt_of_le_of_lt (le_max_right _ _) hz
    have hsub₂ : {s : ℂ | max β (1 / 2) < s.re} ⊆ {s : ℂ | β < s.re} :=
      fun z (hz : max β (1 / 2) < z.re) =>
        show β < z.re from lt_of_le_of_lt (le_max_left _ _) hz
    have hagree := eqOn_halfPlane (c := max β (1 / 2)) (hG.mono hsub₁) (hG'.mono hsub₂)
      (fun s hs => (hGeq s hs).trans (hG'eq s hs).symm)
      (show ((expo (minusSet e) : ℝ) : ℂ) ∈ {s : ℂ | max β (1 / 2) < s.re} by
        show max β (1 / 2) < ((expo (minusSet e) : ℝ) : ℂ).re
        rw [Complex.ofReal_re]
        exact max_lt hβκ hκhalf)
    refine ⟨hagree.trans hG'zero, hκhalf, fun z hz1 hz hzζ => ?_⟩
    have h1 := re_le_of_fake_zero he hG hGeq hz1 hz hzζ
    rw [max_eq_right hlt.le, max_eq_left hκhalf.le] at h1
    exact h1
  · exact Or.inl heq
  · exfalso
    rw [max_eq_left hgt.le] at hmax
    have h1 := expo_plus_le_max he hA hβ hN
    have h2 : max β (expo (minusSet e)) < expo (plusSet e) :=
      max_lt (lt_of_lt_of_le hβρ hmax) hgt
    linarith

/-- **A fake below `√x` is balanced or has a real zero on top.** -/
theorem balance_or_real_top_of_fake {e : ℕ → ℤ} (he : IsEdit e) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ : β ≤ 1 / 2) (hfake : IsIntegerNormFakeAt (editSystem e) β) :
    expo (plusSet e) = expo (minusSet e) ∨
      ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧
        (∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s) ∧
        G ((expo (minusSet e) : ℝ) : ℂ) = 0 ∧ 1 / 2 < expo (minusSet e) ∧
        ∀ z : ℂ, z ≠ 1 → G z = 0 → riemannZeta z ≠ 0 → z.re ≤ expo (minusSet e) := by
  obtain ⟨-, -, -, ⟨A, C, hA, hN⟩, G, hG, hGeq, ρ₀, hρ₀, hρ₀1, hzero, hζ⟩ := hfake
  rcases balance_or_real_top he hA hβ0 hN hG hGeq hρ₀ hρ₀1 hzero hζ (by linarith) with h | h
  · exact Or.inl h
  · exact Or.inr ⟨G, hG, hGeq, h⟩

end GaloisForLFunctions.WorldsOfTheZeroConfiguration.BalanceLaw
