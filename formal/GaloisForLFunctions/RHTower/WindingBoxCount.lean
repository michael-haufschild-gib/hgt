/-
The boundary-arc winding integer has the parity of the enclosed order.

The deck class of a pair of square roots on the two annulus charts is computed two ways for the same
enclosed configuration.  The argument-variation dictionary gives it as `(−1)^k`, where `2πk` is the
two-arc winding mismatch of a logarithm of the member; the box-count gives it as `deckRed 2 (Σ m)`,
the mod-two reduction of the enclosed total order.  Since `deckRed 2 j = (−1)^j`, the two readings
force `(−1)^k = (−1)^(Σ m)`: the winding integer and the enclosed order have the same parity.

This wires the boundary-arc winding integer — the rigid datum that replaces the steerable endpoint
orientations — to the enclosed zero count.  The winding integer's parity is not free: it is the
parity of the total order of the zeros the loop encloses.
-/
import GaloisForLFunctions.RHTower.ArcWindingDictionary
import GaloisForLFunctions.RHTower.SignatureParity
import GaloisForLFunctions.RHTower.DeckMultiZero

open Complex

namespace RHTower

/-- The level-two deck reduction is the sign of the parity: `deckRed 2 j = (−1)^j`. -/
theorem deckRed_two_eq_neg_one_zpow (j : ℤ) : deckRed 2 j = (-1 : ℂ) ^ j := by
  unfold deckRed
  rw [show 2 * (Real.pi : ℂ) * I * (j : ℂ) / ((2 : ℕ) : ℂ) = (j : ℂ) * (Real.pi * I) from by
    push_cast; ring, Complex.exp_int_mul, Complex.exp_pi_mul_I]

/-- Equal signs force equal parity: `(−1)^k = (−1)^j → Even (k − j)`. -/
theorem even_sub_of_neg_one_zpow_eq {k j : ℤ} (h : (-1 : ℂ) ^ k = (-1 : ℂ) ^ j) :
    Even (k - j) := by
  have hne : (-1 : ℂ) ≠ 0 := by norm_num
  have h1 : (-1 : ℂ) ^ (k - j) = 1 := by
    rw [zpow_sub₀ hne, h, ← zpow_sub₀ hne, sub_self, zpow_zero]
  rcases Int.even_or_odd (k - j) with he | ho
  · exact he
  · exact absurd (by rw [ho.neg_one_zpow] at h1; exact h1) (by norm_num)

/-- **The boundary-arc winding integer has the parity of the enclosed order.**  For an enclosed
factorization `f = (∏_{i∈s} (·−ρ i)^{m i})·h` on a ball around `a` with `h` analytic and nonvanishing,
square roots `G₁ G₂` on the two annulus charts, and logarithms `ℓ₁ ℓ₂` of `f` on those charts, the
two-arc winding mismatch integer `k` — `2πk` the difference of the argument variations of `ℓ₁` and
`ℓ₂` between the annulus basepoints — satisfies `(−1)^k = (−1)^(Σ m)`, so `k` and the enclosed total
order `Σ m` have the same parity.  The rigid winding datum is pinned, mod two, to the enclosed zero
count: it is the box-count read through the argument variation instead of the endpoint signs. -/
theorem arcWinding_parity_eq_enclosedOrder {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) (m : ι → ℕ)
    {f h G₁ G₂ ℓ₁ ℓ₂ : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hρ : ∀ i ∈ s, ‖ρ i - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (Metric.ball a R)) (hh0 : ∀ z ∈ Metric.ball a R, h z ≠ 0)
    (hfact : ∀ z ∈ Metric.ball a R, f z = (∏ i ∈ s, (z - ρ i) ^ m i) * h z)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ 2 = f z) (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ 2 = f z)
    (hℓ₁ : AnalyticOnNhd ℂ ℓ₁ (chartRA a r₀ R)) (hℓ₂ : AnalyticOnNhd ℂ ℓ₂ (chartLA a r₀ R))
    (hexp₁ : ∀ z ∈ chartRA a r₀ R, Complex.exp (ℓ₁ z) = f z)
    (hexp₂ : ∀ z ∈ chartLA a r₀ R, Complex.exp (ℓ₂ z) = f z) :
    ∃ k : ℤ,
      ((ℓ₁ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)).im - (ℓ₁ (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I)).im)
          - ((ℓ₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)).im
              - (ℓ₂ (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I)).im) = k * (2 * Real.pi) ∧
      (-1 : ℂ) ^ k = (-1 : ℂ) ^ ((∑ i ∈ s, m i : ℕ) : ℤ) ∧
      Even (k - ((∑ i ∈ s, m i : ℕ) : ℤ)) := by
  obtain ⟨hPmem, hMmem⟩ := annulus_basepoints_mem h0 hrR
  -- the box-count reading of the deck class
  have hbox := box_charge_eq_deckRed s ρ m h0 hrR (n := 2) two_pos hρ hh hh0 hfact
    hG₁ hG₂ hpG₁ hpG₂
  -- the argument-variation reading of the deck class
  obtain ⟨k, hwind, harc⟩ := deckClass_neg_one_zpow_arg_variation
    (isOpen_chartRA a r₀ R) (isPreconnected_chartRA a h0)
    (isOpen_chartLA a r₀ R) (isPreconnected_chartLA a h0)
    hG₁ hG₂ hpG₁ hpG₂ hℓ₁ hℓ₂ hexp₁ hexp₂ hPmem.1 hPmem.2 hMmem.1 hMmem.2
  refine ⟨k, hwind, ?_, ?_⟩
  · have heq : (-1 : ℂ) ^ k = deckRed 2 (((∑ i ∈ s, m i : ℕ)) : ℤ) := by rw [← harc, hbox]
    rw [heq, deckRed_two_eq_neg_one_zpow]
  · exact even_sub_of_neg_one_zpow_eq (by
      have heq : (-1 : ℂ) ^ k = deckRed 2 (((∑ i ∈ s, m i : ℕ)) : ℤ) := by rw [← harc, hbox]
      rw [heq, deckRed_two_eq_neg_one_zpow])

end RHTower
