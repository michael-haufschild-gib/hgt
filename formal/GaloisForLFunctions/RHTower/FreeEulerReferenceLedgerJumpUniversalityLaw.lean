import GaloisForLFunctions.RHTower.LedgerJump
import GaloisForLFunctions.RHTower.RelativeTorsor

/-!
# Free Euler-reference ledger-jump universality law

A finite-Euler reference root is globally nonvanishing and therefore cancels from every chart-root
deck ratio.  Consequently it is invisible not only to a static deck class but to the complete
multiplicity-flux update: adjoining one enclosed zero produces exactly the same ledger jump before
and after reference dressing.
-/

namespace RHTower

open Complex Metric

/-- **Free Euler-reference ledger-jump universality law.**  Dressing all chart roots by any
finite-Euler global root preserves the exact deck-class multiplier contributed by a newly enclosed
zero. -/
theorem freeEulerReference_deckClass_jump
    {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) (m : ι → ℕ)
    {ρ' : ℂ} {m' : ℕ} {f f' h G₁ G₂ H₁ H₂ : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R) {n : ℕ} (hn : 0 < n)
    (hρ : ∀ i ∈ s, ‖ρ i - a‖ ≤ r₀) (hρ' : ‖ρ' - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hfact : ∀ z ∈ ball a R, f z = (∏ i ∈ s, (z - ρ i) ^ m i) * h z)
    (hfact' : ∀ z ∈ ball a R, f' z = (z - ρ') ^ m' * f z)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R))
    (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ n = f z)
    (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ n = f z)
    (hH₁ : AnalyticOnNhd ℂ H₁ (chartRA a r₀ R))
    (hH₂ : AnalyticOnNhd ℂ H₂ (chartLA a r₀ R))
    (hpH₁ : ∀ z ∈ chartRA a r₀ R, H₁ z ^ n = f' z)
    (hpH₂ : ∀ z ∈ chartLA a r₀ R, H₂ z ^ n = f' z)
    (k : ℕ) (P : Finset ℕ) :
    deckClass (fun z => H₁ z * eulerRoot k P z)
        (fun z => H₂ z * eulerRoot k P z)
        (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
        (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) =
      exp (2 * (Real.pi : ℂ) * I * (m' : ℂ) / n) *
        deckClass (fun z => G₁ z * eulerRoot k P z)
          (fun z => G₂ z * eulerRoot k P z)
          (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
          (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) := by
  let pP : ℂ := a + (((r₀ + R) / 2 : ℝ) : ℂ) * I
  let pM : ℂ := a - (((r₀ + R) / 2 : ℝ) : ℂ) * I
  calc
    deckClass (fun z => H₁ z * eulerRoot k P z)
        (fun z => H₂ z * eulerRoot k P z) pP pM =
      deckClass H₁ H₂ pP pM :=
        relative_deckClass_eq k P H₁ H₂ pP pM
    _ = exp (2 * (Real.pi : ℂ) * I * (m' : ℂ) / n) *
        deckClass G₁ G₂ pP pM :=
      deckClass_jump s ρ m h0 hrR hn hρ hρ' hh hh0 hfact hfact'
        hG₁ hG₂ hpG₁ hpG₂ hH₁ hH₂ hpH₁ hpH₂
    _ = exp (2 * (Real.pi : ℂ) * I * (m' : ℂ) / n) *
        deckClass (fun z => G₁ z * eulerRoot k P z)
          (fun z => G₂ z * eulerRoot k P z) pP pM := by
      rw [relative_deckClass_eq k P G₁ G₂ pP pM]

end RHTower
