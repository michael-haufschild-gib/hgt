import GaloisForLFunctions.RHTower.ReflectedGridOffgridBridge
import GaloisForLFunctions.RHTower.WholeLoopClosure

/-!
# Whole-loop reflected-grid deck triviality

The closed-loop incidence theorem produces a paired unit-flux ledger.  The reflected-grid
accounting theorem consumes exactly such a ledger, so the loop's off-grid events cannot change the
canonical completed carrier's level-two deck class.
-/

open Complex

namespace RHTower

/-- **Whole-loop reflected-grid deck-triviality universality law.**  Closed-loop incidence events
are even and flux-paired, their winding has the enclosed analytic-order parity, and adding their
actual unit ledger to any nontrivial completed reflected grid leaves deck level two trivial. -/
theorem incidenceWholeLoop_reflectedGridDeckTriviality
    {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) (m : ι → ℕ)
    (C N : ℕ) (hN : 1 ≤ N)
    {f h G₁ G₂ ℓ₁ ℓ₂ Λ₁ Λ₂ : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ}
    {lo hi : ℝ} {γ : ℝ → ℂ} {Rmod θ : ℝ → ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hρ : ∀ i ∈ s, ‖ρ i - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (Metric.ball a R))
    (hh0 : ∀ z ∈ Metric.ball a R, h z ≠ 0)
    (hfact : ∀ z ∈ Metric.ball a R, f z = (∏ i ∈ s, (z - ρ i) ^ m i) * h z)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R))
    (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ (2 : ℕ) = f z)
    (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ (2 : ℕ) = f z)
    (hℓ₁ : AnalyticOnNhd ℂ ℓ₁ (chartRA a r₀ R))
    (hℓ₂ : AnalyticOnNhd ℂ ℓ₂ (chartLA a r₀ R))
    (hexp₁ : ∀ z ∈ chartRA a r₀ R, Complex.exp (ℓ₁ z) = f z)
    (hexp₂ : ∀ z ∈ chartLA a r₀ R, Complex.exp (ℓ₂ z) = f z)
    (hab : lo < hi)
    (hΛ1ne : ∀ τ ∈ Set.Icc lo hi, Λ₁ (γ τ) ≠ 0)
    (hpolar : ∀ τ ∈ Set.Icc lo hi,
      incidence Λ₁ Λ₂ (γ τ) = (Rmod τ : ℂ) * Complex.exp ((θ τ : ℝ) * I))
    (hRmod : ∀ τ ∈ Set.Icc lo hi, 0 < Rmod τ)
    (hmono : StrictMonoOn θ (Set.Icc lo hi))
    (hθc : ContinuousOn θ (Set.Icc lo hi))
    (hsin : Real.sin (θ lo) ≠ 0)
    (hγ : γ lo = γ hi)
    (hlink :
      ((ℓ₁ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)).im -
          (ℓ₁ (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I)).im) -
        ((ℓ₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)).im -
          (ℓ₂ (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I)).im) = θ hi - θ lo) :
    ∃ (n : ℕ) (e : Fin n → ℝ) (k : ℤ),
      StrictMono e ∧
      (∀ i, e i ∈ Set.Icc lo hi ∧
        pencil Λ₁ Λ₂ ((incidence Λ₁ Λ₂ (γ (e i))).re : ℂ) 1 (γ (e i)) = 0) ∧
      Even n ∧
      LedgerFluxPaired (List.replicate n 1) ∧
      θ hi - θ lo = (k : ℝ) * (2 * Real.pi) ∧
      Even (k - ((∑ i ∈ s, m i : ℕ) : ℤ)) ∧
      deckRed 2 (reflectedGridOffgridCharge C N (List.replicate n 1)) = 1 := by
  obtain ⟨⟨n, e, he, hevents, hneven, hledger⟩,
      ⟨k, hwind, hparity⟩⟩ :=
    incidence_wholeLoop_closure_of_closed s ρ m h0 hrR hρ hh hh0 hfact
      hG₁ hG₂ hpG₁ hpG₂ hℓ₁ hℓ₂ hexp₁ hexp₂ hab hΛ1ne hpolar hRmod
      hmono hθc hsin hγ hlink
  exact ⟨n, e, k, he, hevents, hneven, hledger, hwind, hparity,
    reflectedGridOffgridCharge_deckRed_two_eq_one_of_paired hN hledger⟩

end RHTower
