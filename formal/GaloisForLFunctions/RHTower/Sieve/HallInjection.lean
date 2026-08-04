import GaloisForLFunctions.RHTower.Sieve.MarkerBlockLower
import GaloisForLFunctions.RHTower.Sieve.CellMatching

/-!
# The Hall injection for a marker block

Combining the block contribution with the cell matching: if every retained marker carries at least
`c` cofactors and the source primes number at most `#P · c`, then the sources inject into the targets
inside the same window, moving nothing further than `H`.

This is step 4 of the argument — "matching inside disjoint cells yields a literal injection with
displacement at most `H(X)`" — as a statement about an actual map.  The source bound is what
Brun–Titchmarsh supplies and the target bound is what the sign-count conclusion supplies.
-/

namespace RHTower.Sieve

open Finset

/-- The block sits inside a window as soon as each cell does. -/
theorem markerBlockTargets_mem_window {X H : ℕ} {P : Finset ℕ} {C : ℕ → Finset ℕ}
    (hw : ∀ p ∈ P, ∀ a ∈ C p, X < a * p ∧ a * p ≤ X + H) :
    ∀ n ∈ RHTower.markerBlockTargets P C, X < n ∧ n ≤ X + H := by
  classical
  intro n hn
  rw [RHTower.markerBlockTargets, Finset.mem_image] at hn
  obtain ⟨x, hx, rfl⟩ := hn
  rw [Finset.mem_sigma] at hx
  exact hw x.1 hx.1 x.2 hx.2

/-- **The Hall injection.** -/
theorem exists_hall_injection {X H : ℕ} (P : Finset ℕ) (C : ℕ → Finset ℕ) (sources : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hposC : ∀ p ∈ P, ∀ a ∈ C p, 0 < a)
    (hsmall : ∀ p ∈ P, ∀ a ∈ C p, ∀ r ∈ P, a < r)
    {c : ℝ} (hc : ∀ p ∈ P, c ≤ (((C p).card : ℕ) : ℝ))
    (hsrc : ((sources.card : ℕ) : ℝ) ≤ (P.card : ℝ) * c)
    (htwin : ∀ n ∈ RHTower.markerBlockTargets P C, X < n ∧ n ≤ X + H)
    (hswin : ∀ n ∈ sources, X < n ∧ n ≤ X + H) :
    ∃ f : ℕ → ℕ, Set.InjOn f ↑sources
      ∧ (∀ x ∈ sources, f x ∈ RHTower.markerBlockTargets P C)
      ∧ ∀ x ∈ sources, |(f x : ℤ) - (x : ℤ)| ≤ (H : ℤ) := by
  classical
  have hblock := card_markerBlockTargets_ge P C hprime hposC hsmall hc
  have hcard : sources.card ≤ (RHTower.markerBlockTargets P C).card := by
    have hR : ((sources.card : ℕ) : ℝ)
        ≤ (((RHTower.markerBlockTargets P C).card : ℕ) : ℝ) := le_trans hsrc hblock
    exact_mod_cast hR
  exact exists_injOn_displacement_le (X := X) (H := H) hcard hswin htwin

end RHTower.Sieve
