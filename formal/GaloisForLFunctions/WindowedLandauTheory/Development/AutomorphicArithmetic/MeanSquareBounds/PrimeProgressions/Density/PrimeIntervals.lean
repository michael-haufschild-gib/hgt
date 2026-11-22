import Mathlib

/-! Finite prime intervals in real coordinates. -/

open Finset

namespace QH.PrimeProgressions

/-- The primes in the half-open interval `(x,y]`. -/
noncomputable def primesIoc (x y : ℝ) : Finset ℕ := (Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime

theorem mem_primesIoc {x y : ℝ} (hx : 0 ≤ x) {p : ℕ} :
    p ∈ primesIoc x y ↔ x < p ∧ (p : ℝ) ≤ y ∧ p.Prime := by
  rw [primesIoc, Finset.mem_filter, Finset.mem_Ioc, Nat.floor_lt hx]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, (Nat.le_floor_iff' h3.ne_zero).1 h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, Nat.le_floor h2⟩, h3⟩

end QH.PrimeProgressions
