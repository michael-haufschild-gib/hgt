import GaloisForLFunctions.RHTower.Sieve.PowerWindowMatching

/-!
# The square-root barrier of the marker construction

The positive results reach windows of length any fixed power of the height above `1/2`.  That
exponent is not an artefact of the estimates: it is forced by the geometry.

Unique decoding requires every cofactor to be smaller than every marker, so a cofactor `a` of a
marker `p` satisfies `X < a·p < p²`, putting the markers above `√X`.  If a single cell contains two
cofactors, their products differ by at least `p`, so the window has length at least `p`.  Hence

`X < H²`

as soon as one cell is not a singleton — the construction cannot address a window shorter than the
square root of its height.
-/

namespace RHTower.Sieve

open Finset

/-- **The square-root barrier.**  A cell with two cofactors forces the window to be longer than
`√X`. -/
theorem sq_lt_of_two_mem_cell {X H : ℕ} {P : Finset ℕ} {C : ℕ → Finset ℕ} {p : ℕ}
    (hp : p ∈ P) (hprime : ∀ q ∈ P, q.Prime)
    (hw : ∀ q ∈ P, ∀ a ∈ C q, X < a * q ∧ a * q ≤ X + H)
    (hsmall : ∀ q ∈ P, ∀ a ∈ C q, ∀ r ∈ P, a < r)
    {a b : ℕ} (ha : a ∈ C p) (hb : b ∈ C p) (hab : a ≠ b) :
    X < H * H := by
  have hpos : 0 < p := (hprime p hp).pos
  obtain ⟨hXa, haH⟩ := hw p hp a ha
  obtain ⟨hXb, hbH⟩ := hw p hp b hb
  -- the two products differ by at least one marker, so `p ≤ H`
  have hpH : p ≤ H := by
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · have hstep : a * p + p ≤ b * p := by
        have hle : (a + 1) * p ≤ b * p := Nat.mul_le_mul_right p (by omega)
        calc a * p + p = (a + 1) * p := by ring
          _ ≤ b * p := hle
      linarith
    · have hstep : b * p + p ≤ a * p := by
        have hle : (b + 1) * p ≤ a * p := Nat.mul_le_mul_right p (by omega)
        calc b * p + p = (b + 1) * p := by ring
          _ ≤ a * p := hle
      linarith
  -- a cofactor is below its marker, so the height is below the square of the marker
  have hap : a < p := hsmall p hp a ha p hp
  have hsq : a * p < p * p := (Nat.mul_lt_mul_right hpos).2 hap
  have hHH : p * p ≤ H * H := Nat.mul_le_mul hpH hpH
  linarith

/-- **The barrier in the window form.**  With `H ≤ √X` no cell of a marker block has two
cofactors, so every marker contributes at most one target. -/
theorem card_cell_le_one_of_sq_le {X H : ℕ} {P : Finset ℕ} {C : ℕ → Finset ℕ} {p : ℕ}
    (hp : p ∈ P) (hprime : ∀ q ∈ P, q.Prime)
    (hw : ∀ q ∈ P, ∀ a ∈ C q, X < a * q ∧ a * q ≤ X + H)
    (hsmall : ∀ q ∈ P, ∀ a ∈ C q, ∀ r ∈ P, a < r)
    (hbar : H * H ≤ X) :
    (C p).card ≤ 1 := by
  classical
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hcon
  exact absurd hbar (not_le.2 (sq_lt_of_two_mem_cell hp hprime hw hsmall ha hb hab))

end RHTower.Sieve
