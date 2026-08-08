/-
Off-zero congruence for `L`-series summability.

Comparing two Dirichlet coefficient functions that agree at every nonzero index is the commonest
step in the prime-window and rectangular-Landau layers, and sixteen modules perform it inline: they
apply `Summable.congr` and then split on `n = 0` to rewrite `LSeries.term`.  Mathlib already proves
the term comparison (`LSeries.term_congr`) and the value comparison (`LSeries_congr`); what it does
not expose is the summability comparison in this hypothesis shape — `LSeriesSummable.congr'` asks
for eventual equality instead.

This file supplies it, in one line from the mathlib term comparison.
-/
import Mathlib

/-- **Off-zero congruence for `L`-series summability.**  Two coefficient functions agreeing at every
nonzero index have the same `L`-series terms, so summability transfers.  Mathlib supplies the term
comparison `LSeries.term_congr` and the value comparison `LSeries_congr`, but the summability
comparison only in the eventual-equality form `LSeriesSummable.congr'`. -/
theorem LSeriesSummable.congr_of_ne_zero {f g : ℕ → ℂ} {s : ℂ}
    (h : ∀ {n : ℕ}, n ≠ 0 → f n = g n) (hf : LSeriesSummable f s) : LSeriesSummable g s :=
  hf.congr fun n => LSeries.term_congr h s n

/-- The symmetric form of off-zero congruence. -/
theorem LSeriesSummable.congr_iff_of_ne_zero {f g : ℕ → ℂ} {s : ℂ}
    (h : ∀ {n : ℕ}, n ≠ 0 → f n = g n) : LSeriesSummable f s ↔ LSeriesSummable g s :=
  ⟨LSeriesSummable.congr_of_ne_zero h, LSeriesSummable.congr_of_ne_zero fun hn => (h hn).symm⟩
