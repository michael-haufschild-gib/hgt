import GaloisForLFunctions.Core

/-!
# Freeness of the diagonal prime-torus orbit — additive corollaries (Tier A)

The canonical finite-character obstruction for the diagonal flow `t ↦ (p^{-it})_p`
on `𝕋^∞` is the `ℚ`-linear independence of `{log p}`, formalized in
`GaloisForLFunctions.linearIndependent_log_primes`.

This file adds two genuinely-additive citable forms built **on** that theorem, in the
field's own vocabulary:

* `logPrime_linearIndependent_int` — the `ℤ`-coefficient form, exported from `Core`;
* `logPrime_no_rat_relation` — the field-readable "no diagonal resonance" form: there is no
  nontrivial finite `ℚ`-relation `Σ q_p · log p = 0`.

Nothing here is conjectural: it is unique factorization in linear-independence vocabulary —
the finite additive coordinate of the field. Infinite torus closure, difference-Galois group
dimension, RH, and positivity/reality statements are not formalized in this file.
-/

open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

/-- Field-readable form: **no nontrivial finite `ℚ`-resonance** among the prime logarithms.
This is the finite-character statement derived from `linearIndependent_log_primes`. -/
theorem logPrime_no_rat_relation
    (s : Finset Nat.Primes) (g : Nat.Primes → ℚ)
    (h : ∑ p ∈ s, g p • Real.log (p : ℕ) = 0) :
    ∀ p ∈ s, g p = 0 :=
  linearIndependent_iff'.mp linearIndependent_log_primes s g h

end

end GaloisForLFunctions
