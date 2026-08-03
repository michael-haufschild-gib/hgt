import GaloisForLFunctions.RHTower.MobiusReciprocalMarkerBlockCount

/-!
# The contribution of a marker block

Since the target set has cardinality `∑_{p ∈ P} #(C p)` exactly — the pair-to-product map being
injective — a uniform lower bound on the cofactor counts gives a lower bound on the number of
targets:

`#P · c ≤ #(markerBlockTargets P C)`   whenever `c ≤ #(C p)` for every `p ∈ P`.

In the application `c = (3/16)DL` comes from the sign-count conclusion at a good start, and `#P` is
the number of retained markers, so this is the step that converts "many good starts" into "many
distinct targets".
-/

namespace RHTower.Sieve

open Finset

/-- **The block contributes at least `#P · c` distinct targets.** -/
theorem card_markerBlockTargets_ge (P : Finset ℕ) (C : ℕ → Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hpos : ∀ p ∈ P, ∀ a ∈ C p, 0 < a)
    (hsmall : ∀ p ∈ P, ∀ a ∈ C p, ∀ r ∈ P, a < r)
    {c : ℝ} (hc : ∀ p ∈ P, c ≤ (((C p).card : ℕ) : ℝ)) :
    (P.card : ℝ) * c ≤ (((RHTower.markerBlockTargets P C).card : ℕ) : ℝ) := by
  classical
  have hcard : ((RHTower.markerBlockTargets P C).card : ℕ) = ∑ p ∈ P, (C p).card :=
    RHTower.card_markerBlockTargets P C hprime hpos hsmall
  rw [hcard]
  have hsum : ∑ p ∈ P, c ≤ ∑ p ∈ P, (((C p).card : ℕ) : ℝ) := Finset.sum_le_sum hc
  have hconst : ∑ _p ∈ P, c = (P.card : ℝ) * c := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcast : ((∑ p ∈ P, (C p).card : ℕ) : ℝ) = ∑ p ∈ P, (((C p).card : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hcast, ← hconst]
  exact hsum

end RHTower.Sieve
