import GaloisForLFunctions.HTGeometry.BorelWeil.Realization
import GaloisForLFunctions.HTGeometry.BorelWeil.Vanishing

/-!
# The dominance criterion for Borel–Weil sections

Combining the realization of dominant weights by products of leading principal minors with the
rank-one vanishing theorem gives the exact criterion: over an infinite field, the Borel–Weil line
bundle on the flag variety of `SL(N,k)` has a nonzero global section precisely for the dominant
(antitone) weights.

## Main results

* `GaloisForLFunctions.HTGeometry.BorelWeil.bwSections_ne_bot_iff_antitone`
* `GaloisForLFunctions.HTGeometry.BorelWeil.bwSections_eq_bot_iff_not_antitone`
-/

namespace GaloisForLFunctions.HTGeometry.BorelWeil

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

/-- **Borel–Weil dominance criterion.**  The space of sections of the line bundle attached to a
weight `lam` is nonzero exactly when `lam` is dominant. -/
theorem bwSections_ne_bot_iff_antitone {lam : Fin N → ℕ} :
    bwSections (k := k) lam ≠ ⊥ ↔ Antitone lam := by
  constructor
  · intro h
    by_contra hcon
    exact h (bwSections_eq_bot_of_not_antitone hcon)
  · exact bwSections_ne_bot_of_antitone

theorem bwSections_eq_bot_iff_not_antitone {lam : Fin N → ℕ} :
    bwSections (k := k) lam = ⊥ ↔ ¬ Antitone lam := by
  rw [← not_iff_not, not_not]
  exact bwSections_ne_bot_iff_antitone

end GaloisForLFunctions.HTGeometry.BorelWeil
