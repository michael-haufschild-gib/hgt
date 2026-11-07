# Fourth-trace payment of a wider zero gap

- **Stage:** 2-fully-proven; final ordinary Lean audit pending.
- **Statement:** Every multiplicity copy of a zero of Xi satisfies `12<|Im ρ|`.
- **Source:** The corpus fourth reciprocal trace is below `9/100000`; its individual atoms are nonnegative and invariant under conjugation.

Conjugation pairs distinct zero copies because no Xi zero has zero ordinate. Thus twice any fourth reciprocal atom is bounded by the complete trace. If `|Im ρ|≤12`, verified height 67 puts `ρ` on the critical line. Its reciprocal atom is `1/(Im ρ)^4`, so the trace is at least `2/12^4>9/100000`, a contradiction.

This strengthens the interval available for a product-based Xi minorant. It does not yet provide that minorant or a further rank payment.

Lean: `ThetaCuspSections/FourthTraceZeroGap.lean`. The module check passed; transitive axioms are exactly `propext`, `Classical.choice`, `Quot.sound`. The final ordinary audit remains pending.
