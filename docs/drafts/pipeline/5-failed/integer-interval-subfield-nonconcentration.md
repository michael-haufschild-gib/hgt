# Integer intervals do not avoid subfield resonance

- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** Argon §3A's claim that rational/integer interval support supplies subfield non-concentration.

**Killing theorem:** `ArithmeticHarmonicAnalysis.exists_integerInterval_sextic_moment_excess` constructs arbitrarily large quadratic prime fields and literal integer intervals with `B³≤q` but `16 M₄≥t q B²`, where `t≍q^(1/6)`. The interval lies entirely in the prime subfield and the sextic character is trivial there.

**Positive survivor:** the exact necessary bound `Σ_x(r n_u(x)−B)^4≤r⁴M₄` preserves every affine-line occupancy imbalance. Coordinate boxes have sharp maximal occupancy `max(|I|,|J|)`, attained by an axis; oblique lines have occupancy at most `min(|I|,|J|)`.

**New insight:** one-coordinate integer intervals and balanced two-coordinate windows have different resonance geometry. Neither geometric non-concentration nor complete-field mean square establishes the remaining signed fourth-moment upper bound.

**Status:** closed paper proofs and Lean declarations are on the [formalized card](../3-formalized/integer-intervals-retain-subfield-resonance.md). This retires the interval shortcut only. The actual Eisenstein detector estimate and improved quasi-RH remain open.
