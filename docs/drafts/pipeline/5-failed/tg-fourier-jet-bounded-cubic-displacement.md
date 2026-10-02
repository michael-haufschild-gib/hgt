# TG-C9.7: bounded cubic displacement fails

- **ID:** TG-C9.7-20261002-01a0-negative
- **Stage:** 5-failed
- **Positive survivor:** `../3-formalized/tg-fourier-jet-theta-cubic-classification.md`

The proposed bounded extension of the actual theta displacement cube `(Q-N)³` fails
at every nonzero theta parameter, even on any fixed prime's literal finite depth core.
Both input and output graph coordinates are retained. The exact algebraic reduction
is `(Q-N)³=c²(Q-N)`, with unbounded-neutral coefficient -2c⁴ and only bounded identity
and swap terms remaining. Actual tanh injectivity identifies c=0 exactly with a=0.

The strongest nontrivial positive survivor is NOT merely the zero-parameter case:
every prime admits a positive balancing parameter where Q itself is bounded and
every finite packet's COMPLETE Gram-modular cubic vanishes, despite the unbounded
displacement cube on that same prime core. A common parameter balances at most one
prime. All these statements have dependency-closed paper proofs and passed production
Lean and axiom audits; exact evidence is on the positive card.

This retires bounded nontrivial displacement, not the complete cubic or route TG.
No Gamma–Xi, Hardy-index or sub-unit producer follows.
