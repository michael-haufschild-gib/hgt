# Relation--incidence horizon fusion

- **ID:** ULF-RIHF-001
- **Stage:** 3-formalized
- **Lean:** `RHTower.IntegralNuclearRelationIncidenceHorizon`
- **Paper:** `2-fully-proven/universal-law-field/direct-subunit-anchor/relation-incidence-horizon-fusion.md`

Lean proves unconditionally:

```text
Mul(Tot_delta(R)) = Mul(R) inter ker(delta).
```

At a supplied strict-right Xi copy, the completed Meyer scalar vertical fibre maps onto exactly
the one-dimensional all-cross-prime incidence kernel `C eta`.  Its rank-one projector fixes
`eta`, has rank at most one, belongs to Schatten class one, and has operator trace and trace norm
exactly `1`.

This is a target-fibre theorem, not a pre-divisor source landing and not an RH proof.

Axiom audit: `propext`, `Classical.choice`, `Quot.sound` only.
