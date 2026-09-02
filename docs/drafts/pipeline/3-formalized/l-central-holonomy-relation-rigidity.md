# L central-holonomy relation rigidity

- **ID:** L-CHR
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) `[BRIDGE]`
- **Source:** `rh-current-frontier-map.md` route L correspondence escape
- **Statement:** A scalar-covariant real-linear relation with nonzero target quotient support exists only when source and target holonomies agree.

## Goal

Kill L's multivalued/noncommutative linear-correspondence escape before the fixed Burnol/Deninger reader. Chain: Gamma-six physical holonomy → source/fixed-target relation → nonvertical physical quotient → trivial holonomy → critical line; universally over Xi copies, RH. This does not assume physical descent.

## Gates

- [x] 0 → 1: corpus and primary-literature audit; exact route class and survivor identified
- [x] 1 → 2: dependency-closed paper proof
- [x] 2 → 3: closed Lean theorem, targeted build, axiom audit, umbrella wiring
- [ ] 3 → 4: publication audit

## Exact candidate and attack

Let `R ≤ X × Y` be a vector-space relation over a field. Assume `(x,y)∈R ⇒ (u x,v y)∈R`. If `u≠v`, subtract `u(x,y)` from the covariant pair and divide by `v-u`; then `(0,y)∈R`. Hence any nonvertical output forces `u=v`. Conversely common-scalar covariance is automatic. Apply `u=sourceHorizontalGammaSixPhysicalHolonomy q`, `v=1`; corpus proves `u=1 ↔ Re(q)=1/2`.

**Falsifiers checked:** zero/full-vertical relations are excluded only by explicit nonvertical support; closedness, boundedness, single-valuedness, topology, complex-linearity, commutativity, and finite dimension are absent. Existing second-Cartier pointed-Krein relation survives because source and target carry matched non-scalar two-leg transfers, not mismatched central scalars.

**Novelty claim:** elementary scalar-character rigidity is not claimed new. New result sought is closure of the corpus-specific L correspondence lane. Linear-relation literature treats multivalued/operator decompositions but the audit found no Gamma-six/Burnol holonomy application.

**Lean result:** `sourceHorizontalGammaSixPhysical_fixedTarget_relationCovariance_iff_criticalLine` in `SourceHorizontalGammaSixCentralScalarRelationNoGo`; targeted build passes. Axioms: `propext`, `Classical.choice`, `Quot.sound` only.

## Positive survivor

Noncommutativity or multivaluedness alone cannot help while physical holonomy remains central scalar and target fibre is fixed. Survivor must use matched non-scalar/operator-valued holonomy, nonlinear/non-real-linear transport, or domain/fibre change.
