# L fixed-reader operator-relation rigidity

- **ID:** L-FROR
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) `[BRIDGE]`
- **Source:** L-CHR positive survivor; Route L fixed Burnol/Deninger reader
- **Statement:** A quotient-descending target eigenreader can read a covariant relation class only when its target eigenvalue equals the source scalar holonomy.

## Goal

Kill L's operator-valued/noncommutative multivalued-correspondence escape while physical reader remains fixed. Chain: Gamma-six holonomy → arbitrary target operator relation → descended invariant physical reader with nonzero value → trivial holonomy → critical line.

## Gates

- [x] 0 → 1: corpus/literature audit and falsifiers
- [x] 1 → 2: dependency-closed paper proof
- [x] 2 → 3: closed Lean theorem, targeted build, axiom audit, umbrella wiring
- [ ] 3 → 4: publication audit

## Exact candidate and attack

For `R≤X×Y`, reader `tau:Y→k`, and outputs `y,y'`, assume `(x,y)∈R`, `(u*x,y')∈R`, `tau` kills vertical ambiguity, `tau(y')=v*tau(y)`, and `tau(y)≠0`. Subtract `u*(x,y)` from the covariant pair. The difference is vertical, so `(v-u)tau(y)=0`; hence `u=v`. No target operator is needed.

For Gamma-six use `u=sourceHorizontalGammaSixPhysicalHolonomy q`, fixed-reader eigenvalue `v=1`; corpus proves `u=1 ↔ Re(q)=1/2`.

**Hostile boundary:** result fails if reader does not descend, its target eigenvalue moves with `q`, or relation is non-real-linear. Those are exactly reader-changing/domain-changing survivors. Existing all-gauge single-valued polar no-go is stronger in naturality and weaker in target/relation generality; no corpus duplicate found.

**Lean result:** `sourceHorizontalGammaSixPhysical_fixedReader_relation_nonzero_forces_criticalLine` in `SourceHorizontalGammaSixFixedReaderRelationNoGo`; direct check and targeted build pass. Axioms: `propext`, `Classical.choice`, `Quot.sound` only. Heavy generic descent import was removed; direct check fell from 52s to 9s and targeted build from 83s to 58s.

## Positive survivor

Operator-valued/noncommutative dynamics cannot help if fixed physical reader is invariant and well-defined on relation quotient. Survivor must change reader holonomy, make vertical ambiguity physically readable (thereby abandoning quotient descent), or use non-real-linear/domain-changing semantics.
