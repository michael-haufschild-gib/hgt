# Route R operator-topology compactness dichotomy

- **ID:** route-r-operator-topology-compactness-dichotomy
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Route R cross-prime Stokes--Calkin prequotient comparison, C3f
- **Statement:** No topology on the fixed physical operator space can both keep the compact ideal closed and compactly approximate a nonneutral Route R `(2,3)` receiver.

## Goal

Close every topology-only repair of the external polar/compression handoff at once, rather than
checking norm, strong, weak, or intermediate topologies separately.

## Gates

- [x] 0 → 1 in-progress: exact topology-independent claim and actual receiver specialization
- [x] 1 → 2 fully-proven: dependency-closed proof below
- [x] 2 → 3 formalized: `RouteROperatorTopologyCompactnessDichotomy`, targeted build and axiom audit green
- [ ] 3 → 4 publication-ready

## Exact theorem

Let `H` be Route R's fixed physical Hilbert space, `B(H)` its bounded operators, and
`C ⊆ B(H)` its compact ideal. Give `B(H)` an arbitrary topology `τ`. If `C` is `τ`-closed and
`T ∈ closure_τ(C)`, then `T ∈ C`.

For positive aperture `A` and nonzero horizontal grade `a`, let `T_(A,a)` be the fixed `(2,3)`
Stokes--Sonin commutator. Then no topology `τ` satisfies both

```text
C is τ-closed,
T_(A,a) ∈ closure_τ(C).
```

For the norm topology, sequential compact approximability of `T_(A,a)` is equivalent to `a=0`;
on every Xi divisor fibre this property is globally equivalent to RH.

## Complete proof

Closedness gives `closure_τ(C) ⊆ C`; therefore `T ∈ closure_τ(C)` implies `T ∈ C`. The established
Route R Calkin classification says `T_(A,a)` is compact iff `a=0`. Hence for `a≠0`, simultaneous
closedness and compact approximability are impossible.

In operator norm, compact operators form a closed set. Thus any norm-convergent sequence of compact
operators has compact limit. Conversely a compact operator is the constant norm limit of itself,
so norm compact-approximability is equivalent to compactness. Substituting the fixed receiver gives
equivalence with `a=0`. Substituting each Xi centred rate and using the already proved global
compactness classification gives equivalence with RH. No further premise occurs.

## No-go closure

- **Exact killing theorem/mechanism:** Approximation plus closedness already forces compactness; the
  actual nonneutral receiver is explicitly noncompact.
- **Strongest positive survivor:** Exact topology dichotomy. Strong/weak compact approximation is
  possible only because compact operators are not closed there; a compactness-detecting topology
  cannot approximate the nonneutral receiver by compact stages.
- **New insight:** No intermediate or newly named operator topology can repair Route R merely by
  changing convergence. Any surviving producer must add source-specific tightness or prove
  compactness directly, rather than infer it from topological approximation.
- **Status:** `[BRIDGE] [LEAN-PROVED]` in
  `RHTower/RouteROperatorTopologyCompactnessDichotomy.lean`; targeted module build green; five
  public theorems use only `[propext, Classical.choice, Quot.sound]`.

## Log

- 2026-08-13 — C3f strong-approximation counterexample generalized to arbitrary operator topology;
  complete closure proof recorded.
- 2026-08-13 — exact theorem formalized, wired into `RHTower.lean`, targeted build and axiom audit
  green; moved to Stage 3.
