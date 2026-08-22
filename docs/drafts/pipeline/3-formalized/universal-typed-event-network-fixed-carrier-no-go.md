# Universal typed-event network fixed-carrier no-go

- **ID:** `universal-typed-event-network-fixed-carrier-no-go`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / UNIVERSAL REPRESENTATION / PHYSICAL NO-GO
- **Paper proof:** `../2-fully-proven/not_new_scientific_knowledge/04-rg-stochastic-quantum-fields/universal-typed-event-network-fixed-carrier-no-go.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.EventNetworkFixedCarrier`
- **Scientific status:** `[FORMALIZED] [REDISCOVERED] [NOT NEW SCIENTIFIC KNOWLEDGE]`

## Formalized statements

For any semiring \(R\), set of event types \(I\), and family of \(R\)-modules \(M_i\), the module

`formal/GaloisForLFunctions/HTGeometry/EventNetworkFixedCarrier.lean`

puts all event carriers into the one algebraic direct sum

\[
W=\bigoplus_{i\in I}M_i
\]

and formalizes the corner lift of every typed linear event \(f:M_i\to M_j\). It proves
unconditionally:

1. `typedEventCornerLift_recover` — source inclusion and target projection recover \(f\) exactly;
2. `typedEventCornerLift_injective` — the lift is faithful;
3. `typedEventCornerLift_comp` — every composable typed history is preserved exactly;
4. `typedEventCornerLift_id` — typed identities become direct-sum corner projections;
5. `typedEventCornerLift_add` — addition of parallel histories is preserved;
6. `typedEventCornerLift_neg` and `typedEventCornerLift_sub` — additive inverses and order
   defects are preserved over rings; and
7. `typedEventCornerLift_smul` — scalar weighting is preserved over commutative semirings.

The composition theorem iterates to every finite history in an arbitrary set-indexed network.

## Audit

Focused final build:

```text
lake build GaloisForLFunctions.HTGeometry.EventNetworkFixedCarrier
✔ [1211/1211] Built GaloisForLFunctions.HTGeometry.EventNetworkFixedCarrier
Build completed successfully (1211 jobs).
```

`#print axioms` was run from `/tmp/EventNetworkFixedCarrierAxioms.lean` for every declaration.
Dependencies are limited to Mathlib's standard extensionality and quotient infrastructure:

```text
propext
Classical.choice
Quot.sound
```

Repository audit:

```text
scripts/formal_tools.py lint
formal lint passed
```

There is no `sorry`, `admit`, project `axiom`, `opaque`, or `unsafe` declaration in the module.

## Exact scope

Lean proves the algebraic direct-sum representation theorem. It does not formalize:

1. the Hilbert direct-sum specialization;
2. the completely-positive trace-class corollary;
3. a physical definition of actualization or possibility;
4. spacelike tensor composition or locality;
5. gravitational dressing; or
6. any claim that gravity or gauge forces arise from carrier comparison.

Those exclusions are substantive. The theorem says that different event-carrier types, arbitrary
network size, exact sequential composition, and linear order defects cannot by themselves witness
fundamental creation of physical possibility.

## Physical boundary

The formal theorem kills the bare-carrier route:

> Every set-indexed typed linear event network has one faithful fixed-carrier realization.

Therefore a physical carrier-creation law needs an admissibility structure not preserved by the
corner realization. The first surviving research target is a monoidal-locality obstruction:
derive causal composition and physical spacelike composition from one event law, then prove that
no fixed-carrier realization preserves both together with gauge invariance and gravitational
dressing.

## Gates

- [x] 0 → 1: exact arbitrary-network fixed-carrier claim
- [x] 1 → 2: dependency-closed paper proof and hostile physics audit
- [x] 2 → 3: unconditional Lean module, focused build, axiom audit, lint
- [ ] 3 → 4: intentionally blocked; theorem is a boundary, not new physics

## Log

- 2026-07-29 — formalized exact recovery, faithfulness, composition, corner identities, additive
  structure, order defects, and scalar weighting for arbitrary set-indexed typed module networks.
