# Calderón--Witt singular Gamma transgression

- **ID:** deninger-calderon-witt-singular-gamma-transgression
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** Route L apex: source orientation--transgression completeness
- **Statement:** Cross-prime Milnor incidence carries a canonical source-pointed, depth-resolved Gamma transgression whose reflection-balanced kernel is the admitted Hodge sector.

## Goal

Construct the missing boundary-sensitive chain operation without using Xi zeros, divisor-indexed
coefficients, or an RH premise.  The operation must retain both Calderón--Witt legs through
vector-valued multiplication, retain ordered prime and valuation-depth labels, and only then apply
the normalized Haar orientation.  Its reflection-balanced sector must be an explicit submodule of
the all-prime Milnor incidence space.  Divisor points may enter only after construction, by
specializing the free modular parameter to their centered real displacement.

## Gates

- [x] 0 → 1 in-progress: source-pure formula fixed; canonical cross-prime incidence witness fixed
- [ ] 1 → 2 fully-proven: vector transport, witness formula, sector classification, and singularity proved on paper
- [ ] 2 → 3 formalized: Lean theorem module, targeted build green, lint and axiom audit pass
- [ ] 3 → 4 publication-ready: integrate theorem into orientation-transgression paper

## Approach

For every ordered prime pair `p,q`, use the Calderón coordinate on the `p` component and the
algebraic first-suspension packet on the `q` component.  Their alternating cross-effect

```text
delta_p(x_p) T_q(y_q) - delta_p(y_p) T_q(x_q)
```

takes values in the actual vector-valued degree-two center at `q`.  Multiply it by the
source-derived primitive Gamma modular exterior coefficient at depths `e,f`.  Linearization on the
exterior square, followed by restriction to the Milnor kernel, is the singular transgression.

For `p != q`, the wedge of the canonical `p` defect unit and canonical `q` packet unit is an exact
Milnor-incidence relation.  Its vector transport is the primitive Gamma coefficient times the
actual `q` first-suspension unit; its Haar trace is exactly that coefficient.  Applying the
reflection-odd coefficient defines a linear transport.  Its kernel is the concrete admitted
reflection-balanced/Hodge sector.  Prove the canonical witness lies in this sector iff the free
modular displacement is zero.  This is a source theorem; specializing displacement at an Xi point
then gives an RH-equivalent sector-membership statement, not an RH proof.

Next prove analytic singularity: reflected nonzero displacements have exponentially incompatible
depth profiles, so no finite-Rees operator can sew the two transports.  Then connect the
source-derived sector, rather than a sector defined from Xi commutators, to the Gamma/co-Poisson
Green boundary.

## Log

- 2026-08-02 — orientation--transgression completeness identified cross-prime incidence, not a new
  absolute cohomology class, as the only possible carrier.
- 2026-08-02 — fixed source-pure vector-valued nonlocal cross-effect and canonical incidence
  witness; Lean construction started.
