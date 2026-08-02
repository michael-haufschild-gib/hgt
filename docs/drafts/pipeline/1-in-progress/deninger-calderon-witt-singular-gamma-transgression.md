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
- [x] 1 → 2 fully-proven: vector transport, witness formula, sector classification, singularity, and finite-support Gamma/Hardy boundary comparison proved on paper
- [x] 2 → 3 formalized: Lean theorem modules, targeted builds green, Route L reachability and axiom audit pass
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
- 2026-08-02 — constructed unconditional vector and scalar reflection-odd transports on global
  finite-support Milnor incidence.  The canonical cross-prime witness is admitted exactly at zero
  modular displacement.  Reflected sewing cost is exponential and dominates every finite
  polynomial/Rees order.
- 2026-08-02 — compared transport with actual polarized Euler boundary.  Pair action
  `-(r_i+r_j)=2(h_i+h_j)` is positive.  Weighted Gamma-head/Hardy-tail pairing of the transported
  common test has exact Cauchy response.  Differentiating literal moving head and translated tail
  gives `(E,-E)`, with `E` equal to oriented Calderón--Witt Green transport.  Hodge rotation
  squares to `-1` and exchanges head/tail energy on every labelled source Green primitive.
- 2026-08-02 — proved actual boundary reflection defect equals source reflection-odd transport;
  admitted sector is exactly its kernel.  Canonical cross-prime orientation equals the confluent
  Gamma/co-Poisson exterior.
- 2026-08-02 — Lean module
  `DeningerCalderonWittGammaCoPoissonHodgeBoundaryComparison.lean` direct-compiled and targeted
  build passed.  Key theorems use only `propext`, `Classical.choice`, and `Quot.sound`.  Global
  lint remains red only because concurrently added unrelated modules are not wired into their
  umbrellas; Route L comparison module itself is reachable and contains no forbidden
  declarations.
- 2026-08-02 — constructed
  `DeningerCalderonWittCompletedXiGreenIncidenceComparison.lean`.  Finite Xi jets now multiply the
  actual nonzero cross-prime incidence witness, and normalized Gamma orientation recovers every
  coefficient.  Their induced completion is canonically isometric to the completed Xi comparison
  model.  Completed Green comparison is continuous, isometric on norms, dense, finite-test exact,
  and Frobenius-compatible.  Direct Lean, targeted module build, and axiom audit passed; Route L
  modules are wired into both theorem-area umbrellas.
- 2026-08-02 — audited `riemann-hellinger-hodge-green-descent/main.tex`.  Its safe endpoint
  expectation reaches the completed Xi scalar trace but explicitly gives no boundary-domain
  control at a zero.  Thus completed incidence Hilbert transport is only carrier infrastructure.
  Missing map is a graph-norm lift of the source-side Green current into the unbounded
  Hellinger--Hodge defect domain.

## Exact remaining frontier

Finite-support source construction, Gamma/co-Poisson comparison, and the typed completed
incidence carrier are closed.  They do not imply RH.  Historical
`deningerArithmeticSourceGreen` remains a Xi-divisor comparison-model operator, not an
independently constructed arithmetic Green operator.  Missing scientific theorem is a
source-side, labelled graph-norm estimate carrying the prime-power endpoint Green current into
the unbounded Hellinger--Hodge defect domain at every Xi divisor fibre.  Concretely it must prove
finite tail energy before scalar orientation; local Lean rigidity then forces zero displacement.
Assuming this membership, deriving it from a bounded Hilbert isometry, or restating it as a
divisor/Hodge/RH equivalence receives no closure credit.
