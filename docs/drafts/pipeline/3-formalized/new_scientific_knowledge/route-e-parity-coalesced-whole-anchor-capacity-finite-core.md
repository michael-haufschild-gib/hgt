# Route E parity-coalesced whole-anchor capacity finite core

- **ID:** `ROUTE-E-PARITY-COALESCED-WHOLE-ANCHOR-CAPACITY-FINITE-CORE-001`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / EXACT FINITE ARITHMETIC AND CAPACITY CORE
- **Scientific status:** `[LEAN-PROVED] [BRIDGE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parents:**
  - `../../2-fully-proven/new_scientific_knowledge/route-e-parity-coalesced-full-mass-reservoir-cube-law.md`
  - `../../2-fully-proven/new_scientific_knowledge/route-e-whole-anchor-capacity-displacement-conservation-law.md`
- **RH used:** no
- **Computation used:** no

## Exact theorem package

Explicit shift packets classify finite parity coalescence. Every odd source arity admits full-mass
packets with total drifts `+1` and `-1`. Every even source arity at least four admits coalesced
odd-coordinate packets with both drifts while merged coordinate has shift `-1`. At arity two,
robust coalescence has exactly one downward shift. Coordinatewise sign reversal across an odd
packet reverses product sign, and every partial grade stays within coordinate count.

For whole-anchor multiplication, Lean also proves:

- exact addition of three prime factors by a coprime E3 token;
- exact recovery of reservoir from separated prime band;
- combined opposite-Möbius-sign and cofactor-scaled displacement packet;
- full-subset reciprocal reservoir mass equals finite Euler product;
- a column ceiling `C` forces `card(anchor) ≤ C card(target)`;
- target cardinality below source cardinality forces a column load strictly above one.

## Lean certificate

Modules:

```text
GaloisForLFunctions.RHTower.MobiusParityCoalescedFullMassCube
GaloisForLFunctions.RHTower.MobiusWholeAnchorCapacityDisplacement
```

Principal declarations:

```text
exists_twoSided_fullMass_shiftPackets_of_odd
exists_twoSided_fullMass_shiftPackets_of_even
two_activeBlocks_coalesce_to_downward_singleton
prod_coordinateReversals_eq_neg_of_odd
wholeAnchorE3_exact_packet
wholeAnchor_fullReservoirMass_eq_eulerProduct
FiniteRowStochasticKernel.card_anchor_le_columnCeiling_mul_card_target
FiniteRowStochasticKernel.not_all_columns_le_one_of_card_target_lt
```

Both modules are directly imported by `GaloisForLFunctions.RHTower`. Direct source checks pass;
axiom audit reports only standard quotient/classical axioms.

## Exact boundary

Sparse-forbidden token supply, global E3 capacity, reciprocal-prime Mertens asymptotics, physical
co-degree, mixed Gibbs cost, and normalized seam flux are not consequences of finite packet laws.
They remain Stage 2 arithmetic producers.

## Log

- 2026-08-12 — corpus-growth audit verified and promoted exact parity/whole-anchor finite core.
