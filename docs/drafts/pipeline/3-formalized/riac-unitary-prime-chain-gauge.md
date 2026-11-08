# Vertical unitary equivalence of completed prime chains

- **ID:** RIAC-unitary-chain-gauge
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** [RIAC](../1-in-progress/renormalized-intersection-arithmetic-counts.md), completed topology
- **Statement:** The prescribed diagonal Hilbert completion retains unitary Dirichlet gauge equivalence along every vertical line, in every exterior degree.
- **Lean:** [UnitaryPrimeChainGauge.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/UnitaryPrimeChainGauge.lean)

## Exact result

Embed the actual finite prime exterior chains by the canonical face coefficients
of `G_(δ/2)a` in face `ℓ²`. The squared norm is exactly
`Σ_S (∏_(p∈S)p^δ)|a_S|²`. This embedding is injective and dense for every
real `δ` and every degree, including the augmented empty-face degree.

Multiplication by `∏_(p∈S)p^(it)` defines an explicit unitary in every degree
and agrees with the original finite Dirichlet gauge. The actual boundary
satisfies `d_(s+it)G_(it)=G_(it)d_s`. The adjacent-degree product unitary
maps each finite boundary graph and its closure onto the graph and closure
at `s+it`. Up to this explicit unitary, the closed relation depends only on
`Re(s)`. No boundedness or closability assumption is used.

## Proof and positive survivor

The existing canonical exterior basis and invertible real gauge give
faithfulness and density. Imaginary prime multipliers have norm one, so
`HTGeometry.lpPhaseUnitary` gives the completed gauge. Koszul naturality
supplies the original boundary comparison. Homeomorphisms transport graph
closures exactly.

The positive survivor is the explicit classification of these weighted graph
closures, retaining every arithmetic differential and exterior degree.
Prescribed diagonal conductor weights alone cannot distinguish imaginary
zero locations through invariants preserved by this unitary equivalence.
Additional relative or equivariant structure must supplement the construction.

## Prior work and verification

ESG already supplies the canonical exterior basis, algebraic gauges and cutoff
compatibility. `BiarithmeticGaugeGeometry.PrimeGaugeTorusAndVacuumIntertwiners`
supplies earlier phase invariance. `RHTower.PrimeFaceBoundaryGauge` trivializes
the row-summability graph family in the product topology for all complex
parameters. The present result proves the prescribed Hilbert norm and actual
exterior graph-closure comparison.

Production file passed its direct Lean check and all ten transitive axiom
audits; dependencies use only `propext`, `Classical.choice`, `Quot.sound`.
No completed zero-detection theorem follows.
