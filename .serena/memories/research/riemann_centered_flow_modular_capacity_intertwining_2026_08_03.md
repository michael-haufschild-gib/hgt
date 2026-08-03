Centered-flow capacity conservation/intertwining is CLOSED in the covariant sense.

New module:
formal/GaloisForLFunctions/RHTower/RiemannCenteredFlowCapacityIntertwining.lean

New exact object:
- xiCenteredFlowOrderCapacity rho tau r: factorially normalized derivative-order energy of actual Xi residue Cayley mode.
- xiCenteredFlowRawCapacity rho tau: total over every derivative order.
- xiCenteredFlowSourceCountercharacter rho tau = exp(riemannReflectedSourceEntropy rho * tau).
- xiCenteredFlowConservedCapacity = countercharacter * raw capacity.

Main unconditional laws:
- xiCenteredFlowOrderCapacity_eq: order capacity = multiplicity mass * exp(source rate*tau) * Poisson weight.
- xiCenteredFlowRawCapacity_eq: total raw capacity = multiplicity^2 * exp((2 Re rho - 1)*tau).
- xiCenteredFlowRawCapacity_add: exact centered-flow character intertwining.
- xiCenteredFlowSourceCountercharacter_add: inverse source character is a multiplicative cocycle.
- xiCenteredFlowConservedCapacity_eq_multiplicityMass: prime-tail entropy cancels raw flow exactly, leaving squared multiplicity.
- xiCenteredFlowConservedCapacity_add: exact time invariance.
- static raw capacity at a fibre iff unsquared boundary fracture vanishes.
- global static capacity iff RH.
- global source countercharacter triviality iff RH.

Scientific correction:
The missing object was not conservation itself. Covariant positive conservation exists unconditionally and is source-derived. Remaining arithmetic theorem is triviality of the modular cocycle (source entropy zero on every Xi divisor fibre). A moving metric must not be misrepresented as a fixed invariant positive metric. Reflection cancels cocycles only pairwise/hyperbolically and remains atomically isotropic.

Research card:
docs/drafts/pipeline/3-formalized/riemann-centered-flow-modular-capacity-intertwining.md
Contains complete paper proof and antagonist review.

Verification:
- lake env lean GaloisForLFunctions/RHTower/RiemannCenteredFlowCapacityIntertwining.lean passed.
- lake build GaloisForLFunctions.RHTower.RiemannCenteredFlowCapacityIntertwining produced olean successfully.
- #print axioms on capstone results: only propext, Classical.choice, Quot.sound.
- no sorry/admit/axiom/opaque/unsafe in new module.
- no stale Lean process from this work.
Related prior memory: mem:research/global_atomic_non_erasure_closed_2026_08_03.