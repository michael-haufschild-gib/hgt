# Continuum trace, affine commutator, and finite nodal-edge control

- **ID:** continuum-trace-affine-edge-control
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The additive Dirichlet form in logarithmic coordinates controls
  successor shear, dilated trace cells, affine noncommutativity, and finite weighted
  multiplicative nodal pairings, with exact interval and cell remainder identities.

## Exact theorem

For arbitrary continuous v, set g(x)=∫₀ˣv, D(a,b)=∫ₐᵇexp(−x)v(x)²,
L=exp b−exp a, and Δ=g(b)−g(a). Then

    ∫ₐᵇ exp(−x)(Lv(x)−Δexp x)² = L²D(a,b)−LΔ².

Thus Δ²≤LD(a,b) when a≤b. For σ_b(x)=log(exp x+b), b,s≥0,

    |g(σ_b(x)+s)−g(σ_b(x+s))|²
      ≤ b(exp s−1)D(σ_b(x+s),σ_b(x)+s).

For y_n=log(exp a+kn), k≥0,

    Σ_{n<N}|g(y_{n+1})−g(y_n)|² ≤ kD(a,y_N).

For each multiplicative edge x→x+log(n+1), squared jumps and four times the
opposite-sign nodal pairing are at most n exp x D(x,x+log(n+1)). Nodal estimates
allow arbitrary added constants. Finite nonnegative weighted edge families inherit
these estimates.

## Proof and formal evidence

Paper proof and precise boundaries:
`docs/reports/BiScaleUncertainty/ContinuumCoprimeShear-FACTS.md`.
Namespace: `GaloisForLFunctions.BiScaleUncertainty.ContinuumShear`.

- `ContinuumShearDirichlet.lean`: 29 theorems; direct final Lean audit passed.
- `ContinuumMultiplicativeEdgeControl.lean`: 5 theorems; direct final Lean audit passed.
- All 34 axiom reports contain only `propext`, `Classical.choice`, `Quot.sound`.
- Both leaves are imported by the area umbrella; indexes refreshed.
- Repository lint still reports three unrelated concurrent missing imports; see ledger.

## Significance and boundaries

One contribution to the 100-contribution goal: a concrete continuum bridge from
Pillar VII and its finite nodal graph mechanism, with the correct weighted form
and no unproved analytic admission premise. Classical interval Dirichlet principles
are reused, not claimed as new scientific discoveries. General H1 completion,
coprime-supported trace interpolation, infinite SourceGraph admission, and a full
unitary affine uncertainty theory remain open. The overarching research card stays
in progress.
