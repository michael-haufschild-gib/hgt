# CLG/TTF arbitrary five-point clusters

- **Stage:** 1-in-progress
- **Target:** For every critical aperture, one neighborhood of coalescence contains only positive-definite actual theta Gram matrices on five distinct ordered nodes, with no spacing-ratio bound.
- **Current source inputs:** Global native D1, actual strict rank-three center mixing, and the actual equispaced five-point cusp are Lean-proved.
- **Full RH chain:** Completed theta source → Xi Bezoutian → every finite two-channel Weil packet PSD → RH. This work removes the equal-spacing restriction in one finite local source chamber; higher ranks, global packet geometry, incidence, and cofinal no-escape remain.

## Corpus mechanism

`HTGeometry/HilbertIrreducibility/DividedDifference.lean` proves the divided-difference mean-value theorem for arbitrary increasing nodes using an explicit derivative sequence. Apply it first to the left divided difference of the right-stencil function, then to the right divided difference of the corresponding literal derivative. The mixed entry becomes `(-1)^q f^(p+q)(u-v)/(p!q!)` for points in the two node hulls. Continuity of the derivatives gives uniform entrywise proximity independent of the smallest gap.

Prefix divided differences form an invertible triangular transform of the finite Gram matrix. The limiting derivative matrix is the already proved strict five-dimensional jet form, rescaled by factorials. Matrix positivity stability and exact congruence return positivity to the original arbitrary-node Gram matrix.

## Obligations

1. Mixed divided-difference mean-value identity, including order zero.
2. Uniform entrywise limit as all nodes approach zero, with no lower gap bound.
3. Exact prefix-transform congruence and invertibility on distinct nodes.
4. Literal theta source application, new-capstone audit, narrow direct Lean checks, umbrella wiring.

No numerical certificate or RH-equivalent positivity premise enters the physical capstone.
