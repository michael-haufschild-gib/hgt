# CLG/TTF arbitrary five-point theta clusters

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For every `0<a<1/2`, there exists `δ>0` such that every injective `t : Fin 5 → ℝ` satisfying `|t i-t j|<δ` for all `i,j` has a positive-definite literal center-mixed theta Gram matrix.
- **Capstone:** `RHTower.exists_thetaCuspCenterMixedGramFive_posDef_cluster` in `ThetaCuspCenterMixedFivePointCluster`.
- **Full RH chain:** Completed theta source → Xi Bezoutian → every finite two-channel Weil packet PSD → RH. This closes the arbitrary-shape local rank-five source chamber; higher ranks, global packet geometry, theta-specific incidence, and cofinal no-escape remain.

## Dependency-closed proof

For increasing node lists `x` and `y` of lengths `p+1` and `q+1`, the mixed divided difference of `f(u-v)` is exactly

`(-1)^q f^(p+q)(u-v)/(p!q!)`

for some `u` and `v` inside their respective closed node hulls. `MixedTranslationDividedDifference` proves this, including order zero, from the corpus Hilbert-irreducibility divided-difference mean-value theorem. First apply the left mean-value theorem to the finite right-stencil function and its explicit derivative sequence. Then apply the right mean-value theorem to the resulting literal derivative. No chosen mean-value point is differentiated.

Prefix divided differences are rows of a square lower-triangular transform. Its diagonal entries are inverses of nonzero node-difference products, so distinct nodes make it invertible. `PrefixDividedDifferenceGram` proves the exact Gram congruence. As all nodes approach zero, the mixed mean-value formula and continuity of the derivatives give entrywise convergence to

`M[p,q] = (-1)^q f^(p+q)(0)/(p!q!)`.

Both mean-value points stay in the shrinking node hulls, so the limit holds for every shape, including hierarchies of arbitrarily unequal gaps. No inverse-Vandermonde norm estimate or lower gap bound is required. The corpus matrix-stability theorem transfers strict positivity of `M` to every sufficiently small ordered cluster. Exact invertible congruence returns the original sampled Gram form. This generic theorem requires only `C^(2N-2)` regularity at rank `N`.

For the literal theta density at rank five, the already proved signed jet matrix is positive definite. Diagonal factorial scaling supplies the exact matrix `M`. The existing C8 source theorem discharges all regularity requirements. Translation invariance turns the node-norm neighborhood into a diameter bound; sorting and permutation congruence remove the ordering hypothesis. Thus one bound at each critical aperture covers all distinct five-point configurations.

## Scope

The radius may depend on aperture. The theorem imposes no ordering, minimum-gap, or spacing-ratio restriction on nodes. It does not assert a uniform lower eigenvalue bound for the unnormalized matrices as nodes collide. It does not prove higher-rank theta jet signs, global packet positivity, C5 orientation, or RH.

## Verification

- All three new production modules pass direct `lake env lean` checks without warnings; only needed oleans were generated.
- The new physical capstone's axiom audit returns only `propext`, `Classical.choice`, and `Quot.sound`.
- Formal lint passes; corpus indexes refreshed; all three modules wired into their area umbrellas.
- A scan of all 26 new public declaration names found no matches outside these modules.
- No full, umbrella, or cascading build; no numerical certificate or added axiom.
