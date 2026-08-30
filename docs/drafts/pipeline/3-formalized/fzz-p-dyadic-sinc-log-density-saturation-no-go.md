# FZZ-P dyadic-sinc logarithmic-density saturation no-go

- **ID:** FZZ-P-DYADIC-LOG-DENSITY
- **Stage:** 3-formalized
- **Type:** NO-GO THEOREM
- **Source:** `rh-current-frontier-map.md` FZZ-P live cumulative weighted uniqueness-density core
- **Statement:** One fixed completed FZZ/Schwarzschild response has contact depth at least `2^j` on every odd-multiple stratum `2^j(2n+1)`, whose disjoint weight below radius `2^K` is exactly `K·2^(K-1)`, while retaining every completed symmetry/anchor/positive-real-axis constraint and order-one `exp(C r log r)` growth, yet acquiring an interior off-critical zero.

## Goal
Kill the last local cumulative-density repair below the sharp order-one Jensen ceiling. Full attempted RH chain is:

`literal FZZ parity-delay source → integer response samples and source jets → unique completed complex-order response → physical flux/stationarity → Deninger reflect-gauge charge 1-2 Re(ρ)=0 on every source zero → FZZ completeness → RH`.

The theorem kills the uniqueness arrow. Its dyadic contact mass is logarithmically saturated: every dyadic scale contributes one linear block, so disjoint cumulative jet weight through `R=2^K` is exactly `(R/2) log₂ R`, while the FE-paired product retains an `exp(C r log r)` envelope. Therefore membership in the critical `Θ(R log R)` density class, without a sharper constant normalized to analytic type, cannot select the canonical continuation. A surviving local criterion must impose such a sharp type-density inequality or become supercritical; alternatives must use off-lattice/nonlocal data or a singular/non-entire source law.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, targeted `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
Define the dyadic sinc cascade

`D(z) = ∏_{j≥0} sinc(z / 2^j)^(2^j)`.

Quadratic small-scale sinc control gives locally uniform convergence. The simultaneous bounds

`‖sinc w‖ ≤ exp(C‖w‖)` and `‖sinc w‖ ≤ exp(C‖w‖²)`

give

`log ‖D(z)‖ ≤ C Σ_j min(‖z‖, ‖z‖²/2^j) = O((1+‖z‖) log(2+‖z‖))`.

On the disjoint odd-multiple stratum `2^j(2n+1)`, the `j`-th factor contributes analytic order at least `2^j`. Below `2^K`, that stratum has `2^(K-j-1)` nodes; injectivity follows from uniqueness of the 2-adic valuation of an odd multiple. Hence total certified contact weight is

`Σ_{j<K} 2^(K-j-1)·2^j = K·2^(K-1)`.

Centering by `z ↦ z+3/2` makes the cascade FE-even; sinc reality and multiplication by the sharp conjugate give Schwarz reality. A real-coefficient centered interpolation polynomial inside the anchored positive-square Gamma-null gauge forces one prescribed off-critical zero without losing samples, anchors, positivity, or growth.

Hostile attacks:

1. **Convergence failure:** rule out by a locally uniform `O(R²/2^j)` tail.
2. **Growth exceeds order one:** split scales at `2^j≈‖z‖`; head costs `O(‖z‖ log(2+‖z‖))`, tail `O(‖z‖)`.
3. **Accidental zero/infinite product collapse:** absolute near-one convergence makes the tail nonzero away from factor zeros.
4. **Multiplicity insufficient:** use disjoint odd-multiple strata, prove their node map injective, certify analytic order `≥2^j`, and sum one exact linear block per scale.
5. **Constraint leakage:** audit FE symmetry, Schwarz reality, natural samples, three anchors, positive real phase, and target off-line zero separately.

## No-go closure
- **Exact killing theorem/mechanism:** `[FALSIFIED][ROUTE KILL][PROVED HERE][LEAN-PROVED]`. `RHTower.completed_response_dyadicLogDensity_route_noGo` constructs one noncanonical completed response with all prior real-axis constraints, an interior off-critical zero, and exact certified dyadic budget `K·2^(K-1)` below radius `2^K`.
- **Strongest positive survivor:** Critical-density membership alone is dead. A viable local uniqueness theorem must quantify the leading density constant against the response's analytic type (or prove supercritical contact); otherwise FZZ-P needs off-lattice/nonlocal source information or a singular/non-entire source law.
- **New insight:** FE pairing cancels the linear Weierstrass exponent scale-by-scale, allowing a dyadic tower of increasing local multiplicities to attain critical `Θ(R log R)` contact density while preserving physical response growth. The exact disjoint-stratum law isolates the missing datum: density constant relative to type, not density order.
- **Paper-proof status:** Dependency-closed. Convergence follows from summable quadratic tails; growth from the exact dyadic split `Σ_j min(r,r²/2^j)=O((1+r)log(2+r))`; zeros and analytic orders come from factor divisibility; the window budget is an exact finite sum; completed constraints follow from the existing positive-square gauge package.
- **Lean status:** `DyadicSincLogDensityCanonicalProduct.lean` proves convergence, exact scale regrouping, order-one envelope, node analytic order, and exact dyadic budget. `ThetaCuspHawkingFZZSchwarzschildDyadicLogDensityNoGo.lean` proves completed countermodel package, disjoint-node injectivity/bound, exact window weight, off-critical zero, and noncanonicity. Targeted builds and axiom audit pass with only `propext`, `Classical.choice`, and `Quot.sound`.
- **Novelty status:** Corpus audit found only the prior sparse `O(R^(2/3))` countermodel. Bounded primary-source audit found adjacent classical canonical-product and critical-density uniqueness theory but no exact dyadic cascade obstruction for the FZZ/Schwarzschild completion. Priority claim remains bounded rather than absolute.

## Log
- 2026-08-30 — created directly in 1-in-progress after corpus-grounded conjecture-distance and route-chain audit.
- 2026-08-30 — paper proof closed; formalized dyadic canonical-product infrastructure and completed FZZ-P countermodel; moved to stage 3.
