# HB pre-divisor unbounded-metric finite-graph-energy no-go

- **ID:** HB-UNBOUNDED-GRAPH-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` (read-only) · HB operator/Krein survivor
- **Statement:** Exact HB pre-divisor kernel cannot be represented as `inner (Phi x) (JPhi y)` when both `norm (Phi x)^2` and `norm (JPhi x)^2` are integrable at hard edge.

## Goal
Kill finite graph-energy unbounded/rigged metric branch in chain `HB opposite sign → pre-divisor cancellation kernel → Ward extinction → RH`; no boundedness, closedness, self-adjointness, involutivity, or operator type is assumed.

## Gates
- [x] 0 → 1 in-progress: corpus hard-edge law and exact attack identified
- [x] 1 → 2 fully-proven: complete paper proof, no open dependency
- [x] 2 → 3 formalized: Lean theorem `d4HBPreDivisorFiniteGraphEnergyMetricRouteKilled`; targeted build and axioms audit pass
- [ ] 3 → 4 publication-ready

## Proof
Write the two pairing legs as arbitrary `Phi,Psi`; no operator structure is needed. On the diagonal, exact kernel gives `S(x)=inner (Phi x) (Psi x)`. Since `S≥0`,
`S(x) ≤ norm(Phi x) norm(Psi x) ≤ norm(Phi x)^2+norm(Psi x)^2`.
If both square energies were integrable, domination would make `S` integrable, contradicting corpus theorem `¬ IntegrableOn S`, proved from `x⁻² ≤ S(x)` on `(0,1/2)`.

## No-go closure
- **Exact killing theorem/mechanism:** diagonal Hilbert bound plus hard-edge nonintegrability; arbitrary finite-energy two-leg pairing is impossible.
- **Strongest positive survivor:** exact energy allocation: finite `Phi` energy forces infinite `Psi` energy (and conversely). For `Psi=J Phi`, finite feature energy forces infinite metric-image/graph energy.
- **New insight:** unboundedness alone cannot evade hard-edge divergence; escape requires infinite graph energy or a non-pointwise/distributional pairing.
- **Status:** `[PROVED HERE] [LEAN-PROVED]`; module `ThetaCuspHawkingPreDivisorFiniteGraphEnergyMetricNoGo`; targeted build pass; axioms only `propext`, `Classical.choice`, `Quot.sound`. Corpus search and August-2026 arXiv audit found no prior statement for this HB kernel; underlying Hilbert inequality is classical.

## Log
- 2026-09-01 — frozen after corpus search; targets exact HB operator/Krein survivor.
