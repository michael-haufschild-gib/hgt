# The m-step window branch: independence over the certified-viable region

- **ID:** m-step-window-branch
- **Stage:** 0-backlog
- **Type:** [CONJECTURE] - target grade **BRIDGE**
- **Source:** far end of the critical-curve program; generalizes the sharp window pass
  (`u0-phib-window-independence`) from the ring `‖b‖ > 2+√2` to the full viability region.

## Claim

[CONJECTURE] For every parameter `b` carrying a viability certificate (`K_b ∩ D̄(0,1) = ∅`,
square-tree/disk-chain data as in `U0DiskEscape`) — including `2 < ‖b‖ ≤ 2+√2` outside the
obstructed pattern lobes — the independence capstone `NoRelation ℂ(z) (φ-branch) (u₀)` holds on
a b-dependent annulus across the unit circle, via an **m-step window branch**

  `phiB_m b z = exp(2^{−(m+1)}·(bottcherLog after m steps + Σ_{j<m} 2^{j} · log-corrections))`,

where `m` is the certificate's chain depth.  The theorem family becomes "independence holds
wherever the geometry permits it" — the natural endpoint of *constraint, not flow* for this
object: the branch exists exactly where the constraint (disk-avoidance of `K_b`) allows.

## Why plausible

Everything downstream of the branch is ALREADY generic: the carrier-generic descent
(`kappaP`/`descend_algebraicP`), the carrier-generic capstone assembly functor, and the
φ-generic natural-boundary engine consume any analytic branch with a dyadic pullback onto the
far Böttcher carrier.  Only the branch construction + functional equation + analyticity layer
is new.  The single-step normalization trick (rotate through `log b`, keep `1 + z²/b` in the
right half-plane) must generalize to per-step corrections `log(1 + b/wⱼ²)` along the chain,
each with a right-half-plane certificate on its chain disk — the SAME disk-arithmetic data the
viability certificate already carries (ratio bounds along the chain).

## Open core

1. Branch normalization across `m` steps: the `2^{−j}` weights must telescope in
   `phiB_m² = phiB_{m−1} ∘ f`, with a branch-free δ-identity at the exp level per step.
2. The annulus radius from the chain geometry (first-disk clearance replaces `rB b`).
3. The nondegeneracy witness domain for the engine at chain-carried parameters.

## Log
- 2026-07-02 — carded from the critical-curve program ([ρ.10]); prerequisites banked:
  carrier-generic functor + descent (sharp pass), viability certificates (`U0DiskEscape`),
  slice instances (`U0DichotomySlice`).
