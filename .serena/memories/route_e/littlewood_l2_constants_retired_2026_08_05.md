# Littlewood L2 opened: constant falsifier retired (2026-08-05)

Card: `docs/drafts/pipeline/1-in-progress/littlewood-zero-free-region.md`.

Stress test of the L1 chain under A_k ∈ {10·2^k, 4^k, 8^k, 20^k, 2^{k²/4}}: the
ζ(1+it) ≤ ratio·(log t/loglog t) shape survives ALL of them (ratio ∈ [1.24, 1.93], decreasing
in t, at log t up to 2.3·10⁵). Mechanism: per-block saving exponent −logt/(k·2^k) vs constant
cost k·log c — the k-schedule absorbs any fixed-base exponential. **Consequence: Lean stages
L3–L5 may use the crudest convenient constants; nothing in the Weyl chain needs sharpness.**

L2 remaining = the equation-level paper document (chain KL → D2 → W → Dk → Z → R, per the card
section), then a second numeric gate on the region-transfer bookkeeping (Titchmarsh 1-line →
region, mirroring the PNTPlus Landau pipeline dependency graph) before L6.

Route status stack: MR corridor fully reduced to this card (κ-criterion); route-B units 1–2
built and axiom-clean; Gallagher dyadic tail built; everything else corpus-owned.
