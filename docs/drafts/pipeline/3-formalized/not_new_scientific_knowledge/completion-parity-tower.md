# Completion parity: the fixed-point bit and its 2-adic tower

- **ID:** completion-parity-tower
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For central normal form `(s−1/2)^m·G` (G a symmetric nonvanishing strip unit): a bare completion factor always exists; a continuous one exists iff `m` is even; the rung-k root form completes iff `2^{k+1} ∣ m`; the whole ladder completes iff `m = 0`. FE-completability is decided by the reflection's fixed-point μ₂-charge — the seam-sign bit of the equivariant program — and the completability bits of the root ladder are the 2-adic digits of the central order.
- **Lean:** `CompletionParity.lean` (`completion_raw_exists`, `completion_continuousOn_iff_even_center`), `CompletionParityTower.lean` (`rung_completion_iff_next_dyadic`, `completion_tower_iff_center_order_zero`). Axiom-clean.
- **Dual gate:** PASS. NOVEL — completability-of-a-given-carrier as a question is not posed in the FE literature (FE is always given); the regularity hierarchy (raw/continuous) carrying exactly one bit is new. SIGNIFICANT — welds the Goldilocks lane to the seam-sign/crease-ledger lane through one invariant; the rung hierarchy becomes readable at a single point.

## Log
- 2026-07-09 — formalized; lanes welded on `goldilocks-divisor-rigidity.md`.
