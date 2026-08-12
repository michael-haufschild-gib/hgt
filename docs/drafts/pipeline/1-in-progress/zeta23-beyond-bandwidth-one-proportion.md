# Beyond Zeta-23 bandwidth-one critical-line proportion

- **ID:** `zeta23-beyond-bandwidth-one-proportion`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `claude-zeta23-rank-trace-audit.md`; external Zeta-23 paper and Lean artifact
- **Statement:** Prove unconditionally that the lower density of Riemann-zeta zeros on the critical line is strictly greater than the optimized Zeta-23 constant `≈ 0.6725`.

## Goal

Determine whether higher-bandwidth finite Weil compression, additional prime-side moments, or a
non-scalar source-labelled receiver can beat the optimized Zeta-23 constant without importing RH,
a zero-density assumption, or an unproved long-mollifier asymptotic.

## Gates

- [x] 0 → 1 in-progress: exact target and external comparator identified; internal and external
  frontier audit active.
- [ ] 1 → 2 fully-proven: complete unconditional paper proof, `[PAPER-PROVED]`, no open dependency.
- [ ] 2 → 3 formalized: exact theorem in Lean; targeted build, lint, and axiom gates pass.
- [ ] 3 → 4 publication-ready: standalone paper, independent proof and priority audit.

## Approach

Normalize Zeta-23's optimized variational problem and sharp bandwidth-one ceiling. Audit every
local source-labelled, Weil-form, moment, amplification, and detector theorem that could change
one term of that optimization. Test higher bandwidth and shared-reservoir compression first; reject
any route whose required prime correlation is presently unproved or whose rank cost cancels its
gain.

## Active labels

- `[LITERATURE]` Zeta-23 proves `2/3`, with optimized constant approximately `0.6725`.
- `[LOCAL-RESEARCH]` Scalar bandwidth-one amplification cannot remove per-positive-index rank cost;
  fixed-threshold packets have linear Frobenius cost.
- `[OPEN CORE]` Exhibit and prove a source-clean finite compression whose asymptotic rank--trace
  functional has optimum strictly above `0.6725`, including every needed prime-side correlation.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** pending.
- **Strongest positive survivor:** pending.
- **New insight:** pending.
- **Status:** internal/external audit active; no paper proof; no Lean theorem claimed.

## Log

- 2026-08-12 — created in Stage 1 for exact Zeta-23 constant-improvement target.
