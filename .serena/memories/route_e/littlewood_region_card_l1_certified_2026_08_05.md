# Littlewood region card created; L1 numerically certified (2026-08-05)

New card: `docs/drafts/pipeline/1-in-progress/littlewood-zero-free-region.md` — the production
lane for the single object gating the MR corridor (κ-criterion on
`mr-splice-wide-range-mean-square.md`).

Asset audit: `PNTPlus/ZetaBounds` has the full Landau pipeline with input growth
`ZetaUpperBnd' ≪ log|t|` (upgrading the input upgrades the region; PNTPlus is READ-ONLY —
build in corpus modules importing it). mathlib has NO van der Corput (sum or integral), no
Kuzmin–Landau, no Weyl differencing. Corpus `ZeroLinePower`/`ZeroLineSum` is the k=1 base.

**L1 certified numerically**: k-th-derivative-test chain (constants modeled `A_k = c·2^k`,
minimized over k per dyadic block vs trivial log 2) gives
`∑_{n≤t} n^{-1-it} ≤ ratio·(log t/log log t)` with ratio = 1.93, 1.58, 1.38, 1.24 at
log t = 230, 2303, 23026, 230259; k ≤ 11 throughout; robust under 10× constant inflation.
The classical k-schedule `k ≈ log t/log N + 1`, `k_max ≈ log₂ log t` is what the optimizer
selects.

Staged L2 (paper, honest constants: Kuzmin–Landau + Weyl step + k-fold recursion + packaged
test; re-run L1 with honest A_k) → L3 (Lean Kuzmin–Landau) → L4 (Weyl step + iteration) →
L5 (test + dyadic assembly + ζ(1+it) and rectangle version) → L6 (rerun Landau pipeline →
region; then MR route-B unit 5 + assembly).

Falsifiers: derivative-ratio 2^k must be explicit in the test constants; the rectangle
(σ < 1) version is load-bearing for the Landau pipeline; if L2 constants exceed the 10×
margin, re-run L1 first.
