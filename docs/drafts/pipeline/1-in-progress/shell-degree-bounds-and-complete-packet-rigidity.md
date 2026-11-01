# Shell degree and complete packet rigidity

- **ID:** shell-degree-bounds-and-complete-packet-rigidity
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-0111/obstacles-summary.md`, A8.
- **Target:** Bound the literal shell degree and compare successor–dilation
  rigidity with complete Weil packet energy.

## Shell bound

For a nonnegative `C²` profile supported in `[0,1]` with positive square mass,
`0<c≤N`, and `1≤n≤N`, the proposed bound is

`0 ≤ n·d_n ≤ 2(log 4+4)e^(5/2)c + 2e^(3/2)c(n/N)(log n+1)`.

Expand the non-ratio entry as its finite upward and downward prime-lag sums.
Each autocorrelation is at most the atom mass times its window indicator.
The weighted row `Σ_m √(n/m) NR_nm` equals `n·d_n`; the two directed row
bounds give the displayed constants. This retains the position dependence
needed to distinguish a fixed prefix from the terminal horizon.

## Remaining obligations

- Formalize the pointwise degree bound and its packet-weighted consequence.
- Combine the exact complete packet identity with CSAR rigidity, retaining
  shell, pole, and archimedean terms at fixed and growing overlap.
- Direct leaf checks and transitive axiom audits.
