# Reverse-Bessel Gamma cost has a square-root cutoff and half-log reserve

- **ID:** ccm-reverse-bessel-gamma-half-log-reserve
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** `rh-current-frontier-map.md` · CCM moving-degree source compactness core
- **Statement:** If
  `a(n,j) = (b(n,j+1)/b(n,0)) j!` for the squared-Xi reverse-Bessel weights, then
  `sum_{j<n} a(n,j) <= H_{floor(sqrt n)} + 2`, hence the factorial-weighted Gamma-jet cost uses at
  most one half of the available logarithmic scale, up to an absolute constant.

## Goal

Replace fixed-frequency reverse-Bessel asymptotics, already known to be insufficient, by a uniform
moving-degree estimate at the parabolic source scale.  This is source-native: it uses the exact
coefficient recurrence forced by squared-Xi radial differentiation.  Intended downstream use is a
quantitative lower reserve for moving-degree Gamma/source competition, the current pulse-capital
compactness obstruction.

## Gates

- [x] 0 → 1 in-progress: exact finite statistic, source-pure recurrence, corpus/literature audit,
  dependency-closed paper proof
- [ ] 1 → 2 fully-proven: independent proof audit and downstream source lemma
- [ ] 2 → 3 formalized: Lean theorem `reverseBesselGammaCost_le_halfLogReserve`, targeted build and
  axiom audit
- [ ] 3 → 4 publication-ready: integrate into source-modular superselection manuscript

## Corpus and literature boundary

Corpus search was performed before conjecturing.  Existing Lean proves the exact adjacent
reverse-Bessel recurrence, coefficient domination by `1/j!`, fixed-index convergence to `1/j!`,
and `H_m <= 1 + log m`.  It contains no moving-degree bound for the factorial-weighted sum above,
no square-root coefficient cutoff, and no half-log reserve theorem.  Targeted literature search
found large-degree asymptotics for generalized/reverse Bessel polynomials and their zeros, but no
statement for this factorial-weighted coefficient statistic.  Novelty claim remains deliberately
limited to corpus absence and no match in that targeted search.

## Proof

Write `A_j = (b(n,j)/b(n,0))(j-1)!` for `1 <= j <= n`.  The exact coefficient recurrence gives

`A_{j+1}/A_j = (j/(j+1)) (2(n-j)/(2n-j))`.

All terms are nonnegative.  Since the first factor is at most one,

`A_j - A_{j+1} >= (j/(2n-j)) A_j >= (j/(2n)) A_j`.

Also the existing factorial domination gives `A_j <= 1/j`.  Let
`r = floor(sqrt n)`.  For the tail `j >= r+1`, telescope the preceding decrement inequality:

`sum_{j=r+1}^n A_j <= (2n/(r+1)) A_{r+1} <= 2n/(r+1)^2 < 2`,

because `n < (r+1)^2`.  The head is termwise bounded by the harmonic sum:

`sum_{j=1}^r A_j <= H_r`.

Thus the full cost is at most `H_r + 2`.  Combining `H_r <= 1 + log r`,
`r^2 <= n`, and monotonicity of `log` yields the explicit half-log form
`sum A_j <= 3 + (1/2) log n` for `n >= 1` (with `n = 0` trivial).  No limit interchange or
numerical computation is used.

## Scientific consequence

The reverse-Bessel Gamma jets do not spend the full `log w` available at a parabolic source point:
their effective factorial-weighted support stops at order `sqrt n`, leaving an asymptotic
half-logarithmic reserve.  Fixed-frequency blindness therefore does not extend uniformly to the
moving-degree Gamma packet.  The remaining hard step is to transport this reserve through the
completed source decomposition into a cofinal pulse-capital lower bound.

## Log

- 2026-08-16 — Corpus-first audit isolated the missing moving-degree statistic; dependency-closed
  telescoping proof obtained; Lean formalization started.
