# F2: complete-family positivity at a small critical multiple

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** Some `K > 0` gives eventual positive definiteness of
  `completeWeilMatrix tiltedUnitSpline c N` on the whole horizon space,
  uniformly for `1 ≤ c ≤ 2 K (log N)^(1/8)`.
- **Scope:** F2/A30 in `review-0311/obstacles-summary.md`; no RH claim.

## Mathematical bridge

Write `L = log N`, `M = N / linearDefectCutoff c`. The weighted far reserve
retains `L c⁻⁷ Σ_(n>M)(N/n)⁷x_n²`, at a prefix cost
`O(L/(1+log L)^B) Σ_(n≤M)x_n²`. The log-free residual theorem supplies
low-packet coercivity through `Q = ⌊L^(13/32)⌋` and a small dual weighted
collar budget. The full residual budget is only `≤ L^(1/4)`.

Split at `Q`, `R₀ = ⌊exp √L⌋`, and `R₁ = ⌊exp(L/(1+log L)^5)⌋`.
Needed: simultaneous mid-band/far cross payment retaining the weighted
collar reserve, then low-packet Schur payment with separate prefix and
collar norms. A scalar full-residual bound cannot pay the collar at the
critical exponent.

## Proof status

The earlier paper card uses `Q = ⌊L^(5/16)⌋`; current residual theorem uses
`13/32`. Its final assembly is not yet a Lean theorem. Audit actual source
statements and their dependencies before treating the paper as complete.

- [ ] Weighted complement and all cross terms paid together.
- [ ] Unconditional full-space capstone.
- [ ] Direct Lean checks, standard-only transitive axiom audit, umbrella import.
