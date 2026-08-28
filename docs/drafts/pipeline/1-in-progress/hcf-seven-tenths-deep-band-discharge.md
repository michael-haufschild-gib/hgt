# HCF seven-tenths deep-band discharge

- **ID:** HCF-DEEP-7T
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** Internal cross-route weld: HCF canonical height window + Route-T Ingham density
- **Statement:** The HCF contribution from zeros with `Re s ≥ 7/10` is `o(N(T))`; after this discharge, only `1/2 < Re s < 7/10` can affect the normalized source budget.

## Goal

Remove the deep off-line band from the quantitative HCF source problem without using computations or
any zero-dependent scalarization.  This is source-pure on the counting side: Route T already gives a
literal analytic-multiplicity zeta-zero count, while the HCF canonical normalizer is the actual
Riemann zero count.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure counting theorem, precise remaining charge lemma
- [ ] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3 formalized: Lean theorem, targeted `lake build` green, axiom audit clean
- [ ] 3 → 4 publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Write

`Zdeep(X) = zetaLittlewoodZeroCountAbove inghamFixedGabrielSigma 4 X (7/10)`.

Apply the existing unconditional Route-T theorem at `X + 2`.  It supplies constants `K ≥ 0` and
`α < 7/10 < 1` with `Zdeep(X) ≤ K (X + 2)^α` eventually.  Since
`(X + 2)^α ≤ X + 2 ≤ 2X + 3`, while the canonical HCF window has cardinality `2X + 3`, the existing
Riemann--von Mangoldt formalization proves

`(2X + 3) / N(X) → 0`.

Hence `0 ≤ Zdeep(X) / N(X) ≤ K (2X + 3) / N(X) → 0`.  This gives the unconditional counting weld.

To discharge HCF energy rather than only zero count, prove one new source-independent estimate:

`sup_{|Im z| < 1/2} ∑_{k∈ℤ} |2 / (1 + (z-k)^2)|^2 ≤ C`

for one absolute constant `C`.  Then every finite HCF window contribution from the deep band is at
most `C Zdeep(X)`, hence `o(N(X))`; no height boundary is omitted.  A nearest-integer split reduces the estimate to a
single central term and a convergent quartic tail; sharpness is irrelevant.

The surviving quantitative target is therefore the shallow band `1/2 < Re s < 7/10`.  Its maximal
horizontal displacement from the critical line is `< 1/5`, exactly matching the corpus's fixed
positive-real-shift and submicroscopic separator machinery.

There is a source-only reformulation of that survivor.  Compare the fixed transverse-width
`delta = 1/5` source contour with the existing Plemelj line limit.  Fixed contour minus Plemelj
line limit is the compact annulus covariance carrying precisely the shallow divisor energy; total
diagonal minus fixed contour is the deep band controlled above.  Thus the global corrected
covariance decomposes as

`B_corrected(K_X) = B_annulus,1/5(K_X) + o(N(X))`,

where `B_annulus,1/5` is a difference of two zero-independent pole--Gamma--von-Mangoldt source
evaluations.  This is the proposed replacement statistic: fixed-width annulus, not a narrower
divisor-selected projector and not another receiver window.

## Exact open core

1. Formalize `Zdeep(X) / N(X) → 0` from existing theorems.
2. Prove a uniform full-lattice HCF charge bound, then transfer it to the finite canonical window.
3. Prove multiplicity-exact reflection transport from the right deep zeta packet to Xi copies.
4. Define the fixed-`1/5` contour-minus-Plemelj-line annulus covariance and prove
   `B_corrected - B_annulus,1/5 = o(N)`.
5. Bound the compact annulus covariance by `7936/21125 * N + o(N)` (or the stronger requested
   `21/100` or `4/25` ceiling) through its literal pole--Gamma--von-Mangoldt evaluation.

## Log

- 2026-08-29 — created in 1-in-progress; counting argument dependency-closed on paper; uniform HCF charge bound remains open.
