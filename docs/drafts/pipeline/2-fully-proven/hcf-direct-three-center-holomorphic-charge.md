# HCF direct three-center holomorphic charge

- **ID:** hcf-direct-three-center-holomorphic-charge
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) `[PAPER-PROVED] [NOVELTY UNVERIFIED]`
- **Source:** HCF corrected prime--Gamma lattice route
- **Statement:** Every finite strict-right Xi packet whose nearest three centers lie in `K` deposits at least `63488/21125` per copy directly in `criticalFeaturePrimeGammaOffLineLatticeBudget K`; consequently `7936/21125 · N` is sufficient for the 75% receiver.

## Goal
Remove avoidable global factor-two loss in HCF receiver by using real holomorphic squares directly after exact critical-line subtraction.  `[CONJECTURE] [NOVELTY UNVERIFIED]`

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `three_quarters_line_of_directThreeCenter_primeGammaOffLineLatticeBudget`, targeted build green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
`[PROVED HERE]`

Write `F_t(q)` for the critical-feature Cauchy kernel evaluated on one multiplicity copy.  The
Weil/source diagonal is `Σ_q F_t(q)^2`.  On the critical line `F_t(q)` is real, so the subtracted
critical-line Hermitian trace is exactly the critical-line part of `Σ_q Re(F_t(q)^2)`.  Therefore
the corrected excess is exactly the off-line holomorphic-square trace, not merely comparable to it.

For a copy in its nearest cell, sum the three centers.  Global sector coercivity contributes
`1/2` of the sharp three-center Hermitian quantum `23232/4225`.  The nearest-center sector improves
`1/2` to `3/5`; its Hermitian mass is at least `64/25`.  Hence the direct holomorphic charge is at
least

`(1/2)(23232/4225) + (1/10)(64/25) = 63488/21125`.

All omitted lattice terms are nonnegative by global sector coercivity.  Summing over a finite
packet and using exact off-line trace equality gives

`(63488/21125) · card S ≤ criticalFeaturePrimeGammaOffLineLatticeBudget K`.

If `N = N₀ + 2 card S` and the budget is at most `(7936/21125)N`, division by the charge yields
`card S ≤ N/8`, hence `3N/4 ≤ N₀`.

### Exact trace proof

Square summability of `F_t` implies summability of `F_t(q)^2` and of its real part.  Since the
critical feature is fixed by Weil sharp, its Weil polarization is `Σ_q F_t(q)^2`; the corpus source
identity identifies this with `criticalFeaturePrimeGammaSourceDiagonal t`.

Split `Re(F_t(q)^2)` into line and off-line terms by the predicate
`Re(q.1)=1/2`.  On the line, `xiSpectralPoint q` is real and the real-centered feature evaluation
has zero imaginary part.  Hence `Re(F_t(q)^2)=|F_t(q)|²`, exactly the summand of
`criticalLineCriticalFeatureEnergyTrace`.  Off the line, global sector coercivity gives
`0 ≤ Re(F_t(q)^2)`, and domination by the summable full real-square trace gives summability of the
off-line restriction.  Termwise line/off-line splitting and `tsum_add` therefore prove

`criticalFeaturePrimeGammaOffLineExcess t = Σ'_q offLineHolomorphicEnergy t q`.

### Finite packet proof

For each `q ∈ S`, strict-rightness excludes the critical line.  At its rounded center `kq`, sharp
three-center Hermitian coercivity gives total norm-square at least `23232/4225`.  Applying global
`1/2` sector coercivity to all three terms and the stronger nearest-cell `3/5` inequality to the
central term gives an additional `1/10` of the central norm-square; the nearest-cell Hermitian
floor is `64/25`.  Linear combination yields `63488/21125`.

The three centers belong to `K`.  Every other off-line holomorphic summand is nonnegative, so the
three-term lower bound extends to the full finite `K`-sum.  Finite Fubini, followed by finite-sum
≤ nonnegative `tsum` and the exact trace identity, yields the claimed packet charge.  The receiver
calculation is exact linear arithmetic from `N=N₀+2 card S` and `B≤(7936/21125)N`.

## Hostile audit
- The conjectured sharp pointwise floor `304/75` is not used; no dependency-closed proof is known.
- This is receiver progress, not a source-ceiling proof.  It changes the exact open HCF constant
  from `1452/4225` to `7936/21125` if the trace equality and finite rearrangements close.
- No omitted term may be discarded until its nonnegativity is transported to the exact off-line
  holomorphic summand.

## Open core
None for this theorem.  Route-level open core remains the source-only asymptotic ceiling at the new
constant `7936/21125`.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** Not falsified.
- **Strongest positive survivor:** Direct holomorphic charge above.
- **New insight:** Critical-line subtraction converts HCF source diagonal into a positive off-line holomorphic trace; receiver need not detour through Hermitian energy and global factor two.
- **Status:** `[PAPER-PROVED]`; external 2026 pair-correlation record does not contain this HCF receiver; exact Lean formalization pending.

## Log
- 2026-08-29 — created in 1-in-progress from corpus sector and three-center theorems.
- 2026-08-29 — complete summability/trace/finite-packet proof survived hostile audit; moved to 2-fully-proven.
