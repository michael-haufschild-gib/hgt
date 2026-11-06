# W3: exact extremal blind function

- **ID:** W3-EXACT
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-0611/obstacles-summary.md`, W3.
- **Target:** Construct a nonzero strip-holomorphic `Φ = Ξ g`, with `g` zero-free on `ℝ`, whose spectral square has zero cosine moments at every `log n`, `n ≥ 2`; prove every decay and divisibility condition required by `xiDivisibleBlindTest_stripTest`.

## Mathematical boundary

The existing receiver gives rigidity of every Weil-positive system and `RH ↔ PBAP` from this object. It does **not** prove PBAP. Existence of the extremal function and positivity of the blind program are distinct obligations.

Known constraints: logarithmic Carlson growth after removing the zeta divisor; double-exponential source-tail bounds from the density of simple critical zeros. Neither supplies the extremal function.

## Conjectures

1. Determine whether the strip-decay formulation itself admits a nonzero positive integer-blind spectral square. Resolve its exact analytic-strip obstruction before imposing the Xi divisor.
2. Construct a positive integer-blind square with the full Xi divisor and no extra real zeros, or identify the additional obstruction and formalize its strongest positive survivor.

## Completion gates

- [ ] Explicit construction with unconditional analytic bounds and all integer moments.
- [ ] Full Xi divisibility and real zero-faithfulness.
- [ ] Exact receiver hypotheses discharged in Lean.
- [ ] New modules wired into owning umbrella; individual foreground Lean audits and transitive axiom checks.

No existence claim or RH claim established.
