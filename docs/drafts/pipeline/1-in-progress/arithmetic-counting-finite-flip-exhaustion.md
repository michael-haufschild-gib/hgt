# Finite prime-parity counts and the exhaustion obstruction

- **ID:** ACP-FINITE-FLIP-EXHAUSTION
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Parent:** arithmetic-counting-positivity.md
- **Source:** obstacles-summary.md, parity and exhaustion questions

## Target

For every finite set `F` of primes, determine the harmonic density of
`omega_F(n)=prod_{p in F}(-1)^v_p(n)` by an exact incidence count, including
a horizon-independent error bound. Expected density:

`c_F=prod_{p in F}(p-1)/(p+1)>0`.

Use this count to identify what survives finite-prime truncation and what
fails under exhaustion to the Liouville gauge. Fixed finite sets and a
growing set of primes have different quantifiers; no horizon-uniform bound
may be inferred from individual limits.

## Mechanism to verify

For `p` prime outside `F`, multiplication by `p` preserves `omega_F` and
reverses `omega_(F union {p})`. Splitting off the multiples of `p` should give

`S_(F union {p})(N)+S_(F union {p})(N/p)/p
 =S_F(N)-S_F(N/p)/p`.

Subtract the expected harmonic mean. The new error obeys a contraction under
`N -> floor(N/p)`, forced by the old bounded error and the bounded harmonic
shell `H_N-H_floor(N/p)`. Finite-set induction and strong horizon induction
should prove the bound without an infinite product or a mean-value theorem.

## Novelty and ownership

Corpus searches for finite prime flips and harmonic densities returned the
single-prime pairing and the existing finite-prime Mertens matching law.
Those are distinct: the Mertens sum weights by `Lambda`, whereas this count
weights every positive integer by `1/n`. The arbitrary finite-prime harmonic
law was not found in these searches. Exhaustion and Mobius-support searches
remain to be inspected before fixing the final statement.

The maximal-gap theorem for a single prime at least 11 is owned by the
valuation-box branch. This card does not target a weaker replacement.

## Gates

- [x] Initial corpus search; exact candidate and arithmetic mechanism.
- [ ] Complete novelty and dependency audit.
- [ ] Closed paper proof, including the strongest positive exhaustion law.
- [ ] Lean proof and transitive axiom audit.
- [ ] Canonical source checks, umbrella, foundational README, scratch cleanup.

## Status

Candidate only. The harmonic spectral-coordinate bridge is being finished
first; no theorem on this card is yet claimed as proved.
