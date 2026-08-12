# Gamma-six amplification leaves exact abelian strip slack

- **ID:** source-horizontal-gamma-six-abelian-strip-slack
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/rh-current-frontier-map.md · Frankenstein Gamma-six seam
- **Statement:** Canonical `(2,3)` abelian source apertures multiplied by the complete two-orientation Gamma-six shell tend to zero on every multiplicity-labelled Xi divisor copy, with forward/reverse geometric bases `6^(2a-2)` and `6^(a-2)`.

## Goal

Test the most literal Frankenstein renewal: use coefficient-faithful Gamma-six shell rank to
replenish the exact two-class abelian source aperture while retaining prime labels, both reflection
orientations, and Xi divisor multiplicity.  Classify the failure sharply enough to constrain the
missing producer rather than merely reject the route.

## Gates

- [x] 0 → 1 in-progress: source-pure quantities, exact fusion, explicit exponent attack
- [x] 1 → 2 fully-proven: elementary exponent inequalities and geometric convergence, no open dependency
- [x] 2 → 3 formalized: Lean module `SourceHorizontalGammaSixAbelianStripSlack`, direct check and axiom audit green
- [ ] 3 → 4 publication-ready: standalone theorem, novelty comparison, and integrated exposition

## Approach

For `a∈[0,1)`, pair the canonical abelian two-class admissions at ordered primes `2` and `3` and
multiply by the complete Gamma-six two-orientation shell trace mass.  Bound each forward admission
by `(p+1)p^((a-2)(m+1))` and each reverse admission by
`2p^(-2m-1-a)`.  Exact `2·3=6` exponent bookkeeping gives geometric majorants with bases
`6^(2a-2)` and `6^(a-2)`.  Both lie in `[0,1)`.  Specialization
`a=|primeDepthBVWoldXiCenteredRate(q)|<1` proves evacuation for every `XiZeroCopy q`.

## No-go closure

- **Exact killing theorem/mechanism:** Gamma-six shell mass cannot overcome canonical two-prime admission loss; even full coefficient-faithful shell multiplication converges to zero in both orientations.
- **Strongest positive survivor:** forward reserve is exactly controlled by base `6^(-2(1-a))`; reverse reserve is stronger, `6^(a-2)`.  Strip slack `1-a` therefore becomes an explicit renewal codimension.
- **New insight:** viable multiplicative source renewal must supply at least two prime-clock exponent units on the bottleneck forward branch, or use a genuinely non-mass-preserving operation.  Marking/flags preserve probability mass, while Big-Witt relocation pays the already-formalized per-index cost.
- **Status:** internal corpus search found no prior theorem pairing canonical `(2,3)` apertures with the full two-orientation Gamma-six shell or extracting this exponent.  External Jacobi sum-rule literature motivates information/work comparison but does not prove this arithmetic source law.  External novelty remains unverified.  Paper proof is dependency-closed and formalized in `formal/GaloisForLFunctions/RHTower/SourceHorizontalGammaSixAbelianStripSlack.lean`.

## Conjecture / failure / pivot log

- 2026-08-12 — conjectured global Xi Jacobi entropy/work sum rule; failed because a global positive spectral measure is RH-shaped, while finite rules retain the Route-U boundary term.
- 2026-08-12 — conjectured flag/marking amplification of fixed abelian class-law aperture; failed because adding markings over a probability law preserves total aperture mass.
- 2026-08-12 — conjectured moment-neutral Big-Witt/Verschiebung relocation; failed because the corpus already proves the sharp per-index cost and high-index relocation causes spectral collapse.
- 2026-08-12 — conjectured Gamma-six shell renewal of the exact `(2,3)` aperture; falsified by sharp strip-slack bounds.  Positive survivor proved and formalized.
