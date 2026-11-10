# Assemblies of proved pieces

- **ID:** proved-pieces-assemblies
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-1011/obstacles-summary.md`, §2.1, “Assemblies of proved pieces”.
- **Goal:** Resolve every listed task, with exact paper arguments and kernel-checked Lean declarations; no additional mathematical premises.

## Scope and proof obligations

| Tasks | Required result | Status |
|---|---|---|
| A107 | Level-one positivity gives AAL, B56, and RH or Θ=1 | Inspecting large-prime dichotomy and abscissa laws |
| A110 | B13 iff comb-defect negative index is zero or infinite | Open |
| A106 | AAL from length-dependent floors at `(k+1)π/67`, including prime logs | Open |
| A103 | Cancellation, positivity, companions, long moments, seven-way quasi-RH ladder | Open |
| A108 | Conductor first rung forces primes of both character signs | Open |
| A109 | Normalized prime-error trichotomy | Open |
| A113 | Half-plane map: bounded shapes, positivity, return-free windows | Open |
| A114 | Step-packet limit matrices with both pole moments and RH equivalence | Open |
| A104 | Exceptional-height measure, second and growing moments | Open |
| A105 | Density-matched rung-positive model with arbitrarily high deep zeros | Open |
| A102 | Sharp additive constant in height aperture | Open |
| A80, A94 | Finite-scale converse and index equality | Open |
| A82 | Li ladder as comb forms of tails | Open |
| A79, A81, A93 | Aperture–height constants and order of windowHeight | Open |
| A78, A89 | Cluster window theorem and prescribed sub-logarithmic radius | Open |
| A86, A47 | Near-diagonal cofactors, growing filters, one-quartet constants | Open |
| A111 | Critical-zero proportion from twisted moments and Levinson gate | Open |
| A116 | Ideal degree points, Hecke characters, non-abelian character index | Open; preserve existing independent ideal-square work |
| A119 | Linear depth-sum bound with explicit moment constant | Open |

## Integrity

Each completion requires exact stated scope, a direct `lake --old env lean` check, transitive
`#print axioms`, and umbrella wiring. Existing implications count only after statement and
dependency inspection. Mathematical counterexamples require a positive-survivor audit.
