# Route E source-faithful finite-centering no-go

- **ID:** E-SFC-1
- **Stage:** 3-formalized
- **Type:** THEOREM / ROUTE-BRANCH NO-GO
- **Source:** `rh-current-frontier-map.md` Route E; `Sieve/RouteERamareIncidenceConditionalNegative.lean`
- **Statement:** On any finite positive-integer ambient support containing the source, exact interval centering has one counterterm: negate every literal Möbius source coefficient and vanish off source. Hence source-faithful finite centering of a nonempty Ramaré packet is impossible. Every nonempty packet and actual Ramaré bilinear form has strictly positive interval `L²` energy.

## Goal

Kill finite source-faithful spectral centering as producer for Route E. Corpus identity
`offDiagonal = |active scalar mode|² - prime-load energy` makes exact centering sufficient for
nonpositivity; theorem would prove centering possible only by source erasure. Survivors: quantitative
scalar-mode control, infinite compensation, or source-overlapping non-erasing structure.

## Gates

- [x] 0 → 1: exact corpus source, support-level statement, coefficient-recovery attack
- [x] 1 → 2: dependency-closed paper proof; `[PROVED HERE]`
- [x] 2 → 3: Lean theorem, targeted build, axioms pass, umbrella import
- [ ] 3 → 4: standalone paper and final literature audit

## Approach

For positive integers, injectivity of `log` gives distinct exponents `2πi log n`. Interval vanishing
extends to the entire finite exponential polynomial; exponential uniqueness kills every ambient
coefficient. Thus `bₙ=-μ(n)` on literal source and `bₙ=0` elsewhere. Source faithfulness contradicts
`μ(n)²=1` at any squarefree active index. Conversely this coefficientwise counterterm vanishes.
Nonvanishing on every interval plus continuity and nonnegativity gives strictly positive interval
energy. `[PROVED HERE]`

## Audit

- Corpus: prime-packet interval coefficient recovery exists, but no composite Ramaré packet or
  source-faithful finite-centering classification was found.
- Literature through 2026-08: Ramaré identity/short-interval work retains quantitative bilinear
  control; no finite disjoint-counterterm centering theorem or Route E application found.
  Relevant sources: arXiv:1911.09076, arXiv:2312.05138, arXiv:2603.25961.

## Log

- 2026-09-01 — classification, source-faithful no-go, and positive-energy survivor formalized in
  `RHTower/Sieve/RouteERamareSourceFaithfulFiniteCenteringNoGo.lean`; targeted build and standard-
  axiom audit pass. Finite source-faithful centering branch retired.
