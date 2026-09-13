# Hostile editorial audit: augmented-period-rank classification

## Standard of review

Review assumes a skeptical specialist editor who gives no credit for novelty,
correctness, or exposition unless manuscript itself supplies checkable evidence.
Three questions govern every pass:

1. Are references bibliographically correct and used for claims they support?
2. Does any case, implication, coefficient-field change, or analytic step remain
   open or implicit?
3. Does paper explain motivation, interpretation, and consequences while deriving
   its new results from explicit arguments?

## Literature audit

Primary publisher or author records were checked for all research-paper entries.

| Reference | Metadata and manuscript use | Result |
|---|---|---|
| Kato (2021) | *Funkcialaj Ekvacioj* 64, 225–235, DOI 10.1619/fesi.64.225. Theorem 1.1 proves rational-period differential algebraicity; Remark 1.2 identifies non-rational periods as unknown and anticipates generic failure with possible exceptions. | Correct |
| Nishizawa (2001) | *J. Phys. A* 34, 7411–7421, DOI 10.1088/0305-4470/34/36/320. Introduces the hierarchy used in the manuscript. | Correct; missing DOI added |
| Felder–Varchenko (2000) | *Advances in Mathematics* 156, 44–76, DOI 10.1006/aima.2000.1951. Supports the automorphic interpretation of the two-period elliptic gamma function. | Correct |
| Narukawa (2004) | *Advances in Mathematics* 189, 247–267, DOI 10.1016/j.aim.2003.11.009. Supports modular and integral representations of the multiple hierarchy. | Correct |
| Hardouin–Singer (2008) | *Mathematische Annalen* 342, 333–377, DOI 10.1007/s00208-008-0238-z. Proposition 3.1 is the one-automorphism antecedent of the descent mechanism. | Correct |
| Dreyfus–Hardouin–Roques–Singer (2018) | *Inventiones mathematicae* 213, 139–203, DOI 10.1007/s00222-018-0787-z. Appendix B develops the elliptic orbit-residue framework. | Correct |
| Arreche–Babbitt (2025) | arXiv:2508.18247, DOI 10.48550/arXiv.2508.18247. Gives complete elliptic summability obstructions. | Correct |
| Kolchin (1973) | *Differential Algebra and Algebraic Groups*, Pure and Applied Mathematics 54, Academic Press. | Correct |
| Lang (1987) | *Elliptic Functions*, second edition, Graduate Texts in Mathematics 112, Springer. | Correct |

Focused searches for “multiple elliptic gamma” with “differential
algebraicity,” “differential algebraic,” and “hypertranscendence” found Kato's
paper and no later competing classification of the non-rational-period problem.
This is evidence from the current search, not a claim that bibliographic absence
can be proved.

## Round 1

### Findings

- Product definition omitted the compact-dependent bounds needed for both
  forward and backward factors and did not justify meromorphic reciprocals.
- Differential-algebraic closure lemma invoked finite-jet and tower facts too
  tersely for a paper whose coefficient-field transfers are central.
- Elliptic differential algebraicity relied on a field-description slogan
  without deriving how an arbitrary elliptic function enters that field.
- Product specialization did not identify the finite bad set of fibers.
- Boundary-pole argument did not index the two uncancellable endpoint poles.
- Translation-coset upper bound suppressed induction through positive and
  negative period combinations.
- Introduction stated results but did not isolate what classification enables.
- Nishizawa entry lacked DOI.

### Repairs

- Added uniform compact bounds, Weierstrass-product conclusion, zero-set
  locality, and reciprocal meromorphy.
- Expanded finite-jet separant argument, transitivity, closure, and both uses of
  differential transcendence-degree tower law.
- Derived elliptic-function representation from degree-two Weierstrass
  uniformization, even/odd splitting, and the Weierstrass differential equation.
- Rewrote specialization using finite tensor presentations and explicit proper
  closed exceptional sets.
- Indexed boundary poles by minimum and maximum orbit support.
- Added explicit cocycle induction and same-coset formula.
- Added four precise consequences in introduction and additive/nome
  interpretation after nome-rank corollary.
- Added Nishizawa DOI.

## Round 2

### Findings

- Algebraic-disjointness proof invoked the nondiscreteness lemma for
  `P = Z + Z sigma + Z tau`, although repeated translates produce only the
  subgroup `P_N = Z + Z sigma + Z N tau`.
- Genericity proposition used `G` without identifying the full n-period face.
- Seed notation used parameter values as if they were index labels and reused
  `q` without a local definition.
- Product-curve field was written in a nonstandard function-field notation.
- Pole isolation omitted the short argument that `-h_i` and `0` are distinct.

### Repairs

- Applied the nondiscreteness proof directly to `P_N`; rational independence is
  preserved by the nonzero integer multiplier `N`.
- Defined the n-period `G` in the genericity proposition.
- Separated finite labels from period values and defined the local nome.
- Introduced `X_omega` and used `C(X_tau × X_sigma)`.
- Added `h_i notin P` and `Lambda_tau subset P` at the pole-isolation step.

## Round 3

### Adversarial proof-chain check

- Rank two: rational-affine normal form, positive common-step construction,
  facewise nilpotence, finite-dimensional two-translation theorem, logarithmic
  derivative transfer. No appeal to Kato's theorem and no omitted face.
- Rank at least three: rank-three minor extraction, two-period seed,
  simultaneous Ostrowski descent, product specialization, one-orbit pole
  contradiction, coface propagation. No residual parameter case.
- Exact seed matroid: zero period class, parallel nonzero classes, independence
  of distinct nonzero classes, equality for defects and quotients, and base
  change from elliptic compositum to rational functions are all proved.
- Infinite ambient set: only finite sections are asserted; no infinite product is
  smuggled into theorem.
- Genericity: exceptional set is covered by countably many explicit proper real
  hyperplanes; null, meagre, conull, and comeagre conclusions follow in the
  stated relative parameter space.
- Scope: paper classifies every finite upper-half-plane period tuple for the
  Nishizawa product. No case of Kato's stated problem remains open.

### Formal and artifact gate

- Main dichotomy, rational-affine exception, explicit non-rational example,
  nome quotient rank, translation-coset rank, arbitrary-family graph law, and
  measure/category genericity have unconditional theorem declarations in the
  formal corpus.
- Axiom audits for capstone declarations report only foundational quotient and
  classical-logic principles; no custom axiom, `sorry`, `admit`, `opaque`, or
  `unsafe` declaration occurs in target modules.
- Target module build and direct module check passed before manuscript audit.
- PDF compiles without TeX warnings, unresolved references, or overflow.
- All rendered pages pass visual inspection.
- Manuscript contains no references to proof-assistant implementation or source
  code. A separately headed provenance declaration identifies every AI system
  used and limits the human contributor's role to project management.

## Editorial decision

No substantive mathematical, bibliographic, scope, motivation, interpretation,
or presentation defect remains after Round 3. Recommendation: accept subject to
ordinary independent priority and specialist referee review.
