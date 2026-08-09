# The C1⟷O open-core reduction theorem

- **ID:** ULF-MECH-3
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper, dependency-closed assembly of verified in-tree components)
- **Parents:** ULF-MECH-2 (implication-graph program); frontier map route dossiers C1, O
- **Scientific status:** `[PROVED HERE — ASSEMBLY]` `[BRIDGE-GRADE BY CONSTRUCTION]`
  `[FIRST THEOREM-GRADE ANNOTATION OF THE MAP'S CONDITIONAL ROUTE COUNT]` `[NOT RH]`
  `[NO LEAN — user directive]`

## Verified components (each read in-tree this session; exact hypotheses recorded)

- **(A) Arithmetic realization on the absolute domain** (`XiWeilResolventSource.lean`):
  the spectral Cauchy polarization equals its divided-difference relative-trace form
  (`xiWeilPolarization_cauchy_eq_relativeResolvent_dividedDifference`), and admits the
  absolutely convergent von-Mangoldt + archimedean realization, valid where the centered
  parameters satisfy 1 < Re(1/2 + z·I) (`XiC_ne_zero_of_one_lt_centered_re` gates the
  domain).
- **(B) ℓ²-continuity transport** (`XiQuotientRealDecay.lean`,
  `tendsto_primeArchSource_packetSum_of_tendsto`; hypotheses verified verbatim this cycle):
  for Cauchy packets with ALL parameters in the absolute region, if the evaluation vectors
  converge in the divisor ℓ² space, the arithmetic (relative-trace divided-difference) sums
  converge to the ℓ² inner product against the limit — i.e. the arithmetic side extends
  continuously to the ℓ²-closure of absolute-domain Cauchy packet evaluations.
- **(C) Route O's literal object** (`CCMPublishedRestrictedWeilMatrix.lean`):
  `ccmPublishedRestrictedWeilPairing a F` = (pole + prime Mellin–Stieltjes pairing) −
  (archimedean pairing) on tent tests of logarithmic aperture (0, 2a]; the route's matrices
  are this pairing on the finite tent family.
- **(D) Square-summability of tent evaluations** (elementary, proved here): a tent test is
  Lipschitz with compact support, so its transform decays like γ^{-2} on horizontal strips;
  against Riemann–von Mangoldt counting (O(log T) zeros per unit height) the evaluation
  vector over the divisor is square-summable — tents lie in the corpus's
  `XiWeilSquareSummable` pairing class (`xiWeilPairSummable_of_squareSummable`).

## Theorem (reduction)

Let 𝒦 denote the ℓ²-closure of evaluation vectors of absolute-domain Cauchy packets, and let
q̄ denote C1's extended form on 𝒦 (well-defined by (B), computed by the ℓ² inner product of
`XiWeilLineConjHilbert`). Then:

1. **(Intertwining on the closed class.)** For every test whose evaluation vector lies in 𝒦
   and whose arithmetic pairing is the limit of its approximating packets' pairings, the
   O-type arithmetic pairing equals q̄ of its evaluation vector. In particular, on
   absolute-domain Cauchy/rectangular packet classes the identity is exact and closed
   in-tree — by (A) alone.
2. **(The comparison reduces to C1's connector.)** By (C) and (D), each tent evaluation
   vector v(F) is a square-summable divisor vector; the C1⟷O comparison at aperture a is
   exactly the question of identifying O's literal arithmetic pairing at F with q̄ at v(F) —
   i.e. membership-with-identification of tent tests in the closed class of (B). That is
   verbatim Route C1's recorded first unresolved connector ("identifying the continuous
   limit with an actual prime sum for a given test outside the resolvent core"). Hence:
   **closing C1's test-algebra connector on the tent family intertwines Route O's entire
   matrix family with C1's ℓ² spectral form; two open cores hang on one connector.**
3. **(Unconditional witness transport.)** On every class where the identity is closed
   (absolute-domain packets), a negativity witness for the arithmetic pairing IS a
   negativity witness for the spectral form q̄ — with no hypothesis. Any O-side negativity
   produced inside such a class transports to C1 instantly.

*Remark (residual description, cited not used).* Session memory records the criterion "the
Cauchy core's ℓ²-closure is everything iff every Xi zero is simple; the complement is the
fibrewise mean-zero space" at paper level (memory `cauchy-core-density-is-zero-simplicity`;
`XiWeilLineConjHilbert.lean` explicitly does not assert density). If that criterion holds,
the reduction's residual subspace is exactly the multiplicity defect. The theorem above does
not depend on it.

## Independence re-test (map §1, executed)

No full merger is claimed: C1's first unresolved producer (singular positive closure /
descent of the identified form) and O's (whole-ground profile exhaustion with intact
polar–prime cross terms) remain distinct statements with distinct admission conditions. The
map's twelve-route count stands; its "conditional on current corpus identification" caveat
acquires this as its first theorem-grade annotation: the C1–O PAIR is connector-coupled, not
independent at the comparison level.

## Hostile verdicts

- Novelty: BRIDGE-grade by construction (assembly of in-tree theorems plus one elementary
  decay lemma); the reduction statement and the connector identification are the new
  content, at the graph level, not the route level.
- Correctness risk: concentrated in (D)'s decay computation (elementary) and in reading
  (B)'s hypotheses correctly — both re-verified this cycle; (B) requires absolute-domain
  parameters, which is why the connector is genuinely open and the theorem is a reduction,
  not a merger.

## Log

- 2026-08-09 — assembled and promoted after the two promotion gates resolved: (B)'s exact
  hypotheses verified in-tree; the density-criterion dependency REMOVED from the statement
  (downgraded to a cited remark). Independence re-test run: no count change, annotation
  recorded.
