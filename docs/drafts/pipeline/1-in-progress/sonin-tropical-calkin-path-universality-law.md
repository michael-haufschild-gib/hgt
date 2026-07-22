# Sonin tropical Calkin path universality law

- **ID:** sonin-tropical-calkin-path-universality-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper-proved and Lean-formalized)
- **Source:** Post-Law-32 theorem-first scan of all `CCMSonin*.lean` modules and consumers
- **Statement:** At every positive cutoff, the genuine Gram-word operators of two finite Sonin
  scale paths with common endpoints are equal modulo compact operators exactly when their minimum
  visited scales agree. This classifier sits in the faithful inverse semigroup of canonical Sonin
  states; every path word is noncompact, endpoint absorption is the endpoint-minimum case, and
  concatenation tropicalizes to `min`.

## Gates

- [x] 0 → 1 in-progress: exact Lean declarations and all direct consumers read
- [x] Complete paper proof with no open dependency
- [x] Lean direct check
- [x] Hostile literature noncollision audit
- [ ] Final module build, lint, and axiom audit

## Internal noncollision audit

Three `scripts/formal_tools.py research` searches found canonical-state Calkin faithfulness,
finite-word normal forms, path-to-window reduction, endpoint absorption, and one Xi--Hurwitz loop
consumer. No declaration classifies two arbitrary genuine paths with fixed endpoints by equality
of their minima. The Xi--Hurwitz consumer uses only one path versus its direct endpoint edge.

## Paper proof

For each path `P`, the finite-path normal form gives compact equality between its genuine Gram
word and the canonical live window determined by `(P.start, P.endpoint, P.minimum)`. If two path
operators with common endpoints are compactly equal, transitivity gives compact equality of their
windows. Faithfulness of live-window Calkin representation gives equality of windows, and the
fixed-endpoint window classifier gives equality of minima. Conversely, equal endpoints and equal
minima make the canonical windows identical, so the two path normal forms give compact equality.

The inverse-semigroup, noncompactness, endpoint-absorption, and tropical-concatenation fields are
the exact terminal laws already proved for the same carrier. Together they show the new classifier
is a faithful tropical path representation, not an isolated equivalence.

## Lean formalization

`RHTower/SoninTropicalCalkinPathUniversalityLaw.lean` proves the arbitrary two-path classifier and
packages it with six carrier laws. Exact direct check:

```text
lake env lean GaloisForLFunctions/RHTower/SoninTropicalCalkinPathUniversalityLaw.lean
```

passed after two dependent-coordinate proof fixes.

## Hostile literature noncollision audit

Searches covered Sonin/prolate spaces, Calkin algebras, partial-isometry inverse semigroups,
dilation-window semigroups, and tropical path minima. Connes--Moscovici study the prolate operator
and Sonin space ([arXiv:2112.05500](https://arxiv.org/abs/2112.05500));
Connes--Consani--Moscovici develop semilocal Sonin spaces and prolate wave operators
([arXiv:2310.18423](https://arxiv.org/abs/2310.18423)). Neither contains a finite Gram-path
Calkin classifier by minimum visited scale. Popov--Radjavi characterize abstract self-adjoint
partial-isometry semigroups as inverse-semigroup representations
([arXiv:1306.1973](https://arxiv.org/abs/1306.1973)), but do not construct this Sonin window
carrier or its tropical fixed-endpoint path law. No exact collision was found; this is not a
priority claim.

## Log

- 2026-07-21 — Found from terminal Sonin theorems after exact consumer/duplicate scan. Paper proof
  closed from path normal form, live-window faithfulness, and fixed-endpoint minimum recovery.
- 2026-07-21 — Arbitrary two-path classifier and seven-field carrier certificate passed exact
  direct Lean check. Hostile Sonin/prolate/inverse-semigroup search found no tropical-minimum
  Calkin path law. Exhaustion resumed from augmented corpus.
