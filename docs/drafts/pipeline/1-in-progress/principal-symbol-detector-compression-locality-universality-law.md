# Principal-Symbol Detector Compression–Locality Universality Law

- **ID:** principal-symbol-detector-compression-locality-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** Lean-corpus closure of linear-width and quadratic-width principal-symbol completions with holographic locality
- **Statement:** In at least four law directions, the linear detector is strictly smaller than the quadratic detector while preserving the same exact scalar horizon and maximal exterior symbol; both realizations retain the identical pair-covering locality obstruction.

## Goal

Determine whether internal detector compression changes either observable dependence geometry or
bounded-valence membrane cost.  Shared scalar pencil, scalar law, and law-coordinate space provide
the connector; strict detector-cardinality comparison distinguishes the conclusion from existing
single-construction capstones.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, exact `lake env lean` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Construct exact finite equivalences for increasing law pairs and for the three-grade quadratic
detector.  This gives quadratic detector width `1+n+choose n 2`, versus linear width `2n+1`;
the inequality is strict for `n ≥ 4`.  Apply both completion horizon/maximal-symbol theorems to
the same scalar pencil, then derive pair completeness and the covering bound separately from each
realization's independent coordinate brackets.

## Proof

`[PROVED HERE]` Increasing law pairs are equivalent to increasing embeddings of `Fin 2`, hence
to two-element coordinate subsets.  The quadratic detector index is the disjoint union of one
vacuum state, `n` single states, and `choose n 2` pair states, so its clocked width is
`(1+n+choose n 2)d`; the linear detector's clocked width is `(2n+1)d`.  Induction using Pascal's
identity proves `n < choose n 2` for `n ≥ 4`, and `d>0` gives strict clocked-width compression.

Applying both completion theorems to the same `A₀,F,m` identifies both dependence horizons with
the same zero locus `{c | F c = 0}` and proves both exterior commutator maps injective.  Their
coordinate principal brackets are therefore independently linearly independent.  Any
membrane-local presentation of either symbol must contain every coordinate pair, and counting
pairs in bounded-valence supports gives the same `choose n 2` covering lower bound for both.

## Novelty audit

- **Status:** `[LEAN PROVED — LITERATURE AUDITED]`
- Covering-design literature studies exactly the pair-covering combinatorics underlying the
  membrane bound; see Gordon–Kuperberg–Patashnik,
  [*Asymptotically optimal covering designs*](https://arxiv.org/abs/math/9511224), and
  Horsley–Singh,
  [*New lower bounds for t-coverings*](https://arxiv.org/abs/1706.06825).
- Kato studies exact local compression preserving bipartite correlations
  ([arXiv:2309.07434](https://arxiv.org/abs/2309.07434);
  [DOI 10.1109/TIT.2025.3562884](https://doi.org/10.1109/TIT.2025.3562884)).
- Quantum-state and detector compression literature treats lossless correlation or state
  compression, not scalar-law-preserving nilpotent principal-symbol completions with independent
  exterior commutators.
- Targeted searches found no theorem proving strict `2n+1` versus
  `1+n+choose n 2` compression while simultaneously preserving an exact algebraic-dependence
  horizon, maximal exterior symbol, and an unchanged bounded-valence pair-covering obstruction.

## Lean certificate

- Module:
  `GaloisForLFunctions.HTGeometry.PrincipalSymbolDetectorCompressionLocalityUniversalityLaw`
- Main theorem:
  `GaloisForLFunctions.HTGeometry.principalSymbolDetectorCompression_localityUniversality`
- Exact source check:
  `lake env lean GaloisForLFunctions/HTGeometry/PrincipalSymbolDetectorCompressionLocalityUniversalityLaw.lean`
  (exit 0, no output)
- Imported by `GaloisForLFunctions/HTGeometry.lean`.
- Axiom audit and module build deferred to required final audit; no intermediate `lake build`.

## Log

- 2026-07-23 — created in 1-in-progress after whole-corpus locality cluster scan.
- 2026-07-23 — exact Lean proof completed and post-proof literature audit found no exact prior law.
