# Selected Proofs cross-corpus bridge audit

- **ID:** ten-proofs-cross-corpus-bridge-audit
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** OpenAI `ten-proofs`, commit `6fefffdbab0dfa726fcfde6cefae23aa7a1888f3`
- **Statement:** At least one theorem among the ten upstream Lean certificates either discharges an existing `HTGeometry`/`RHTower` hypothesis or `Prop` interface, or composes with an existing value/reflection interface to yield a non-trivial theorem absent from the local corpus.

## Goal

Determine the exact mathematical overlap between all ten imported proof surfaces and the complete
`HTGeometry`/`RHTower` theorem interfaces.  Accept only an explicit dependency-closed composition;
reject matches that are merely lexical, type-incompatible, tautological, or renamed existing facts.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `<name>`, `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Freeze upstream at the recorded commit; integrate each certificate without proof weakening; extract
every public declaration and its exact hypotheses/conclusion; enumerate every local explicit
hypothesis, `Prop` interface, equality, reflection, transport, and value-relation declaration; then
test all type-correct compositions in Lean.  For each candidate, distinguish hypothesis discharge,
new theorem, reusable bridge, rediscovery, and trivial specialization.

## Hostile audit

- A shared word such as compactness, rigidity, metric, positivity, spectrum, reflection, or volume
  is not evidence of a bridge.
- A theorem obtained by supplying an arbitrary existing local hypothesis is not a discharge.
- An equality transport is non-trivial only when it removes a genuine interface boundary or yields
  a conclusion not already available under equivalent or weaker assumptions.
- Repository absence alone does not establish scientific novelty.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** pending exhaustive declaration-level audit
- **Strongest positive survivor:** pending
- **New insight:** pending
- **Status:** upstream integration and internal audit in progress

## Log

- 2026-08-01 — created in `1-in-progress`; upstream commit and three acceptance modes frozen.
