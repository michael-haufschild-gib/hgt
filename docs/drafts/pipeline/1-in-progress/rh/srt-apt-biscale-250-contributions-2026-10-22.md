# SRT, arithmetic positivity and bi-scale research programme

- **ID:** srt-apt-biscale-250-2026-10-22
- **Stage:** 1-in-progress
- **Type:** CANDIDATE programme
- **Source:** user attachment `cb4d9f9f-4e5e-4466-aa13-8cde32568dc8/pasted-text-1.txt`
- **Goal:** 250 distinct, significant mathematical contributions satisfying the attachment.
- **Accepted contributions in this programme:** **0 / 250**.

## Counting gate

A contribution must solve a previously unresolved mathematical question, supply a new
problem-solving tool, discharge a substantive corpus premise, or advance an RH route.
Do not count preliminary lemmas, changes of constants, repackaged equivalences, no-go
statements, duplicate results, or an unsupported novelty claim. One mathematical advance
counts once even when transported among the five names of the Weil form.

Each accepted item needs its exact statement, dependency-closed paper proof, corpus
novelty comparison, model/selectivity audit, Lean module and foreground leaf audit,
axiom audit, and umbrella wiring. An unfinished conjecture is not an accepted item.

## Constraints

- Do not use `hgtl7`.
- All three requested READMEs are read-only.
- No computations, added axioms, assumed analytic inputs, heartbeat increases, full builds,
  or umbrella builds. Final Lean command: `lake --old env lean <leaf>.lean` in `formal/`.
- Search the project corpus before mathlib or a new proof. Search metadata are source-only;
  semantic coverage is incomplete, so verify relevant source and proofs.
- Existing worktree has extensive unrelated edits. Preserve them.
- Continue conjecture → proof or failure analysis → next conjecture until all 250 qualify.

## Evidence read

The complete current files were read, including motivation, mechanisms, traps and frontier:

- `formal/GaloisForLFunctions/SquareRootThreshold/README.md` (1032 lines).
- `formal/GaloisForLFunctions/arithmetic-positivity-theory/README.md` (1523 lines).
- `formal/GaloisForLFunctions/BiScaleUncertainty/README.md` (1410 lines).
- Root/formal `AGENTS.md`, formal guide and overview, `docs/reports/STATUS.md`.
- Relevant RW and SRT entries in `docs/reports/rh-current-frontier-map.md`.

## Conjecture loop

### Q1: quantitative finite-scale tent detection

README frontier: positivity on one grid at scale n/radius R should give a quantitative
depth/height exclusion. Corpus already has qualitative eventual grids, quantitative
full-form stability, and near-top visibility with an explicit horizon. A mere extraction
of a convergence constant is not counted. Full target requires paying the negative
margin and the contribution of zeros beyond the horizon without smuggling in attainment
or a depth-gap premise. Retained as an open candidate, not a theorem or a no-go.

Corpus searches: `quantitative grid tent zero detection depth height` and
`uniform off line zero detection finite aperture grid interpolation error`.
Results: `FactorialTentActualZetaDetectionAndFullZeroFormBridge`,
`FactorialTentDepthGapClusterAndPolarGraphBridge`, `FactorialTentPatternWeilCompleteness`,
and the SRT near-top/horizon modules. Search complete; semantic index incomplete.

### Q2: global stability across sieve support changes

Not new: `SievePhysicalTranslationStability.exists_physical_translate_error` already gives
uniform sixth-root physical-translation recovery from fifth/sixth arrays, without an
anchor or fixed support. Do not reprove or count it. Search:
`global stability translated fifth sixth moments changing support`.

### Q3: growing-window negativity of the actual critical prime channel

Current attack candidate. APT proves the limiting critical prime form uniformly negative
for every finite pattern, but finite-scale negativity is stated with support fixed before
the scale tends to infinity. Seek an explicit growing-width regime in which the *actual*
prime channel is uniformly negative on every coefficient vector. This would retain the
favourable arithmetic sign independently of the archimedean log-scale gain.

First inspect the finite-scale matrix, quantitative correlation estimates, and affine
comparison. Do not count an unspecified slowly growing diagonal sequence: that follows
formally from fixed-support convergence. A qualifying result must prove a concrete
growth regime and its complete prime/harmonic tail bound.

Searches launched:

- `critical prime matrix uniform growing support negative finite scale`
- `critical correlation quantitative convergence rate translated pattern`
- `affine comparison prime channel window negativity`

## Continuation state

No accepted theorem yet. Q3 now has a concrete linear-width target and proof architecture
in `critical-prime-negativity-on-linear-windows.md`. Uniform harmonic/prime tails and
disjoint affine-error intervals are existing inputs; finite-head operator control is
the missing assembly. Search JSON snapshots are in `/tmp/hgt-250-*.json`.
Programme card is the durable ledger; tmp files are expendable. Next: formalize Q3's
full-weight bounds and affine head, then audit the complete growing-window theorem.

Q3's frequency geometry and support counting now pass the exact foreground leaf
audit in `RHTower/FactorialCriticalAffineFrequencies.lean`; umbrella import added.
The full analytic estimate remains a paper proof with unaudited Lean drafts.
Its imports encounter stale relocated `.olean` headers. The root instructions
reiterate plain named-leaf checks and prohibit output flags; the earlier request
for an output-flag exception is withdrawn. Continue within that restriction.
