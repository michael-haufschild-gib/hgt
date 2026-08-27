# Continuous exponential epigraphs are locally closed

- **ID:** `continuous-exponential-epigraph-locally-closed`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean)
- **Source:** topological support prerequisite for D'Agnolo--Kashiwara exponential sheaves
- **Statement:** `[LITERATURE] [BRIDGE]` A continuous real phase has closed full exponential
  epigraph; restriction to an open base domain is locally closed in the product.

## Goal

Let `X` be topological, `φ : X → ℝ` continuous, and `U⊆X` open.  Prove

\[
 E_\phi=\{(x,t):0\le t+\phi(x)\}
\]

is closed in `X×ℝ`, and

\[
 E_{U,\phi}=\{(x,t):x\in U,\ 0\le t+\phi(x)\}
\]

is locally closed.

## Frontier

- `[LITERATURE]` Exponential sheaves use continuous subanalytic phases on open subanalytic domains;
  their supports are locally closed: https://arxiv.org/abs/2408.04260, Section 6.
- `[CORPUS]` Support definitions and exact convolution/order laws are formalized in
  `StokesEnhancedEpigraphConvolution.lean`; no prior corpus theorem connected them to product
  topology.

## Complete paper proof

`[PAPER-PROVED]` The map `F : X×ℝ → ℝ`, `F(x,t)=t+φ(x)`, is continuous as sum of second
projection and `φ` after first projection.  Since `[0,∞)` is closed,

\[
 E_\phi=F^{-1}([0,\infty))
\]

is closed.  The set `U×ℝ` is open as inverse image of `U` under first projection, and

\[
 E_{U,\phi}=(U\times\mathbb R)\cap E_\phi.
\]

Intersection of an open set and a closed set is locally closed.

## Hostile audit

- Continuity is load-bearing: arbitrary phase epigraph need not be closed.
- Local closedness is only topological.  Subanalyticity of graph/support remains a separate layer.
- This theorem supplies a valid support for extension-by-zero; it does not construct the sheaf.

Verdict: `BRIDGE`.

## Gates

- [x] 0 → 1 in-progress: exact hypotheses and failure boundary recorded
- [x] 1 → 2 fully-proven: dependency-closed proof above
- [x] 2 → 3 formalized: exact theorem, direct check, targeted build, umbrella wiring, and
  authoritative repository lint pass
- [ ] 3 → 4 publication-ready: not applicable as standalone novelty

## Log

- 2026-08-24 — Topological epigraph theorem isolated and paper-proved.
- 2026-08-24 — Formalized as `isClosed_exponentialEpigraph` and
  `isLocallyClosed_exponentialEpigraphOn` in
  `GaloisForLFunctions.HTGeometry.StokesEnhancedEpigraphConvolution`. Direct `lake env lean` and
  targeted `lake build GaloisForLFunctions.HTGeometry.StokesEnhancedEpigraphConvolution` passed.
  `#print axioms` for both new declarations reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
- 2026-08-27 — Re-audited exact statements; direct module check, targeted build, umbrella-wiring
  lint, and authoritative repository lint pass; promoted to Stage 3.
