# Enhanced exponential-epigraph phase order

- **ID:** `enhanced-exponential-epigraph-order`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** D'Agnolo--Kashiwara exponential objects; follows
  `enhanced-exponential-epigraph-convolution.md`
- **Statement:** `[LITERATURE] [BRIDGE]` Closed exponential epigraph inclusion is equivalent to
  pointwise phase order; hence phase-to-support is an order embedding.

## Goal

For arbitrary `X` and phases `φ ψ : X → ℝ`, prove

\[
 E_\phi\subseteq E_\psi
 \quad\Longleftrightarrow\quad
 \forall x,\ \phi(x)\le\psi(x). \tag{1}
\]

This is the support-level dominance law behind triangular morphisms between exponential objects on
Stokes sectors.  It proves that support calculus retains the complete phase, unlike the existing
finite wall-label shadow.

## Frontier

- `[LITERATURE]` For enhanced exponential objects, D'Agnolo--Kashiwara explain that a nonzero
  morphism between epigraph objects forces the corresponding phase inequality on the sector:
  https://arxiv.org/abs/2408.04260, Section 5.
- `[CORPUS]` Existing cellular modules retain only active/inactive adjacent arcs and finite wall
  labels.  Corpus search found no exact phase-to-support order embedding.
- `(1)` is parent-theory support algebra, not new scientific knowledge.

## Complete paper proof

`[PAPER-PROVED]` Suppose `E_φ⊆E_ψ`.  For fixed `x`, the boundary point `(x,-φ(x))` lies in
`E_φ`; inclusion gives

\[
 0\le -\phi(x)+\psi(x),
\]

so `φ(x)≤ψ(x)`.

Conversely, suppose `φ(x)≤ψ(x)` for every `x`.  If `(x,t)∈E_φ`, then

\[
 0\le t+\phi(x)\le t+\psi(x),
\]

so `(x,t)∈E_ψ`.  This proves `(1)`.  Mutual inclusion gives pointwise antisymmetry, so
`E_φ=E_ψ` implies `φ=ψ`; phase-to-support is therefore an order embedding.

## Hostile audit

- Direction depends on convention `E_φ={t+φ≥0}`; reversing epigraph convention reverses order.
- Support inclusion is necessary input for morphism triangularity, not a proof of a nonzero sheaf
  morphism or its one-dimensionality.
- No topology, continuity, subanalyticity, or RH data are used or smuggled in.

Verdict: `BRIDGE`.

## Gates

- [x] 0 → 1 in-progress: exact claim and parent collision recorded
- [x] 1 → 2 fully-proven: complete dependency-closed proof above
- [x] 2 → 3 formalized: exact Lean order embedding, direct check, targeted build, prior axiom audit, umbrella wiring, and authoritative repository lint pass
- [ ] 3 → 4 publication-ready: not applicable as standalone novelty

## Log

- 2026-08-24 — Exact phase-order theorem paper-proved after support-convolution frontier audit.
- 2026-08-24 — Formalized as `EnhancedEpigraph.exponentialEpigraph_subset_iff` and
  `EnhancedEpigraph.exponentialEpigraphOrderEmbedding` in
  `StokesEnhancedEpigraphConvolution.lean`.  Direct Lean check and targeted module build pass;
  theorem axioms are `[propext, Classical.choice, Quot.sound]`.
- 2026-08-27 — Exact statement re-audited; direct check, targeted build, umbrella-wiring lint, and authoritative repository lint pass; promoted to Stage 3.
