# Enhanced exponential-epigraph convolution

- **ID:** `enhanced-exponential-epigraph-convolution`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** D'Agnolo--Kashiwara enhanced exponential objects; foundational bridge for
  `polarized-irregular-source-purity-law.md`
- **Statement:** `[LITERATURE] [BRIDGE]` Fiberwise additive convolution of domain-restricted closed
  exponential epigraph supports intersects the base domains and adds the phases exactly.

## Goal

Construct first non-combinatorial support law required by enhanced irregular Riemann--Hilbert
theory.  For a type `X`, domains `U,V⊆X`, and phases `φ ψ : X → ℝ`, set

\[
 E_{U,\phi}=\{(x,t):x\in U,\ 0\le t+\phi(x)\}
\]

and

\[
 A\star_X B=\{(x,t):\exists u,v,\ (x,u)\in A,\ (x,v)\in B,\ u+v=t\}.
\]

Exact claim:

\[
 E_{U,\phi}\star_X E_{V,\psi}=E_{U\cap V,\phi+\psi}. \tag{1}
\]

This is support-level infrastructure for the enhanced convolution tensor.  It is not yet a
sheaf, derived, ind-sheaf, bordered-space, constructibility, or holonomic `D`-module theorem.

## Internal frontier

- `[CORPUS]` `StokesCellularMicrolocalSheaf.lean` computes a finite rational cellular shadow of
  exponential epigraph microstalks.
- `[CORPUS]` `StokesCellularCategory.lean` packages those shadows as cospan/quiver functors.
- `[CORPUS]` `StokesAnalyticMicrolocalRealization.lean` transports finite labels to actual phase-zero
  directions.
- No corpus declaration found for exponential epigraph supports, their exact phase order, or
  fiberwise additive convolution.

## External frontier

- `[LITERATURE]` D'Agnolo--Kashiwara represent an exponential factor by an epigraph sheaf
  `C_{t+φ(x)≥0}` and build enhancement using convolution in the extra real variable:
  https://arxiv.org/abs/2408.04260, Sections 5--6.
- `[LITERATURE]` Their full irregular correspondence targets enhanced subanalytic/ind-sheaf
  categories and reconstructs holonomic `D`-modules from enhanced tempered solutions:
  https://arxiv.org/abs/1311.2374.

Equation `(1)` is elementary support calculus inside that parent theory.  No novelty is claimed.

## Complete paper proof

`[PAPER-PROVED]` Let `(x,t)` lie in the left side.  Choose `u,v` with `u+v=t`,
`x∈U`, `x∈V`, `0≤u+φ(x)`, and `0≤v+ψ(x)`.  Thus `x∈U∩V`; adding inequalities gives

\[
 0\le u+v+\phi(x)+\psi(x)=t+(\phi+\psi)(x),
\]

so `(x,t)∈E_{U∩V,φ+ψ}`.

Conversely, suppose `(x,t)∈E_{U∩V,φ+ψ}`.  Then `x∈U` and `x∈V`.  Choose

\[
 u=-\phi(x),\qquad v=t+\phi(x).
\]

Then `u+v=t`, `u+φ(x)=0`, and

\[
 v+\psi(x)=t+\phi(x)+\psi(x)\ge0.
\]

Thus `(x,u)∈E_{U,φ}`, `(x,v)∈E_{V,ψ}`, and `(x,t)` lies in the fiberwise convolution.  Both
inclusions hold, proving `(1)`.  Taking `U=V=X` gives the full-base specialization.

## Hostile audit

- No topology is needed for `(1)`; adding continuity or subanalyticity would be an artificial
  hypothesis.
- Equality is fiberwise.  Ordinary Minkowski addition allowing different base points would make
  the statement false.
- Support equality alone does not give an isomorphism of sheaf convolutions; proper direct image,
  derived tensor, coefficients, and enhancement quotient remain separate obligations.
- This theorem cannot imply RH or even the irregular Riemann--Hilbert correspondence.  Its value is
  exact reusable support algebra, replacing an implicit picture by a checked invariant.

Verdict: `BRIDGE`.

## Gates

- [x] 0 → 1 in-progress: exact well-typed claim, parent theory, collision boundary, proof, and
  falsifiers recorded
- [x] 1 → 2 fully-proven: complete dependency-closed paper proof above
- [ ] 2 → 3 formalized: exact Lean theorem, targeted `lake env lean`, module build, axiom audit,
  and umbrella wiring
- [ ] 3 → 4 publication-ready: not applicable as standalone novelty

## Log

- 2026-08-24 — Internal/external frontier audited; exact support theorem frozen and paper-proved.
- 2026-08-24 — Exact theorem formalized as
  `EnhancedEpigraph.fiberwiseAdditiveConvolution_exponentialEpigraphOn`, with the full-base
  specialization `fiberwiseAdditiveConvolution_exponentialEpigraph`, in
  `StokesEnhancedEpigraphConvolution.lean`; direct Lean check and targeted module build pass; all
  new theorem axioms are `[propext, Classical.choice, Quot.sound]`; module is wired into
  `HTGeometry.lean`.  Stage remains 2 because repository-wide lint currently fails on six unrelated
  pre-existing umbrella-reachability errors in dirty worktree.
- 2026-08-24 — Returned to Gate 4 after checking the primary statement: strengthened full-base
  formula to the exact domain-intersection law used by D'Agnolo--Kashiwara.  Paper proof, direct
  Lean check, targeted module build, and new-declaration axiom audit all pass.
