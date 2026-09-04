# Growing-multiplicity escaping-quartet sharpness

- **ID:** growing-multiplicity-escaping-quartet-sharpness
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean)
- **Source:** `multiplicity-parity-ladder-route.md`
- **Statement:** Xi-symmetric hypertranscendental carriers can have off-line zeros of order tending to infinity while converging compact-open to Xi, provided the zeros escape vertically fast enough.

## Goal

Test the report's claimed continuous-class obstruction at its exact boundary. Preserve the completed
functional equation, Schwarz symmetry, hypertranscendence, and increasing local multiplicity while
letting only noncompact divisor charge escape.

## Gates

- [x] 0 → 1 in-progress: explicit source family and falsifier identified
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem, targeted build green, axiom audit clean
- [ ] 3 → 4 publication-ready: standalone paper

## Statement and proof

Fix real horizontal displacement `a`. Let `Q_n(s)` be the normalized functional-equation quartet
gauge at height `n+1`, and put

\[
  G_n(s)=Q_n(s)^{n+1},\qquad X_n(s)=G_n(s)\xi(s).
\]

The gauge is a product of two factors `1+u_±(s)/(n+1)^2`, raised to power `n+1`, where
`u_±(s)=((s-1/2)±a)^2`. On every compact set, the variable-power estimate is controlled by
`(n+1)/(n+1)^2=1/(n+1)→0`. Hence both powered factors converge locally uniformly to one, so
`G_n→1` and `X_n→xi` locally uniformly.

Every `X_n` retains the completed functional equation, Schwarz symmetry, and hypertranscendence.
At the explicit upper-right quartet point `rho_n=1/2+a+i(n+1)`, the base gauge vanishes. Therefore
`Q_n^(n+1)` has zero jets through order `n`, and multiplication by Xi preserves those zero jets.
For `a>0`, every `rho_n` lies strictly right of the critical line while its imaginary part tends
to infinity. `[PROVED HERE]`

## Lean formalization

Module:
`formal/GaloisForLFunctions/RHTower/SquarefreeConvolutionHalfMovingAnchorQuartetEscapeSharpness.lean`

Formalized conclusions include:

- local-uniform convergence `G_n → 1` and `X_n → xi`;
- completed functional equation and Schwarz symmetry for every carrier;
- hypertranscendence for every carrier;
- vanishing of every jet through order `n` at `rho_n`;
- membership of `rho_n` in `rightHalf` for `a>0`;
- vertical escape and eventual avoidance of every compact set.

Verification on 2026-09-04:

- direct `lake env lean` check: pass;
- targeted build: `13174/13174`, pass;
- `#print axioms` for all principal theorems: only `propext`, `Classical.choice`, `Quot.sound`.

Umbrella import:
`formal/GaloisForLFunctions/RHTower.lean`.

## Interpretation

No topology-only continuity argument can bound off-line multiplicity below one. Even full Xi shape
passport and hypertranscendence tolerate unbounded local multiplicity hidden at noncompact boundary.
This does not refute source-specific analytic methods and does not construct requested arithmetic
half-divisor: quartet is inserted by hand and leaves ordinary Dirichlet/Euler source class.

## Log

- 2026-09-04 — paper proof and scratch Lean proof completed
- 2026-09-04 — production Lean module, targeted build, axiom audit, and umbrella wiring completed
