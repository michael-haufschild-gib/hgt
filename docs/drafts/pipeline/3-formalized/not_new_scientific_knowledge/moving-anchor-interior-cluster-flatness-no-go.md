# Moving-anchor interior-cluster flatness no-go

- **ID:** moving-anchor-interior-cluster-flatness-no-go
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** squarefree-half counterterm normal-family frontier
- **Statement:** An Euler-faithful locally bounded holomorphic approximation cannot have zeros of increasing order at anchors converging inside `rightHalf`.

## Goal

Determine whether moving or distributed Hermite anchors evade the complete fixed-anchor no-go,
and isolate exact geometric escape condition required of any surviving anchor schedule.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, targeted build green, axiom audit passed
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Exact claim

[PROVED HERE] Let `F_N` be analytic on `rightHalf`, locally bounded there, and convergent
compact-open on `farHalf` to `poleClearedFirstTraceSourceLimit`. Let anchors `b_N` converge within
`rightHalf` to `b∈rightHalf`, and let `depth N→∞`. If

`F_N^(j)(b_N)=0` whenever `j≤depth N`,

then contradiction.

## Complete proof

Vitali gives a holomorphic function `G` on connected `rightHalf` with `F_N→G` locally uniformly.
Uniqueness on `farHalf` makes `G` agree there with `poleClearedFirstTraceSourceLimit`.

Fix `j`. Cauchy's derivative theorem upgrades local uniform convergence to

`F_N^(j)→G^(j)` locally uniformly on `rightHalf`.

Because `b_N→b` within `rightHalf` and `G^(j)` is continuous there, local uniform convergence at
moving arguments gives

`F_N^(j)(b_N)→G^(j)(b)`.

Since `depth N→∞`, the left side is eventually exactly zero. Therefore `G^(j)(b)=0`. This holds for
every `j`, so analytic germ determinacy makes `G` zero near `b`; the identity theorem makes `G`
identically zero on `rightHalf`.

At `s=2`, Euler uniqueness instead gives

`G(2)=poleClearedFirstTraceSourceLimit(2)≠0`,

because its square is `(2-1) exp(coronaPrimeZeta(2))`. Contradiction.

## Hostile audit

- Anchor convergence is within `rightHalf`, ensuring every moving evaluation eventually lies in
  the local-uniform domain.
- Derivative order is fixed before `N→∞`; increasing depth supplies eventual zero for that order.
- Moving evaluation uses local-uniform derivative convergence plus continuity of the limit
  derivative, not pointwise convergence alone.
- Result does not assume a Hermite formula. It applies to any locally bounded Euler-faithful family
  with increasing vanishing order at clustered anchors.

## No-go closure

- **Exact killing theorem/mechanism:** Interior clustering plus increasing exact jet annihilation
  forces a flat nonzero Euler-faithful Vitali limit.
- **Strongest positive survivor:** Every viable high-depth anchor schedule must escape every compact
  subset of `rightHalf`; in particular it must approach the critical boundary, move vertically to
  infinity, or leave to the far right. Distributed schemes may survive only if no growing-depth
  mass accumulates at an interior point.
- **New insight:** Moving anchors change the fixed-anchor obstruction only through noncompactness,
  not through motion itself.
- **Status:** Complete dependency-closed paper proof and generic Lean theorem
  `not_eulerFaithful_locallyBounded_of_moving_flat_anchors`.

## Compact-escape corollary

[PAPER-PROVED] Under the same analyticity, Euler-fidelity, local-boundedness, increasing-depth, and
moving-zero-jet hypotheses, the anchors eventually avoid every compact `K⊂rightHalf`.

Otherwise they visit some such `K` frequently. Sequential compactness extracts a strictly
increasing index map `phi` for which `anchor(phi n)` converges to a point of `K`. Strict increase
gives `phi n→∞`; therefore analyticity, local bounds, Euler convergence, depth divergence, and the
zero-jet identities all pass to the restricted family. The moving-anchor theorem gives a
contradiction. This is the exact formal version of “anchors must escape every compact subset.”

[LEAN-PROVED] `moving_flat_anchors_eventually_avoid_compact` formalizes this corollary in the same
module.

## Lean verification

- Module:
  `formal/GaloisForLFunctions/RHTower/SquarefreeConvolutionHalfMovingAnchorFlatnessNoGo.lean`
- Direct check:
  `lake env lean GaloisForLFunctions/RHTower/SquarefreeConvolutionHalfMovingAnchorFlatnessNoGo.lean`
  — passed.
- Targeted build:
  `lake build GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfMovingAnchorFlatnessNoGo`
  — passed, `13067/13067` jobs.
- Axiom audit for both interior-cluster no-go and compact-escape classification:
  `[propext, Classical.choice, Quot.sound]` only.
- Umbrella:
  `formal/GaloisForLFunctions/RHTower.lean` imports module.

## Log

- 2026-09-04 — conjectured after complete fixed-anchor closure; moving-evaluation bridge found in Mathlib; promoted directly to Stage 2.
- 2026-09-04 — formalized generic moving-anchor normal-family obstruction; promoted to Stage 3.
