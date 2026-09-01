# Source-horizontal finite-negative-capacity carrier no-go

- **ID:** SH-FNC-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` shared HB/FZZ-P/PW-B/RBH producer
- **Statement:** Off the critical wall, no pair of arbitrary-dimensional real quadratic carriers with uniformly bounded finite negative capacity can receive every reflected source-horizontal packet by exact linear quadratic pullback.

## Goal

Kill the arbitrary-dimensional Hilbert/Pontryagin/finite-negative-index continuation of the shared linear-quadratic Ward route. Chain: source-horizontal packets have negative index `m-1` for all `m`; exact pullback embeds each negative subspace into the target; bounded target negative capacity is impossible; only infinite-negative-index, nonlinear, or singular/domain-changing producers survive.

## Gates

- [x] 0 → 1  in-progress: corpus source and exact attack fixed
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, target build, axiom audit
- [ ] 3 → 4  publication-ready: standalone proof and novelty audit

## Theorem

For any off-wall Xi copy `q`, target modules `M₁,M₂` of arbitrary dimension, quadratic forms `Q₁,Q₂`, and finite capacities `k₁,k₂` bounding dimensions of all finite-dimensional negative-definite subspaces of `Q₁,Q₂`, an injectively prime-labelled packet of size `max k₁ k₂ + 2` prevents simultaneous exact pullback of the `q` and line-reflected source forms through arbitrary linear maps into `M₁,M₂`.

`[PROVED HERE]` Exact pullback is injective on every negative source subspace: a kernel vector would have both zero target quadratic value and strictly negative source value. Its target image is therefore a negative-definite subspace of the same finite dimension. A right-half packet supplies dimension `m-1`; off wall one reflected orientation is right-half; `m=max k₁ k₂+2` contradicts both capacity bounds.

## Approach

On a right-half packet, choose its exact `(m-1)`-dimensional negative subspace. Exact quadratic pullback makes the restricted landing injective and its image negative definite, so target capacity is at least `m-1`. Off wall, one reflected orientation is right-half. Take `m=max k₁ k₂+2`.

## Novelty audit

Internal corpus has the finite-ambient-dimension theorem and an all-prime rigged carrier with unbounded negative index, but no arbitrary-dimensional bounded-negative-capacity obstruction. Primary black-hole/QNM literature through August 2026 treats nonlinear mode excitation, non-self-adjoint bilinear projections, continuous spectra, and higher-order response; no RH-linked reflected-source finite-index no-go was found.

## No-go closure

- **Exact killing theorem/mechanism:** `sourceHorizontalFiniteNegativeCapacityQuadraticCarrierRouteKilled`.
- **Strongest positive survivor:** a linear quadratic producer must carry finite negative subspaces of every dimension.
- **New insight:** infinite ambient dimension is insufficient; the survivor must have genuinely infinite negative index.
- **Status:** dependency-closed in `SourceHorizontalFiniteNegativeCapacityQuadraticCarrierNoGo.lean`; direct Lean and target build pass; axiom audit uses only `propext`, `Classical.choice`, `Quot.sound`; umbrella wired. Global lint reports unrelated pre-existing unwired modules.
