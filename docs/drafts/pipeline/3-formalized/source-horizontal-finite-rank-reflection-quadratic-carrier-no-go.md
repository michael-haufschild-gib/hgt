# Source-horizontal finite-rank reflection quadratic-carrier no-go

- **ID:** SH-FRRP
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** shared HB/FZZ-P/PW-B/RBH source-horizontal producer
- **Statement:** An exact all-packet linear quadratic reflection on any target, including infinite-index targets, cannot differ from any real scalar operator by finite rank.

## Goal

Kill scalar-essential finite-rank reflection dynamics before the common four-route Ward receiver. Chain: exact reflected landing makes `T - cI` injective on every strict-sign source subspace; source packets have arbitrarily large positive or negative index off wall; finite operational rank is impossible.

## Gates

- [x] 0 → 1  corpus-led conjecture and RH chain fixed
- [x] 1 → 2  dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3  Lean theorem, target build, axiom audit, umbrella wiring
- [ ] 3 → 4  publication-ready note

## Theorem

Let `T` act on an arbitrary-dimensional real quadratic carrier and suppose `T - cI` has operational rank at most `k`, for any real `c`. If a source packet and its line reflection land exactly through `f` and `T ∘ f`, then both source inertia indices are at most `k`. Thus an off-wall packet of size `k+2`, whose reflected pair has an index `k+1`, cannot land.

`[PROVED HERE]` If `(T-cI)(f x)=0`, then `T(f x)=c f(x)`. Quadratic homogeneity and exact anti-isometry give `(c²+1)Q(f x)=0`, impossible for a nonzero vector in a positive- or negative-definite source subspace. Therefore `(T-cI)∘f` is injective there, while its range dimension is at most `k`.

## Lean closure

- Killing capstone: `sourceHorizontalFiniteRankReflectionQuadraticCarrierRouteKilled`.
- Positive survivor: `sourceZeroHorizontalSharedReservoir_allReflectionLandings_forces_infiniteRankPerturbation`.
- Operational rank predicate: `LinearMapFiniteRankAtMost`.
- Module: `SourceHorizontalFiniteRankReflectionQuadraticCarrierNoGo.lean`.
- Direct Lean and target-only `lake build` pass. Axiom audit: `propext`, `Classical.choice`, `Quot.sound`. Umbrella wired.

## Novelty audit

Internal corpus contained finite-dimensional and finite-negative-capacity obstructions, but not this arbitrary-dimensional infinite-index finite-rank-near-scalar obstruction. Primary literature search through August 2026 found general Krein-space and finite-rank perturbation work, not this RH source-packet theorem. Novelty claim is the exact shared-source application and sharp survivor, not the elementary dimension lemma alone.

## No-go closure

- **Killed:** every exact linear quadratic shared-source reflection with `T-cI` finite rank for some real `c`.
- **Strongest positive survivor:** every all-packet exact linear reflection has `T-cI` of unbounded operational rank for every real `c`.
- **Remaining escape:** genuinely non-scalar essential/infinite-rank reflection, or nonlinear, singular, or domain-changing landing.
